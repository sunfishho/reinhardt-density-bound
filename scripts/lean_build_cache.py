"""Conservative cache and fair compiler admission for the local Lean wrapper.

The external mathlib/toolchain trees are pinned, read-only build inputs. Their
*directly imported* artifacts are hashed. All local source/import provenance is
checked recursively; legacy artifacts without provenance can still be imported,
but never permit a cache hit. No timestamps are used to authorize reuse.
"""
from __future__ import annotations

from contextlib import contextmanager
from dataclasses import dataclass
import fcntl
import hashlib
import gzip
import json
import os
from pathlib import Path
import subprocess
import sys
import time
import threading
import uuid

SCHEMA = 1
SUMMARY_PREFIX = 'LEAN_BUILD '
PRIORITIES = {'interactive': 0, 'normal': 10, 'bulk': 20}


def digest(path: Path) -> str:
    h = hashlib.sha256()
    with path.open('rb') as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b''):
            h.update(chunk)
    return h.hexdigest()


def companions(path: Path):
    return {suffix: digest(Path(str(path) + suffix))
            for suffix in ('.private', '.server') if Path(str(path) + suffix).exists()}


def normalize_argv(config, argv):
    normalized = []
    path_next = False
    for arg in argv:
        if path_next:
            normalized.append(str(config.path(arg)))
            path_next = False
        elif arg in ('-o', '-R'):
            normalized.append(arg)
            path_next = True
        elif arg.startswith('--o='):
            normalized.extend(['-o', str(config.path(arg[4:]))])
        elif arg.startswith('--root='):
            normalized.extend(['-R', str(config.path(arg[7:]))])
        elif arg.endswith('.lean'):
            normalized.append(str(config.path(arg)))
        else:
            normalized.append(arg)
    return normalized


def reusable_argv(config, argv):
    """Ignore only a valid memory cap and the nonsemantic profiling switch.

    Profiling *requests* still always run a fresh compiler. A successful artifact
    produced while profiling is reusable by a later ordinary request. All other
    arguments, especially -D, package configuration, and trust flags, stay exact.
    Malformed caps are retained so an invalid invocation cannot hit the cache.
    """
    def valid_memory_cap(value):
        # Deliberately narrow: only ordinary nonnegative ASCII caps in the
        # portable signed-32-bit range. Unusual/malformed options stay exact.
        return (len(value) <= 10 and value.isascii() and value.isdecimal()
                and int(value) <= 2147483647)
    args = normalize_argv(config, argv)
    result = []
    i = 0
    while i < len(args):
        arg = args[i]
        if arg == '--profile':
            i += 1
            continue
        if arg in ('-M', '--memory') and i + 1 < len(args) and valid_memory_cap(args[i + 1]):
            i += 2
            continue
        if ((arg.startswith('-M') and valid_memory_cap(arg[2:]))
                or (arg.startswith('--memory=') and valid_memory_cap(arg[len('--memory='):]))):
            i += 1
            continue
        result.append(arg)
        i += 1
    return result


def replay_compiler_output(record, report):
    """Preserve audit output and identify any replayed profiling measurements."""
    if '--profile' in record.get('argv', []):
        report['replayed_profile_output'] = True
        report['cached_build_compile_seconds'] = record.get('compile_seconds')
        print('lean_cached: replaying a cached successful build; profiling timings below '
              'describe that earlier build, not this invocation.', file=sys.stderr, flush=True)
    sys.stdout.write(record['compiler_output'])
    sys.stdout.flush()


def object_digest(value) -> str:
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def provenance_equal(left, right):
    """Exact JSON-value equality without unfolding shared dependency DAGs.

    Snapshots and decoded records are acyclic. Remember container pairs only
    for this comparison: all keys, ordered entries, and scalar values are still
    checked, and mutations between calls are never hidden by a persistent memo.
    """
    pending = [(left, right)]
    seen = set()
    while pending:
        a, b = pending.pop()
        if a is b:
            continue
        if isinstance(a, dict) and isinstance(b, dict):
            pair = (id(a), id(b))
            if pair in seen:
                continue
            if a.keys() != b.keys():
                return False
            seen.add(pair)
            pending.extend((a[key], b[key]) for key in a)
        elif isinstance(a, list) and isinstance(b, list):
            pair = (id(a), id(b))
            if pair in seen:
                continue
            if len(a) != len(b):
                return False
            seen.add(pair)
            pending.extend(zip(a, b))
        elif a != b:
            return False
    return True


def pack_record(value):
    """Losslessly encode shared dependency objects once, instead of unfolding a DAG."""
    nodes, memo = [], {}
    def encode(v):
        if not isinstance(v, (dict, list)):
            return v
        key = id(v)
        if key in memo:
            return {'ref': memo[key]}
        index = len(nodes)
        memo[key] = index
        nodes.append(None)
        nodes[index] = (['dict', [[k, encode(x)] for k, x in v.items()]]
                        if isinstance(v, dict) else ['list', [encode(x) for x in v]])
        return {'ref': index}
    root = encode(value)
    return {'record_encoding': 'shared-json-v1', 'root': root, 'nodes': nodes}


def unpack_record(value):
    if value.get('record_encoding') != 'shared-json-v1':
        return value
    nodes, memo, visiting = value['nodes'], {}, set()
    def decode(v):
        if not isinstance(v, dict):
            return v
        if set(v) != {'ref'} or type(v['ref']) is not int or not 0 <= v['ref'] < len(nodes):
            raise ValueError('Invalid shared JSON reference')
        index = v['ref']
        if index in visiting:
            raise ValueError('Cyclic shared JSON record')
        if index in memo:
            return memo[index]
        visiting.add(index)
        kind, items = nodes[index]
        if kind == 'dict':
            result = {k: decode(x) for k, x in items}
        elif kind == 'list':
            result = [decode(x) for x in items]
        else:
            raise ValueError('Invalid shared JSON node')
        visiting.remove(index)
        memo[index] = result
        return result
    return decode(value['root'])


def atomic_json(path: Path, value) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    if path.parent.name == 'records':
        value = pack_record(value)
    tmp = path.with_name(path.name + '.' + uuid.uuid4().hex + '.tmp')
    tmp.write_text(json.dumps(value, indent=2) + '\n')
    os.replace(tmp, path)


@dataclass
class Config:
    root: Path
    tool: Path
    libs: list[Path]
    env: dict[str, str]

    def __post_init__(self):
        self.root = self.root.resolve()
        self.tool = self.tool.resolve()

    @property
    def state(self):
        return self.root / 'logs' / 'lean_build_cache'

    def initialize(self):
        for name in ('records', 'locks', 'queue', 'invocations', 'headers', 'demands'):
            (self.state / name).mkdir(parents=True, exist_ok=True)

    def path(self, value: str) -> Path:
        p = Path(value)
        return (self.root / p if not p.is_absolute() else p).resolve()

    def record_path(self, output: Path) -> Path:
        return self.state / 'records' / (object_digest(str(output)) + '.json')

    def input_identity(self):
        # Hash content every time: mtimes are not evidence that binaries match.
        configs = {str(p.relative_to(self.root)): digest(p)
                   for p in (self.root / 'lean-toolchain', self.root / 'lakefile.toml')
                   if p.exists()}
        return {'tool': str(self.tool), 'tool_sha256': digest(self.tool),
                'lean_path': self.env.get('LEAN_PATH', ''), 'project_config': configs}


def parse_outputs(config: Config, argv: list[str]):
    """Only ordinary source-to-olean invocations are reusable.

    Additional output modes, setup JSON, plugins, snapshots, stdin, and executing
    main are deliberately not cached. The compiler itself remains available.
    """
    sources = [config.path(a) for a in argv if a.endswith('.lean')]
    output = None
    for i, a in enumerate(argv):
        if a == '-o' and i + 1 < len(argv):
            output = config.path(argv[i + 1])
        elif a.startswith('--o='):
            output = config.path(a[4:])
    banned = ('--run', '--server', '--worker', '--stdin', '--setup', '--plugin',
              '--load-dynlib', '--incr-', '--deps', '--src-deps', '--json')
    extra = any(a in ('-i', '-c', '-b') or a.startswith(('--i=', '--c=', '--bc=')) for a in argv)
    mode_ok = not extra and not any(a.startswith(banned) for a in argv)
    local = len(sources) == 1 and sources[0].is_relative_to(config.root)
    eligible = bool(output and local and mode_ok and output.is_relative_to(config.root))
    return sources[0] if len(sources) == 1 else None, output, eligible


def imported_paths(config: Config, source: Path, identity=None, *, allow_missing_local=False):
    # Header results are keyed by source/tool/path contents, not timestamps.
    # Artifact contents are still freshly hashed by DependencySnapshot.
    identity = identity or config.input_identity()
    key = object_digest({'source': str(source), 'sha256': digest(source), 'identity': identity})
    cached_path = config.state / 'headers' / (key + '.json')
    search = [p.resolve() for p in config.libs] + [config.tool.parent.parent / 'lib/lean']
    try:
        cached = json.loads(cached_path.read_text())
        paths = []
        for entry in cached:
            relative = Path(entry['module_path'])
            first = next((p / relative for p in search if (p / relative).exists()), None)
            if first is None or first.resolve() != Path(entry['path']):
                break
            paths.append(first.resolve())
        else:
            return paths
    except (FileNotFoundError, json.JSONDecodeError, KeyError):
        pass
    # Let Lean parse its own import syntax. --deps only reads the header.
    result = subprocess.run([str(config.tool), '--deps', str(source)], cwd=config.root,
                            env=config.env, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
    if result.returncode:
        raise RuntimeError('Unable to inspect Lean imports: ' + result.stderr.strip() + result.stdout.strip())
    paths = sorted(set(config.path(line.strip()) for line in result.stdout.splitlines() if line.strip()))
    missing = [p for p in paths if p.suffix != '.olean' or
               (not p.exists() and not (allow_missing_local and p.is_relative_to(config.root)
                                        and p.with_suffix('.lean').is_file()))]
    if missing:
        raise RuntimeError('Missing imported .olean; build dependencies first: ' + ', '.join(map(str, missing)))
    entries = []
    for path in paths:
        base = next((p for p in search if path.is_relative_to(p)), None)
        if base is None:
            break
        entries.append({'path': str(path), 'module_path': str(path.relative_to(base))})
    else:
        atomic_json(cached_path, entries)
    return paths


def load_record(config: Config, output: Path):
    path = config.record_path(output)
    try:
        if path.exists():
            value = json.loads(path.read_text())
        else:
            with gzip.open(str(path) + '.gz', 'rt') as f:
                value = json.load(f)
        value = unpack_record(value)
        return value if value.get('schema') == SCHEMA else None
    except (FileNotFoundError, ValueError, KeyError, TypeError, IndexError):
        return None


class DependencySnapshot:
    def __init__(self, config: Config, identity=None):
        self.config = config
        self.identity = identity or config.input_identity()
        self.memo = {}
        self.visiting = set()
        self.incomplete = set()
        self.stale = set()

    def local_source(self, artifact: Path):
        # Project modules live beside their artifacts. Overlay mathlib modules
        # belong to the pinned external build, not the project source graph.
        if artifact.is_relative_to(self.config.root) and not artifact.is_relative_to(self.config.root / '.lake'):
            source = artifact.with_suffix('.lean')
            if source.exists():
                return source
        return None

    def source_inputs(self, source: Path):
        return {'source': str(source), 'source_sha256': digest(source),
                'imports': [self.artifact(p) for p in imported_paths(self.config, source, self.identity)]}

    def artifact(self, artifact: Path):
        key = str(artifact)
        if key in self.memo:
            return self.memo[key]
        if key in self.visiting:
            raise RuntimeError('Cyclic local imports: ' + key)
        self.visiting.add(key)
        result = {'path': key, 'sha256': digest(artifact)}
        auxiliary = companions(artifact)
        if auxiliary:
            result['companions'] = auxiliary
        source = self.local_source(artifact)
        if source is not None:
            inputs = self.source_inputs(source)
            result['local_inputs'] = inputs
            record = load_record(self.config, artifact)
            if record is None:
                self.incomplete.add(str(source))
                # A timestamp can reject obviously stale legacy artifacts, but
                # can never authorize a cache hit.
                if source.stat().st_mtime_ns > artifact.stat().st_mtime_ns:
                    self.stale.add(str(source) + ' (legacy source is newer than artifact)')
            elif (record.get('identity') != self.identity or not provenance_equal(record.get('inputs'), inputs)
                  or record.get('output_sha256') != result['sha256']
                  or record.get('output_companions', {}) != auxiliary):
                self.stale.add(str(source) + ' (source, imports, toolchain, or artifact changed)')
        self.memo[key] = result
        self.visiting.remove(key)
        return result


@contextmanager
def output_lock(config: Config, output: Path | None, priority='normal'):
    if output is None:
        yield 0.0
        return
    key = object_digest(str(output))
    path = config.state / 'locks' / (key + '.lock')
    demand = config.state / 'demands' / (uuid.uuid4().hex + '.json')
    start = time.monotonic()
    try:
        with path.open('a+') as f:
            while True:
                try:
                    fcntl.flock(f, fcntl.LOCK_EX | fcntl.LOCK_NB)
                    break
                except BlockingIOError:
                    if not demand.exists():
                        # Avoid priority inversion: a paused bulk owner must be
                        # allowed to finish when an interactive request needs
                        # the same output. This cannot preempt an active Lean.
                        atomic_json(demand, {'pid': os.getpid(), 'output': key,
                                             'priority': PRIORITIES[priority]})
                    time.sleep(.1)
            demand.unlink(missing_ok=True)
            yield time.monotonic() - start
    finally:
        demand.unlink(missing_ok=True)


def is_bulk(source: Path | None):
    text = str(source)
    return any(part in text for part in ('/Generated/', '/SOS/', '/Potential/H1_', '/Potential/H2.'))


def requested_priority(config: Config, source: Path | None):
    value = config.env.get('REINHARDT_LEAN_PRIORITY', 'bulk' if is_bulk(source) else 'normal')
    if value not in PRIORITIES:
        raise RuntimeError('REINHARDT_LEAN_PRIORITY must be interactive, normal, or bulk')
    return value


def alive(pid):
    try:
        os.kill(pid, 0)
        return True
    except ProcessLookupError:
        return False
    except PermissionError:
        return True


@contextmanager
def compiler_slot(config: Config, source: Path | None, output: Path | None = None):
    """Priority then FIFO among new wrappers; never preempts running Lean."""
    priority = requested_priority(config, source)
    gate = config.root / 'logs' / 'pause_data_builds'
    request = {'pid': os.getpid(), 'priority': PRIORITIES[priority], 'created_ns': time.time_ns(),
               'bulk': is_bulk(source) or priority == 'bulk', 'interactive': priority == 'interactive',
               'output': object_digest(str(output)) if output else None}
    token = config.state / 'queue' / (uuid.uuid4().hex + '.json')
    atomic_json(token, request)
    slots = max(1, int(config.env.get('REINHARDT_LEAN_JOBS', '1')))
    handles = [(config.root / 'logs' / f'lean-slot-{i}.lock').open('a+') for i in range(slots)]
    chosen = None
    start = time.monotonic()
    try:
        with (config.state / 'queue.lock').open('a+') as queue_lock:
            while chosen is None:
                with_locked_queue = False
                try:
                    fcntl.flock(queue_lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
                    with_locked_queue = True
                    pending = []
                    demands = {}
                    for entry in (config.state / 'demands').glob('*.json'):
                        try:
                            item = json.loads(entry.read_text())
                        except (FileNotFoundError, json.JSONDecodeError):
                            continue
                        if not alive(item['pid']):
                            entry.unlink(missing_ok=True)
                            continue
                        demands[item['output']] = min(demands.get(item['output'], 100), item['priority'])
                    paused = gate.exists()
                    for entry in (config.state / 'queue').glob('*.json'):
                        try:
                            item = json.loads(entry.read_text())
                        except (FileNotFoundError, json.JSONDecodeError):
                            continue
                        if not alive(item['pid']):
                            entry.unlink(missing_ok=True)
                            continue
                        effective_priority = min(item['priority'], demands.get(item.get('output'), 100))
                        if paused and item['bulk'] and effective_priority != PRIORITIES['interactive']:
                            continue
                        pending.append((effective_priority, item['created_ns'], str(entry)))
                    pending.sort()
                    if pending and pending[0][2] == str(token):
                        for handle in handles:
                            try:
                                fcntl.flock(handle, fcntl.LOCK_EX | fcntl.LOCK_NB)
                                chosen = handle
                                token.unlink(missing_ok=True)
                                break
                            except BlockingIOError:
                                pass
                except BlockingIOError:
                    pass
                finally:
                    if with_locked_queue:
                        fcntl.flock(queue_lock, fcntl.LOCK_UN)
                if chosen is None:
                    time.sleep(0.1)
        yield time.monotonic() - start
    finally:
        token.unlink(missing_ok=True)
        for handle in handles:
            handle.close()


def cache_matches(config, source, output, argv, identity):
    snap = DependencySnapshot(config, identity)
    inputs = snap.source_inputs(source)
    record = load_record(config, output)
    match = bool(record and not snap.incomplete and not snap.stale and output.exists()
                 and record.get('identity') == identity and provenance_equal(record.get('inputs'), inputs)
                 and reusable_argv(config, record.get('argv', [])) == reusable_argv(config, argv)
                 and record.get('output_sha256') == digest(output)
                 and record.get('output_companions', {}) == companions(output))
    return match, snap, inputs, record


def run(config: Config, argv: list[str]) -> int:
    config.initialize()
    start = time.monotonic()
    source, output, eligible = parse_outputs(config, argv)
    profile_requested = '--profile' in argv
    reuse_allowed = config.env.get('REINHARDT_LEAN_CACHE', '1') != '0' and not profile_requested
    report = {'schema': SCHEMA, 'pid': os.getpid(), 'source': str(source) if source else None,
              'output': str(output) if output else None, 'cache_hit': False,
              'priority': requested_priority(config, source), 'dedup_wait_seconds': 0.0,
              'queue_seconds': 0.0, 'compile_seconds': 0.0, 'cache_validation_seconds': 0.0,
              'exit_code': 1, 'timed_out': False, 'argv': list(argv),
              'cache_argv': reusable_argv(config, argv), 'profile_requested': profile_requested}
    if profile_requested:
        report['cache_disabled_reason'] = 'profiling_requires_fresh_compile'
    try:
        with output_lock(config, output, report['priority']) as duplicate_wait:
            report['dedup_wait_seconds'] = duplicate_wait
            identity = config.input_identity() if eligible else None
            validation_start = time.monotonic()
            hit, snap, inputs, record = cache_matches(config, source, output, argv, identity) if eligible else (False, None, None, None)
            report['cache_validation_seconds'] += time.monotonic() - validation_start
            if eligible and reuse_allowed and hit:
                replay_compiler_output(record, report)
                report.update(cache_hit=True, exit_code=0)
                return 0
            with compiler_slot(config, source, output) as queue_seconds:
                report['queue_seconds'] = queue_seconds
                # The queue may be long. Recheck all dependencies after admission.
                if eligible:
                    validation_start = time.monotonic()
                    identity = config.input_identity()
                    hit, snap, inputs, record = cache_matches(config, source, output, argv, identity)
                    report['cache_validation_seconds'] += time.monotonic() - validation_start
                    if snap.stale:
                        raise RuntimeError('Stale local dependencies; rebuild with lean_cached.py first:\n  ' + '\n  '.join(sorted(snap.stale)))
                    if snap.incomplete:
                        report['provenance_incomplete'] = sorted(snap.incomplete)
                    if hit and reuse_allowed:
                        replay_compiler_output(record, report)
                        report.update(cache_hit=True, exit_code=0)
                        return 0
                timeout = float(config.env.get('REINHARDT_LEAN_TIMEOUT_SECONDS', '0'))
                if timeout < 0:
                    raise RuntimeError('REINHARDT_LEAN_TIMEOUT_SECONDS must be nonnegative')
                compiler_start = time.monotonic()
                proc = subprocess.Popen([str(config.tool), *argv], cwd=config.root, env=config.env,
                                        stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
                chunks = []
                timed_out = threading.Event()
                def stop_own_child():
                    if proc.poll() is None:
                        timed_out.set()
                        proc.terminate()
                        try:
                            proc.wait(timeout=5)
                        except subprocess.TimeoutExpired:
                            proc.kill()
                            proc.wait()
                timer = threading.Timer(timeout, stop_own_child) if timeout else None
                if timer:
                    timer.daemon = True
                    timer.start()
                try:
                    for line in proc.stdout:
                        chunks.append(line)
                        sys.stdout.write(line)
                        sys.stdout.flush()
                    result = proc.wait()
                    if timed_out.is_set():
                        result = 124
                finally:
                    if timer:
                        timer.cancel()
                    if proc.poll() is None:
                        proc.terminate()
                        proc.wait()
                    report['compile_seconds'] = time.monotonic() - compiler_start
                report['exit_code'] = result
                report['timed_out'] = timed_out.is_set()
                if result == 0 and eligible and output.exists():
                    validation_start = time.monotonic()
                    after_identity = config.input_identity()
                    after = DependencySnapshot(config, after_identity)
                    after_inputs = after.source_inputs(source)
                    report['cache_validation_seconds'] += time.monotonic() - validation_start
                    if after_identity != identity or not provenance_equal(after_inputs, inputs):
                        raise RuntimeError('Build inputs changed during compilation; rebuild before using the output.')
                    atomic_json(config.record_path(output), {
                        'schema': SCHEMA, 'identity': identity, 'inputs': inputs, 'argv': list(argv),
                        'cache_argv': reusable_argv(config, argv),
                        'output_sha256': digest(output), 'output_companions': companions(output), 'compiler_output': ''.join(chunks),
                        'provenance_incomplete_at_build': sorted(after.incomplete),
                        'compile_seconds': report['compile_seconds'], 'built_at_ns': time.time_ns(),
                    })
                return result
    except (OSError, RuntimeError, ValueError) as exc:
        report.update(exit_code=1, error=str(exc))
        print('lean_cached: ' + str(exc), file=sys.stderr)
        return 1
    finally:
        report['wall_seconds'] = time.monotonic() - start
        report['overhead_seconds'] = max(0.0, report['wall_seconds'] - report['queue_seconds']
                                        - report['dedup_wait_seconds'] - report['compile_seconds'])
        atomic_json(config.state / 'invocations' / (str(time.time_ns()) + '-' + str(os.getpid()) + '.json'), report)
        if config.env.get('REINHARDT_LEAN_TIMING_FILE'):
            atomic_json(config.path(config.env['REINHARDT_LEAN_TIMING_FILE']), report)
        print(SUMMARY_PREFIX + json.dumps(report, sort_keys=True), file=sys.stderr, flush=True)


def dependency_order(config: Config, source: Path):
    """List local dependencies before dependents, without compiling anything."""
    order, seen = [], set()
    snap = DependencySnapshot(config)
    def visit(path):
        if path in seen:
            return
        seen.add(path)
        for artifact in imported_paths(config, path, allow_missing_local=True):
            child = snap.local_source(artifact)
            if child is not None:
                visit(child)
        order.append(path)
    visit(source)
    return order
