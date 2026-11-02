"""Focused wrapper tests using a fake compiler; these do not invoke Lean."""
import contextlib
import fcntl
import io
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import time
import unittest

SCRIPTS = Path(__file__).resolve().parents[1] / 'scripts'
sys.path.insert(0, str(SCRIPTS))
from lean_build_cache import Config, dependency_order, load_record, reusable_argv, run

FAKE = r'''#!/usr/bin/env python3
import os, pathlib, sys, time
args=sys.argv[1:]
root=pathlib.Path(os.environ['FAKE_ROOT'])
source=pathlib.Path(next(a for a in args if a.endswith('.lean')))
imports=[root.joinpath(*line.split()[1].split('.')).with_suffix('.olean') for line in source.read_text().splitlines() if line.startswith('import ')]
if '--deps' in args:
    with (root/'header_calls').open('a') as f:
        f.write(source.name+'\n')
    print('\n'.join(str(p) for p in imports))
    raise SystemExit(0)
with (root/'compiles').open('a') as f:
    f.write(source.name+'\n')
delay=next((float(line.split(':')[1]) for line in source.read_text().splitlines() if line.startswith('-- delay:')),0)
time.sleep(delay)
if '-- fail' in source.read_text():
    print('intentional compiler failure')
    raise SystemExit(3)
output=pathlib.Path(args[args.index('-o')+1])
output.write_bytes(source.read_bytes()+b''.join(p.read_bytes() for p in imports))
print("'Example.result' depends on axioms: [propext]")
'''

HARNESS = '''import os, sys
from pathlib import Path
sys.path.insert(0, sys.argv[1])
from lean_build_cache import Config, run
root=Path(os.environ['FAKE_ROOT'])
config=Config(root,root/'fake_lean',[root],dict(os.environ))
raise SystemExit(run(config,sys.argv[2:]))
'''


class BuildCacheTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name).resolve()
        self.tool = self.root / 'fake_lean'
        self.tool.write_text(FAKE)
        self.tool.chmod(0o755)
        self.env = dict(os.environ, FAKE_ROOT=str(self.root), LEAN_PATH=str(self.root), REINHARDT_LEAN_JOBS='1')
        self.env.pop('REINHARDT_LEAN_PRIORITY', None)
        self.env.pop('REINHARDT_LEAN_TIMEOUT_SECONDS', None)
        self.config = Config(self.root, self.tool, [self.root], self.env)
        self.config.initialize()
        self.children = []

    def tearDown(self):
        for child in self.children:
            if child.poll() is None:
                child.terminate()
            child.communicate(timeout=5)
        self.tmp.cleanup()

    def source(self, name, text='def example := 1\n'):
        path = self.root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)
        return path

    def args(self, source):
        return ['-o', str(source.with_suffix('.olean')), str(source)]

    def invoke(self, source, env=None, flags=None):
        stdout, stderr = io.StringIO(), io.StringIO()
        config = Config(self.root, self.tool, [self.root], dict(env or self.env))
        with contextlib.redirect_stdout(stdout), contextlib.redirect_stderr(stderr):
            code = run(config, list(flags or []) + self.args(source))
        report = json.loads(next(line.removeprefix('LEAN_BUILD ') for line in stderr.getvalue().splitlines() if line.startswith('LEAN_BUILD ')))
        return code, stdout.getvalue(), report

    def spawn(self, source, **env):
        child = subprocess.Popen([sys.executable, '-c', HARNESS, str(SCRIPTS), *self.args(source)],
                                 env=dict(self.env, **env), stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
        self.children.append(child)
        return child

    def finish(self, child):
        stdout, stderr = child.communicate(timeout=10)
        report = json.loads(next(line.removeprefix('LEAN_BUILD ') for line in stderr.splitlines() if line.startswith('LEAN_BUILD ')))
        return child.returncode, stdout, report

    def count(self):
        path = self.root / 'compiles'
        return path.read_text().splitlines() if path.exists() else []

    def wait_queued(self, number):
        deadline = time.monotonic() + 4
        while time.monotonic() < deadline:
            if len(list((self.config.state / 'queue').glob('*.json'))) >= number:
                return
            time.sleep(.02)
        self.fail('workers did not enter queue')

    def test_replays_output_and_invalidates_source_even_with_same_timestamp(self):
        source = self.source('A.lean')
        code, output, first = self.invoke(source)
        self.assertEqual(code, 0)
        code, output2, second = self.invoke(source)
        self.assertEqual(output, output2)
        self.assertTrue(second['cache_hit'])
        self.assertEqual(second['compile_seconds'], 0)
        stamp = source.stat().st_mtime_ns
        source.write_text('def example := 2\n')
        os.utime(source, ns=(stamp, stamp))
        self.assertEqual(self.invoke(source)[0], 0)
        self.assertEqual(self.count(), ['A.lean', 'A.lean'])

    def test_local_dependency_requires_provenance_and_detects_stale_content(self):
        dep = self.source('A.lean')
        dep.with_suffix('.olean').write_text('legacy artifact')
        source = self.source('B.lean', 'import A\ndef example := 3\n')
        for _ in range(2):
            code, _, report = self.invoke(source)
            self.assertEqual(code, 0)
            self.assertFalse(report['cache_hit'])
            self.assertIn(str(dep), report['provenance_incomplete'])
        self.assertEqual(self.invoke(dep)[0], 0)
        self.assertEqual(self.invoke(source)[0], 0)
        self.assertTrue(self.invoke(source)[2]['cache_hit'])
        stamp = dep.stat().st_mtime_ns
        dep.write_text('def example := 7\n')
        os.utime(dep, ns=(stamp, stamp))
        code, _, report = self.invoke(source)
        self.assertEqual(code, 1)
        self.assertIn('Stale local dependencies', report['error'])
        self.assertEqual(dependency_order(self.config, source), [dep, source])

    def test_transitive_change_and_output_corruption_are_detected(self):
        a = self.source('A.lean')
        b = self.source('B.lean', 'import A\ndef b := 2\n')
        c = self.source('C.lean', 'import B\ndef c := 3\n')
        for source in (a, b, c):
            self.assertEqual(self.invoke(source)[0], 0)
        a.with_suffix('.olean').write_text('corrupted')
        self.assertEqual(self.invoke(c)[0], 1)
        # Rebuilding the damaged dependency repairs provenance.
        self.assertEqual(self.invoke(a)[0], 0)
        self.assertTrue(self.invoke(c)[2]['cache_hit'])
        c.with_suffix('.olean').write_text('corrupted')
        self.assertFalse(self.invoke(c)[2]['cache_hit'])

    def test_failure_is_not_cached(self):
        source = self.source('A.lean', '-- fail\n')
        self.assertEqual(self.invoke(source)[0], 3)
        self.assertFalse(self.config.record_path(source.with_suffix('.olean')).exists())
        self.assertEqual(self.invoke(source)[0], 3)
        self.assertEqual(len(self.count()), 2)

    def test_bootstrap_discovers_not_yet_built_local_dependencies(self):
        a = self.source('A.lean')
        b = self.source('B.lean', 'import A\ndef b := 2\n')
        c = self.source('C.lean', 'import B\ndef c := 3\n')
        self.assertEqual(dependency_order(self.config, c), [a, b, c])
        # Planning may tolerate missing local outputs; normal compilation must not.
        self.assertEqual(self.invoke(c)[0], 1)
        for source in dependency_order(self.config, c):
            self.assertEqual(self.invoke(source)[0], 0)
        self.assertTrue(self.invoke(c)[2]['cache_hit'])

    def test_concurrent_duplicate_compiles_once(self):
        source = self.source('A.lean', '-- delay:0.3\n')
        first, second = self.spawn(source), self.spawn(source)
        results = [self.finish(first), self.finish(second)]
        self.assertEqual([r[0] for r in results], [0, 0])
        self.assertEqual(self.count(), ['A.lean'])
        self.assertEqual(sum(r[2]['cache_hit'] for r in results), 1)
        self.assertGreater(max(r[2]['dedup_wait_seconds'] for r in results), .1)

    def test_priority_and_queue_time_are_separate(self):
        a = self.source('A.lean', '-- delay:0.02\n')
        b = self.source('B.lean', '-- delay:0.02\n')
        with (self.root / 'logs/lean-slot-0.lock').open('a+') as lock:
            fcntl.flock(lock, fcntl.LOCK_EX)
            bulk = self.spawn(a, REINHARDT_LEAN_PRIORITY='bulk')
            self.wait_queued(1)
            interactive = self.spawn(b, REINHARDT_LEAN_PRIORITY='interactive', REINHARDT_LEAN_TIMEOUT_SECONDS='.8')
            self.wait_queued(2)
            time.sleep(1.0)  # Longer than timeout, but compiler has not started.
            fcntl.flock(lock, fcntl.LOCK_UN)
        results = [self.finish(interactive), self.finish(bulk)]
        self.assertEqual([r[0] for r in results], [0, 0])
        self.assertEqual(self.count(), ['B.lean', 'A.lean'])
        self.assertGreater(results[0][2]['queue_seconds'], .8)
        self.assertLess(results[0][2]['compile_seconds'], .8)

    def test_pause_gate_rechecked_and_interactive_bypasses(self):
        a = self.source('Certificate/SOS/A.lean')
        b = self.source('Certificate/SOS/B.lean')
        gate = self.root / 'logs/pause_data_builds'
        with (self.root / 'logs/lean-slot-0.lock').open('a+') as lock:
            fcntl.flock(lock, fcntl.LOCK_EX)
            bulk = self.spawn(a)
            self.wait_queued(1)
            gate.touch()  # Created after worker starts waiting.
            interactive = self.spawn(b, REINHARDT_LEAN_PRIORITY='interactive')
            self.wait_queued(2)
            fcntl.flock(lock, fcntl.LOCK_UN)
        self.assertEqual(self.finish(interactive)[0], 0)
        self.assertIsNone(bulk.poll())
        gate.unlink()
        self.assertEqual(self.finish(bulk)[0], 0)
        self.assertEqual(self.count(), ['B.lean', 'A.lean'])

    def test_relative_arguments_share_cache_and_header_parser_is_reused(self):
        source = self.source('A.lean')
        self.assertEqual(self.invoke(source)[0], 0)
        header_calls = (self.root / 'header_calls').read_text()
        with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
            self.assertEqual(run(self.config, ['-o', 'A.olean', 'A.lean']), 0)
        self.assertEqual(self.count(), ['A.lean'])
        self.assertEqual((self.root / 'header_calls').read_text(), header_calls)

    def test_companion_changes_invalidate_output_and_dependencies(self):
        source = self.source('A.lean')
        companion = Path(str(source.with_suffix('.olean')) + '.private')
        companion.write_text('private proof data')
        self.assertEqual(self.invoke(source)[0], 0)
        self.assertTrue(self.invoke(source)[2]['cache_hit'])
        consumer = self.source('B.lean', 'import A\ndef b := 3\n')
        self.assertEqual(self.invoke(consumer)[0], 0)
        companion.write_text('changed private proof data')
        self.assertEqual(self.invoke(consumer)[0], 1)
        self.assertFalse(self.invoke(source)[2]['cache_hit'])
        self.assertEqual(self.invoke(consumer)[0], 0)

    def test_interactive_duplicate_promotes_paused_bulk_owner(self):
        source = self.source('Certificate/SOS/A.lean', '-- delay:0.02\n')
        (self.root / 'logs/pause_data_builds').touch()
        bulk = self.spawn(source)
        self.wait_queued(1)
        interactive = self.spawn(source, REINHARDT_LEAN_PRIORITY='interactive')
        results = [self.finish(bulk), self.finish(interactive)]
        self.assertEqual([r[0] for r in results], [0, 0])
        self.assertEqual(self.count(), ['A.lean'])
        self.assertTrue(results[1][2]['cache_hit'])

    def test_memory_cap_is_nonsemantic_but_other_flags_remain_significant(self):
        source = self.source('A.lean')
        self.assertEqual(self.invoke(source, flags=['-M', '8192'])[0], 0)
        self.assertTrue(self.invoke(source, flags=['-M', '2048'])[2]['cache_hit'])
        self.assertTrue(self.invoke(source)[2]['cache_hit'])
        self.assertTrue(self.invoke(source, flags=['--memory=4096'])[2]['cache_hit'])
        self.assertTrue(self.invoke(source, flags=['-M1024'])[2]['cache_hit'])
        self.assertFalse(self.invoke(source, flags=['-D', 'maxRecDepth=2048'])[2]['cache_hit'])
        self.assertEqual(len(self.count()), 2)
        for cap in ('invalid', '-1', '١٢٣', '999999999999999999999999'):
            self.assertNotEqual(reusable_argv(self.config, ['-M', cap]), [])

    def test_profile_always_fresh_but_profiled_artifact_reusable(self):
        source = self.source('A.lean')
        flags = ['-M', '8192', '--profile']
        for _ in range(2):
            code, _, report = self.invoke(source, flags=flags)
            self.assertEqual(code, 0)
            self.assertFalse(report['cache_hit'])
            self.assertEqual(report['cache_disabled_reason'], 'profiling_requires_fresh_compile')
        record_path = self.config.record_path(source.with_suffix('.olean'))
        record = load_record(self.config, source.with_suffix('.olean'))
        self.assertEqual(record['argv'], flags + self.args(source))
        # Older cache records have argv but no explicit reusable key.
        record.pop('cache_argv')
        record_path.write_text(json.dumps(record))
        code, output, report = self.invoke(source, flags=['-M', '2048'])
        self.assertEqual(code, 0)
        self.assertTrue(report['cache_hit'])
        self.assertTrue(report['replayed_profile_output'])
        self.assertEqual(report['compile_seconds'], 0)
        self.assertEqual(len(self.count()), 2)
        self.assertIn('depends on axioms', output)

    def test_timeout_only_stops_own_compiler_and_never_caches(self):
        source = self.source('A.lean', '-- delay:2\n')
        child = self.spawn(source, REINHARDT_LEAN_TIMEOUT_SECONDS='.08')
        code, _, report = self.finish(child)
        self.assertEqual(code, 124)
        self.assertTrue(report['timed_out'])
        self.assertLess(report['compile_seconds'], 1)
        self.assertFalse(self.config.record_path(source.with_suffix('.olean')).exists())


if __name__ == '__main__':
    unittest.main()
