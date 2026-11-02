"""Verify the Reinhardt bound with upstream Comparator and Nanoda on macOS.

Uses the upstream fake-landrun launcher: this is not Linux sandbox isolation.
Existing compiled dependencies are exported and replayed, not trusted as axioms.
"""
from pathlib import Path
import argparse
import datetime
import hashlib
import json
import os
import re
import resource
import shutil
import signal
import subprocess
import time

BASE = Path(__file__).resolve().parent
ROOT = BASE.parent.parent


def sha(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as f:
        while chunk := f.read(1024 * 1024):
            h.update(chunk)
    return h.hexdigest()


def save(path, value):
    temp = path.with_suffix(path.suffix + '.tmp')
    temp.write_text(json.dumps(value, indent=2) + '\n')
    temp.replace(path)


def validate_artifacts():
    previous = json.loads((ROOT / 'logs/final/verification.json').read_text())
    files = {}
    for item in previous['source_and_artifact_manifest']:
        for field in ('source', 'artifact'):
            p = ROOT / item[field]
            actual = sha(p)
            if actual != item[field + '_sha256']:
                raise RuntimeError('Source/artifact differs from final audit: ' + str(p))
            files[str(p)] = actual
        for suffix, expected in item['artifact_companions'].items():
            p = Path(str(ROOT / item['artifact']) + suffix)
            if sha(p) != expected:
                raise RuntimeError('Companion differs from final audit: ' + str(p))
            files[str(p)] = expected
    for directory in (ROOT / 'vendor_mathlib', ROOT / '.lake/build/lib/lean'):
        for p in directory.rglob('*'):
            if p.is_file() and (p.suffix == '.lean' or '.olean' in p.name):
                files[str(p)] = sha(p)
    return dict(local_modules=len(previous['source_and_artifact_manifest']), files=files)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--controls-only', action='store_true')
    parser.add_argument('--full-only', action='store_true')
    args = parser.parse_args()
    settings = json.loads((BASE / 'paths.json').read_text())
    stamp = datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ')
    output = BASE / 'recorded' / stamp
    output.mkdir(parents=True)
    print('Verification receipts:', output, flush=True)
    (BASE / 'latest-run.txt').write_text(str(output) + '\n')
    pin = Path(settings['lean']).parent
    env = dict(os.environ, PATH=str(pin) + os.pathsep + os.environ['PATH'],
               LEAN_NUM_THREADS='1', COMPARATOR_LANDRUN=settings['landrun'],
               COMPARATOR_LEAN4EXPORT=str(BASE / 'capture_export.py'),
               COMPARATOR_NANODA=str(BASE / 'nanoda_launch.py'))
    soft, hard = resource.getrlimit(resource.RLIMIT_STACK)
    if hard != resource.RLIM_INFINITY and hard > soft:
        resource.setrlimit(resource.RLIMIT_STACK, (hard, hard))
    artifacts = validate_artifacts()
    print('Validated source/object hashes for', artifacts['local_modules'], 'local modules.', flush=True)
    components = {}
    for name, path in settings['components'].items():
        components[name] = {
            'path': path,
            'revision': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=path, text=True).strip(),
            'diff': subprocess.check_output(['git', 'diff', 'HEAD', '--'], cwd=path, text=True),
        }
    core_diff = subprocess.check_output(['git', 'diff', 'HEAD', '--', 'Main.lean', 'Comparator.lean', 'Comparator'],
                                       cwd=settings['components']['comparator'], text=True)
    if core_diff:
        raise RuntimeError('Upstream Comparator checking code has local changes')
    provenance = dict(
        started_at_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
        theorem='Certificate.Packing.reinhardt_density_lower_bound',
        statement='For every symmetric convex disc K in R^2, 8950112/10000000 < packingDensity K.',
        isolation='upstream fake-landrun; no Linux sandbox',
        comparator='standard upstream executable; unchanged Main.lean and Comparator modules',
        nanoda_adjustments='two workers; 512 MiB worker stacks; success logging; axiom pretty-printing disabled',
        proof_checking_rules_modified=False,
        definition_holes=[], permitted_axioms=['propext', 'Quot.sound', 'Classical.choice'],
        components=components,
        input_artifacts=artifacts,
        harness_sha256={str(p.relative_to(BASE)): sha(p) for p in BASE.iterdir()
                        if p.is_file() and p.name != 'latest-run.txt'},
        executable_sha256={key: sha(settings[key]) for key in ('lean', 'comparator', 'exporter', 'nanoda', 'landrun')},
        stack_limit_bytes=resource.getrlimit(resource.RLIMIT_STACK),
        lean_version=subprocess.check_output([settings['lean'], '--version'], text=True).strip(),
    )
    save(output / 'provenance.json', provenance)
    results = []

    def run(name, config, expected=0, markers=(), command=None):
        stage = output / name
        stage.mkdir()
        stage_env = dict(env, REINHARDT_COMPARATOR_RECEIPT=str(stage))
        command = command or [settings['comparator'], str(config)]
        logfile = stage / 'check.log'
        start = time.monotonic()
        last_report = start
        disk_floor = 8 * 1024 ** 3
        print('Running', name, 'log:', logfile, flush=True)
        save(output / 'status.json', dict(state='running', stage=name, pid=os.getpid()))
        stopped = None
        with logfile.open('w') as log:
            proc = subprocess.Popen(['/usr/bin/time', '-l', *command], cwd=BASE, env=stage_env,
                                    stdout=log, stderr=subprocess.STDOUT, start_new_session=True)
            try:
                while proc.poll() is None:
                    free = shutil.disk_usage(ROOT).free
                    if free < disk_floor:
                        stopped = 'Free disk space fell below 8 GiB; stopped to protect the workstation.'
                        os.killpg(proc.pid, signal.SIGTERM)
                        try:
                            proc.wait(timeout=10)
                        except subprocess.TimeoutExpired:
                            os.killpg(proc.pid, signal.SIGKILL)
                        break
                    if time.monotonic() - last_report > 60:
                        print(name, 'running for', round(time.monotonic() - start),
                              'seconds; free disk GiB', round(free / 1024 ** 3, 1), flush=True)
                        last_report = time.monotonic()
                    time.sleep(2)
                status = proc.wait()
            except BaseException:
                os.killpg(proc.pid, signal.SIGTERM)
                proc.wait()
                raise
        text = logfile.read_text(errors='replace')
        rss = re.search(r'(\d+)\s+maximum resident set size', text)
        record = dict(name=name, command=command, exit_code=status,
                      expected_exit_code=expected, seconds=time.monotonic() - start,
                      log_sha256=sha(logfile), stopped=stopped,
                      maximum_resident_bytes=int(rss[1]) if rss else None,
                      passed=status == expected and not stopped and all(m in text for m in markers))
        if name in ('ControlGood', 'reinhardt') and record['passed']:
            module = 'Solution' if name == 'reinhardt' else 'ControlGood'
            export = json.loads((stage / (module + '-export.json')).read_text())
            nanoda = json.loads((stage / 'nanoda-result.json').read_text())
            record['same_export_for_both_kernels'] = (
                export['complete'] and nanoda['exit_code'] == 0 and not nanoda['broken_pipe']
                and export['sha256'] == nanoda['input_sha256']
                and export['bytes'] == nanoda['input_bytes'])
            record['export_sha256'] = export['sha256']
            record['export_bytes'] = export['bytes']
            record['passed'] &= record['same_export_for_both_kernels']
        results.append(record)
        save(output / 'results.json', results)
        print(name, 'PASSED' if record['passed'] else 'DID NOT PASS',
              'elapsed seconds', round(record['seconds'], 1), flush=True)
        if not record['passed']:
            save(output / 'status.json', dict(state='incomplete', stage=name, result=record))
            print(text[-8000:], flush=True)
            raise SystemExit(1)
        return stage

    success = ['Nanoda kernel accepts the solution', 'Lean default kernel accepts the solution',
               'Your solution is okay!']
    if not args.full_only:
        run('ControlGood', BASE / 'ControlGood.json', markers=success)
        run('ControlBadStatement', BASE / 'ControlBadStatement.json', expected=1,
            markers=['Challenge and solution theorem statement do not match'])
        run('ControlBadAxiom', BASE / 'ControlBadAxiom.json', expected=1,
            markers=["Illegal axiom detected: 'forbiddenControl'"])
    if not args.controls_only:
        run('reinhardt', BASE / 'config.json', markers=success)
    changed = [path for path, expected in artifacts['files'].items() if sha(path) != expected]
    harness_changed = [name for name, expected in provenance['harness_sha256'].items()
                       if sha(BASE / name) != expected]
    executables_changed = [name for name, expected in provenance['executable_sha256'].items()
                           if sha(settings[name]) != expected]
    integrity = dict(artifacts_changed=changed, harness_changed=harness_changed,
                     executables_changed=executables_changed)
    save(output / 'postcheck-integrity.json', integrity)
    if changed or harness_changed or executables_changed:
        save(output / 'status.json', dict(state='integrity_mismatch', **integrity))
        raise SystemExit('Inputs changed during verification')
    save(output / 'status.json', dict(state='complete', full_proof_verified=not args.controls_only,
        standard_comparator_passed=not args.controls_only, nanoda_passed=not args.controls_only,
        isolation='none (upstream macOS development launcher)', results=results))
    print('Completed:', output, flush=True)


if __name__ == '__main__':
    main()
