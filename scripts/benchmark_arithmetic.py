#!/usr/bin/env python3
"""Bounded comparison of complete Lean checks; excludes queue time from speedups."""
from pathlib import Path
import argparse
import hashlib
import json
import os
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--tag', default='H1_0B001')
    parser.add_argument('--variant', action='append', default=[])
    parser.add_argument('--timeout', type=float, default=180)
    parser.add_argument('--memory-mb', type=int, default=4096)
    parser.add_argument('--priority', choices=['interactive', 'normal', 'bulk'], default='normal')
    args = parser.parse_args()
    manifest = json.loads((ROOT / 'logs' / f'benchmark_{args.tag}_manifest.json').read_text())
    out = ROOT / 'logs' / 'arithmetic_benchmarks'
    out.mkdir(exist_ok=True)
    results = []
    for job in manifest:
        if args.variant and job['variant'] not in args.variant:
            continue
        source = ROOT / job['source']
        timing_path = out / f'{source.stem}.timing.json'
        env = dict(os.environ, REINHARDT_LEAN_PRIORITY=args.priority,
                   REINHARDT_LEAN_TIMEOUT_SECONDS=str(args.timeout),
                   REINHARDT_LEAN_CACHE='0', REINHARDT_LEAN_TIMING_FILE=str(timing_path))
        run = subprocess.run([sys.executable, str(ROOT / 'scripts/lean_cached.py'),
                              '-M', str(args.memory_mb),
                              '-o', str(source.with_suffix('.olean')), str(source)],
                             cwd=ROOT, env=env, text=True, stdout=subprocess.PIPE,
                             stderr=subprocess.STDOUT)
        (out / f'{source.stem}.log').write_text(run.stdout)
        timing = json.loads(timing_path.read_text()) if timing_path.exists() else {}
        match = re.search(re.escape("'" + job['theorem'] + "'") +
                          r' depends on axioms: \[([^]]*)\]', run.stdout)
        axioms = sorted({a.strip() for a in match.group(1).split(',') if a.strip()}) if match else None
        verified = run.returncode == 0 and axioms is not None and set(axioms) <= {
            'propext', 'Classical.choice', 'Quot.sound'}
        result = dict(job, source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
                      verified=verified, axioms=axioms, exit_code=run.returncode, timing=timing)
        (out / f'{source.stem}.json').write_text(json.dumps(result, indent=2) + '\n')
        results.append(result)
        print(json.dumps(dict(variant=job['variant'], verified=verified,
                              compile_seconds=timing.get('compile_seconds'),
                              queue_seconds=timing.get('queue_seconds'),
                              timed_out=timing.get('timed_out'), exit_code=run.returncode)), flush=True)
    (out / f'{args.tag}_latest.json').write_text(json.dumps(results, indent=2) + '\n')


if __name__ == '__main__':
    main()
