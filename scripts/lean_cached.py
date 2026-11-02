#!/usr/bin/env python3
"""Use pinned mathlib; deduplicate and cache local Lean builds conservatively.

REINHARDT_LEAN_PRIORITY=interactive|normal|bulk controls admission (no preemption).
REINHARDT_LEAN_CACHE=0 forces compilation but retains dependency freshness checks.
--profile always compiles freshly; successful artifacts are reusable across
memory-cap differences (-M / --memory). Other compiler flags remain significant.
REINHARDT_LEAN_TIMING_FILE records queue, compiler, validation, and total times.
REINHARDT_LEAN_TIMEOUT_SECONDS bounds only compiler runtime, not queue time.
--bootstrap-list SOURCE lists local dependency builds; --bootstrap SOURCE builds
that list explicitly, in order. Existing uncertified imports never enable reuse.
"""
import os
from pathlib import Path
import shlex
import sys
from lean_build_cache import Config, dependency_order, run

ROOT = Path(__file__).resolve().parents[1]
CACHE = Path(os.environ.get('REINHARDT_CACHED_PROJECT', '/Users/matthewho/.codex/.chatgpt-projects/g-p-6a5ad858ad18819189c51db74c9c12e9/courtade-kumar-publish'))
TOOL = Path.home() / '.elan/toolchains/leanprover--lean4---v4.33.0/bin/lean'
libs = [ROOT, ROOT / '.lake/build/lib/lean'] + [p / '.lake/build/lib/lean' for p in (CACHE / '.lake/packages').iterdir()]
env = dict(os.environ, LEAN_PATH=':'.join(str(p) for p in libs if p.exists()))
config = Config(ROOT, TOOL, libs, env)
argv = sys.argv[1:]
if argv and argv[0] in ('--bootstrap-list', '--bootstrap'):
    if len(argv) != 2:
        raise SystemExit('usage: lean_cached.py --bootstrap[-list] SOURCE.lean')
    paths = dependency_order(config, config.path(argv[1]))
    for path in paths:
        args = ['-o', str(path.with_suffix('.olean')), str(path)]
        if argv[0] == '--bootstrap-list':
            print(shlex.join([sys.executable, str(ROOT / 'scripts/lean_cached.py'), *args]))
        else:
            status = run(config, args)
            if status:
                raise SystemExit(status)
    raise SystemExit(0)
raise SystemExit(run(config, argv))
