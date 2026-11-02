"""Freshly compile a checker entry, without rebuilding existing dependencies."""
from pathlib import Path
import json
import os
import subprocess
import sys

BASE = Path(__file__).resolve().parent
settings = json.loads((BASE / 'paths.json').read_text())
name = sys.argv[1]
if name not in {'Challenge', 'Solution', 'ControlChallenge', 'ControlGood',
                'ControlBadStatement', 'ControlBadAxiom'}:
    raise SystemExit('Unknown entry module')
# The reference cannot search the proof project or its Mathlib overlay.
paths = settings['solution_paths'] if name == 'Solution' else settings['challenge_paths']
env = dict(os.environ, LEAN_PATH=os.pathsep.join(paths), LEAN_NUM_THREADS='1')
out = BASE / '.lake/build/lib/lean' / (name + '.olean')
out.parent.mkdir(parents=True, exist_ok=True)
command = [settings['lean'], '-j1', '-M8192', '-DElab.async=false',
           '-o', str(out), str(BASE / (name + '.lean'))]
print('Fresh entry compilation:', name, flush=True)
raise SystemExit(subprocess.run(command, cwd=BASE, env=env).returncode)
