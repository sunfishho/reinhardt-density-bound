#!/usr/bin/env python3
"""Select two worker threads; preserve the upstream kernel and axiom policy."""
from pathlib import Path
import hashlib
import json
import os
import subprocess
import sys
import time

base = Path(__file__).resolve().parent
settings = json.loads((base / 'paths.json').read_text())
output = Path(os.environ['REINHARDT_COMPARATOR_RECEIPT'])
config = json.loads(Path(sys.argv[1]).read_text())
original = dict(config)
assert config['unpermitted_axiom_hard_error'] is True
assert set(config['permitted_axioms']) == {'propext', 'Quot.sound', 'Classical.choice'}
assert config['use_stdin'] is True
# The upstream default uses the main thread's small stack. Two threads activate
# the existing 512 MiB worker-stack allocation; neither change alters checking.
config.update(num_threads=2, print_success_message=True, print_axioms=False)
(output / 'nanoda-original-config.json').write_text(json.dumps(original, indent=2) + '\n')
cfg = output / 'nanoda-config.json'
cfg.write_text(json.dumps(config, indent=2) + '\n')
start = time.monotonic()
proc = subprocess.Popen([settings['nanoda'], str(cfg)], stdin=subprocess.PIPE)
h = hashlib.sha256()
count = 0
broken = False
while chunk := sys.stdin.buffer.read(1024 * 1024):
    h.update(chunk)
    count += len(chunk)
    if not broken:
        try:
            proc.stdin.write(chunk)
        except BrokenPipeError:
            broken = True
try:
    proc.stdin.close()
except BrokenPipeError:
    broken = True
status = proc.wait()
record = dict(seconds=time.monotonic() - start, exit_code=status,
              input_sha256=h.hexdigest(), input_bytes=count, broken_pipe=broken)
(output / 'nanoda-result.json').write_text(json.dumps(record, indent=2) + '\n')
print('Nanoda receipt:', json.dumps(record), flush=True)
raise SystemExit(status if status >= 0 else 128 - status)
