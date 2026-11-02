#!/usr/bin/env python3
"""Record the exact upstream export bytes passed through to Comparator."""
from pathlib import Path
import datetime
import hashlib
import json
import os
import subprocess
import sys
import time

base = Path(__file__).resolve().parent
settings = json.loads((base / 'paths.json').read_text())
output = Path(os.environ['REINHARDT_COMPARATOR_RECEIPT'])
module = sys.argv[1]
if not module.replace('_', '').isalnum():
    raise SystemExit('Unexpected export module')
dest = output / (module + '.ndjson')
env = dict(os.environ)
# Keep challenge and solution definitions in separate environments even though
# they have matching declaration names.
paths = settings['solution_paths'] if module == 'Solution' else settings['challenge_paths']
env['LEAN_PATH'] = os.pathsep.join([str(base / '.lake/build/lib/lean'), *paths])
start = time.monotonic()
started = datetime.datetime.now(datetime.timezone.utc).isoformat()
proc = subprocess.Popen([settings['exporter'], *sys.argv[1:]], env=env, stdout=subprocess.PIPE)
h = hashlib.sha256()
count = 0
with dest.open('wb') as f:
    while chunk := proc.stdout.read(1024 * 1024):
        h.update(chunk)
        count += len(chunk)
        f.write(chunk)
        sys.stdout.buffer.write(chunk)
    sys.stdout.buffer.flush()
status = proc.wait()
record = dict(module=module, arguments=sys.argv[1:], started_at=started,
              seconds=time.monotonic() - start, bytes=count, sha256=h.hexdigest(),
              exit_code=status, complete=status == 0)
(output / (module + '-export.json')).write_text(json.dumps(record, indent=2) + '\n')
print('Recorded export:', json.dumps(record), file=sys.stderr, flush=True)
raise SystemExit(status)
