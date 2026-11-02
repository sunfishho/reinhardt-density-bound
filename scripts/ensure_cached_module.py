#!/usr/bin/env python3
"""Compile missing pinned mathlib modules locally; leave the source cache untouched."""
import os,re,shutil,subprocess,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
CACHE=Path(os.environ.get('REINHARDT_CACHED_PROJECT','/Users/matthewho/.codex/.chatgpt-projects/g-p-6a5ad858ad18819189c51db74c9c12e9/courtade-kumar-publish'))
SOURCE=CACHE/'.lake/packages/mathlib'
seen=set()
def visit(name):
 if name in seen:return
 seen.add(name);relative=Path(*name.split('.'))
 output=ROOT/'.lake/build/lib/lean'/relative.with_suffix('.olean')
 if output.exists():return
 src=SOURCE/relative.with_suffix('.lean')
 if not src.exists():raise FileNotFoundError(src)
 for dep in re.findall(r'^(?:public |private )?import ([A-Za-z0-9_.]+)',src.read_text(),re.M):visit(dep)
 dest=ROOT/'vendor_mathlib'/Path(*name.split('.')[1:]).with_suffix('.lean');dest.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src,dest)
 output.parent.mkdir(parents=True,exist_ok=True)
 print('Compiling missing cached module:',name,flush=True)
 subprocess.run([sys.executable,str(ROOT/'scripts/lean_cached.py'),'-o',str(output),str(dest)],check=True,cwd=ROOT)
for name in sys.argv[1:]:visit(name)
