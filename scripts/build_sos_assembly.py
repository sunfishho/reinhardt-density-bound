#!/usr/bin/env python3
"""Assemble previously checked blocks and audit each derived nonnegativity theorem."""
from pathlib import Path
import argparse,hashlib,json,re,subprocess,sys,time
ROOT=Path(__file__).resolve().parents[1]
p=argparse.ArgumentParser();p.add_argument('--identity',choices=['H1_0','H1_1','H1_2','H2'],required=True);p.add_argument('--resume',action='store_true');p.add_argument('--block',type=int);args=p.parse_args()
OUT=ROOT/'logs/assembly';OUT.mkdir(exist_ok=True)
jobs=json.loads((ROOT/'Certificate/Assembly/manifest.json').read_text())
mods=[(j['module'],'nonnegative') for j in jobs if j['identity']==args.identity and (args.block is None or j['block']==args.block)]
bundles=json.loads((ROOT/'Certificate/Assembly/block_bundles.json').read_text()) if (ROOT/'Certificate/Assembly/block_bundles.json').exists() else []
selected_bundles=[b for b in bundles if b['identity']==args.identity]
if args.block is None and selected_bundles:
 mods=[(b['module'],'nonnegative') for b in selected_bundles]
if args.block is None:
 tree=ROOT/f'Certificate/Assembly/SumTrees/{args.identity}/manifest.json'
 if tree.exists():
  # Every chunk prints its last checked total theorem; all earlier ones are imports
  # or dependencies of that theorem and are included in the eventual final audit.
  for mod in json.loads(tree.read_text())['modules']:
   src=ROOT/Path(*mod.split('.')).with_suffix('.lean')
   audited=re.findall(r'^#print axioms (\S+)',src.read_text(),re.M)[-1]
   mods.append((mod,audited))
 mods.extend([(f'Certificate.Assembly.{args.identity}Sum','sum_identity'),(f'Certificate.Assembly.{args.identity}Proof','target_lower_bound')])
for mod,theorem in mods:
 path=ROOT/Path(*mod.split('.')).with_suffix('.lean');tag=path.stem
 if '.SumTrees.' in mod:tag=mod.split('.SumTrees.')[1].replace('.','_')
 shash=hashlib.sha256(path.read_bytes()).hexdigest();reportpath=OUT/(tag+'.json')
 # Imported build state is recorded as well, to avoid reusing reports across changed data.
 imports=re.findall(r'^import (\S+)',path.read_text(),re.M)
 deps=[ROOT/Path(*i.split('.')).with_suffix('.olean') for i in imports if i.startswith('Certificate.')]
 missing=[str(d.relative_to(ROOT)) for d in deps if not d.exists()]
 if missing:raise SystemExit('Build imported modules first: '+', '.join(missing))
 dhash=hashlib.sha256(b''.join(d.read_bytes() for d in deps)).hexdigest()
 if args.resume and reportpath.exists():
  old=json.loads(reportpath.read_text())
  if old.get('verified') and old.get('source_sha256')==shash and old.get('imports_sha256')==dhash and path.with_suffix('.olean').exists():continue
 start=time.monotonic()
 run=subprocess.run([sys.executable,str(ROOT/'scripts/lean_cached.py'),'-o',str(path.with_suffix('.olean')),str(path)],cwd=ROOT,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 (OUT/(tag+'.log')).write_text(run.stdout)
 if run.returncode:print(run.stdout);raise SystemExit(run.returncode)
 match=re.search(r"'([^']*\."+theorem+r")' depends on axioms: \[([^]]*)\]",run.stdout)
 assert match,'missing theorem audit'
 axioms={a.strip() for a in match.group(2).split(',') if a.strip()}
 assert axioms <= {'propext','Classical.choice','Quot.sound'},axioms
 for _,names in re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",run.stdout):
  assert {a.strip() for a in names.split(',') if a.strip()} <= {'propext','Classical.choice','Quot.sound'},names
 report=dict(module=mod,theorem=match.group(1),source_sha256=shash,imports_sha256=dhash,verified=True,axioms=sorted(axioms),seconds=time.monotonic()-start)
 reportpath.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report),flush=True)
