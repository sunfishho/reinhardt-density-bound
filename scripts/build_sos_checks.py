#!/usr/bin/env python3
"""Check recorded polynomial expansions against each actual Gram block.
This does not by itself prove primitive constraints nonnegative or differentiate V.
"""
from pathlib import Path
import argparse,hashlib,json,re,subprocess,sys,time
ROOT=Path(__file__).resolve().parents[1]
p=argparse.ArgumentParser();p.add_argument('--identity',choices=['H1_0','H1_1','H1_2','H2']);p.add_argument('--block',type=int);p.add_argument('--resume',action='store_true');p.add_argument('--memory-mb',type=int);args=p.parse_args()
jobs=json.loads((ROOT/'Certificate/SOS/manifest.json').read_text())
jobs=[j for j in jobs if (args.identity is None or j['identity']==args.identity) and (args.block is None or j['block']==args.block)]
OUT=ROOT/'logs/sos';OUT.mkdir(exist_ok=True)
core=['MatrixPositivity','IntervalSoundness','GramSoundness','DiagonalCheck','ListDotSoundness','FastGram','SparsePolynomial','SOSPolynomial']
basehash=hashlib.sha256(b''.join((ROOT/f'Certificate/{name}.lean').read_bytes() for name in core)).hexdigest()
for j in jobs:
 start=time.monotonic();tag=j['proof'].split('.')[-1];reportpath=OUT/(tag+'.json')
 modules=[j['matrix_data'],j['data']]+j.get('auxiliary',[])+[j['proof']]
 paths=[ROOT/Path(*module.split('.')).with_suffix('.lean') for module in modules]
 shash=hashlib.sha256(b''.join(f.read_bytes() for f in paths)).hexdigest()
 prooftext=paths[-1].read_text()
 chunked=bool(j.get('auxiliary'))
 short='import Certificate.ShortMultiplication' in prooftext
 jobcore=core+(['FastExpansion'] if chunked or 'import Certificate.FastExpansion' in prooftext or 'import Certificate.SparseExpansion' in prooftext else [])
 jobcore += [name for name in ['SparseExpansion','MergeArithmetic','ChunkedExpansion','ShortMultiplication'] if 'import Certificate.'+name in prooftext or name=='MergeArithmetic' and (short or chunked) or name=='ChunkedExpansion' and chunked]
 jobhash=hashlib.sha256(b''.join((ROOT/f'Certificate/{name}.lean').read_bytes() for name in jobcore)).hexdigest()
 if args.resume and reportpath.exists():
  old=json.loads(reportpath.read_text())
  if old.get('expansion_verified') and old.get('source_sha256')==shash and old.get('core_sha256')==jobhash and all(f.with_suffix('.olean').exists() for f in paths):continue
 stages=[]
 for path in paths:
  t=time.monotonic();run=subprocess.run([sys.executable,str(ROOT/'scripts/lean_cached.py')]+(['-M',str(args.memory_mb)] if args.memory_mb else [])+['-o',str(path.with_suffix('.olean')),str(path)],cwd=ROOT,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
  (OUT/(path.stem+'.log')).write_text(run.stdout)
  stage=dict(module=path.stem,seconds=time.monotonic()-t,exit_code=run.returncode)
  timing_lines=[line[len('LEAN_BUILD '):] for line in run.stdout.splitlines() if line.startswith('LEAN_BUILD ')]
  if timing_lines:
   timing=json.loads(timing_lines[-1])
   stage.update({key:timing[key] for key in ['cache_hit','queue_seconds','dedup_wait_seconds','compile_seconds','cache_validation_seconds','overhead_seconds','timed_out'] if key in timing})
   if timing.get('provenance_incomplete'):stage['provenance_incomplete']=timing['provenance_incomplete']
  stages.append(stage)
  if run.returncode:print(run.stdout);raise SystemExit(run.returncode)
 theorem=j['proof'].replace('Proof','')+'.weighted_nonnegative'
 match=re.search(re.escape("'"+theorem+"'")+r' depends on axioms: \[([^]]*)\]',run.stdout)
 assert match,'expected final theorem audit missing'
 axioms={a.strip() for a in match.group(1).split(',') if a.strip()}
 assert axioms <= {'propext','Classical.choice','Quot.sound'}
 r=dict(j,compile_seconds=sum(stage.get('compile_seconds',0) for stage in stages),queue_seconds=sum(stage.get('queue_seconds',0)+stage.get('dedup_wait_seconds',0) for stage in stages),cache_hits=sum(stage.get('cache_hit',False) for stage in stages),source_sha256=shash,core_sha256=jobhash,expansion_verified=True,multiplier_nonnegativity_verified=False,axioms=sorted(axioms),seconds=time.monotonic()-start,stages=stages)
 reportpath.write_text(json.dumps(r,indent=2)+'\n')
 print(json.dumps({k:r[k] for k in ['identity','block','expansion_verified','seconds','compile_seconds','queue_seconds','cache_hits']}),flush=True)
