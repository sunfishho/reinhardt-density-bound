#!/usr/bin/env python3
"""Compile selected exact matrix proofs, recording timings, source hashes, and axiom audit.
A report is evidence only for the individual completed positivity theorem it names.
"""
from pathlib import Path
import argparse,concurrent.futures,hashlib,json,re,subprocess,sys,time
ROOT=Path(__file__).resolve().parents[1]
p=argparse.ArgumentParser();p.add_argument('--identity',choices=['H1_0','H1_1','H1_2','H2']);p.add_argument('--block',type=int);p.add_argument('--workers',type=int,default=1);p.add_argument('--resume',action='store_true');p.add_argument('--skip',action='append',default=[]);args=p.parse_args()
jobs=json.loads((ROOT/'Certificate/Generated/manifest.json').read_text())
jobs=[j for j in jobs if (args.identity is None or j['identity']==args.identity) and (args.block is None or j['block']==args.block) and f"{j['identity']}:{j['block']}" not in args.skip]
OUT=ROOT/'logs/matrices';OUT.mkdir(exist_ok=True)
core=['MatrixPositivity','IntervalSoundness','GramSoundness','DiagonalCheck','ListDotSoundness','FastGram']
basehash=hashlib.sha256(b''.join((ROOT/f'Certificate/{name}.lean').read_bytes() for name in core)+(ROOT/'lean-toolchain').read_bytes()+(ROOT/'lakefile.toml').read_bytes()).hexdigest()
allowed={'propext','Classical.choice','Quot.sound'}
def compile_job(job):
 tag=job['proof_module'].split('.')[-1];report_path=OUT/(tag+'.json')
 paths=[ROOT/Path(*job[k].split('.')).with_suffix('.lean') for k in ['data_module','proof_module']]
 shash=hashlib.sha256(b''.join(f.read_bytes() for f in paths)).hexdigest()
 if args.resume and report_path.exists():
  old=json.loads(report_path.read_text())
  if old.get('verified') and old.get('source_sha256')==shash and old.get('core_sha256')==basehash and all(f.with_suffix('.olean').exists() for f in paths):return old
 r=dict(job,source_sha256=shash,core_sha256=basehash,verified=False,stages=[]);start=time.monotonic()
 for path in paths:
  t=time.monotonic();run=subprocess.run([sys.executable,str(ROOT/'scripts/lean_cached.py'),'-o',str(path.with_suffix('.olean')),str(path)],cwd=ROOT,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
  (OUT/(path.stem+'.log')).write_text(run.stdout)
  stage=dict(module=path.stem,seconds=time.monotonic()-t,exit_code=run.returncode)
  timing_lines=[line[len('LEAN_BUILD '):] for line in run.stdout.splitlines() if line.startswith('LEAN_BUILD ')]
  if timing_lines:
   timing=json.loads(timing_lines[-1])
   stage.update({key:timing[key] for key in ['cache_hit','queue_seconds','dedup_wait_seconds','compile_seconds','cache_validation_seconds','timed_out'] if key in timing})
  r['stages'].append(stage)
  if run.returncode:
   r['error']='Lean compilation failed';break
 else:
  match=re.search(re.escape("'"+job['theorem']+"'")+r' depends on axioms: \[([^]]*)\]',run.stdout)
  if match:
   axioms={a.strip() for a in match.group(1).split(',') if a.strip()};r['axioms']=sorted(axioms)
   r['verified']=axioms.issubset(allowed)
  else:r['error']='Expected final theorem axiom audit was not found'
 r['compile_seconds']=sum(stage.get('compile_seconds',0) for stage in r['stages'])
 r['queue_seconds']=sum(stage.get('queue_seconds',0)+stage.get('dedup_wait_seconds',0) for stage in r['stages'])
 r['cache_hits']=sum(stage.get('cache_hit',False) for stage in r['stages'])
 r['seconds']=time.monotonic()-start
 report_path.write_text(json.dumps(r,indent=2)+'\n');return r
def report(result):
 print(json.dumps({k:result.get(k) for k in ['identity','block','n','verified','seconds','compile_seconds','queue_seconds','cache_hits','error']}),flush=True)
 return result['verified']
if args.workers==1:
 for job in jobs:
  if not report(compile_job(job)):raise SystemExit(1)
else:
 pool=concurrent.futures.ThreadPoolExecutor(max_workers=args.workers)
 todo=iter(jobs);pending=set();failed=False
 for _ in range(args.workers):
  job=next(todo,None)
  if job is not None:pending.add(pool.submit(compile_job,job))
 while pending and not failed:
  done,pending=concurrent.futures.wait(pending,return_when=concurrent.futures.FIRST_COMPLETED)
  for future in done:
   if not report(future.result()):failed=True
  if not failed:
   for _ in done:
    job=next(todo,None)
    if job is not None:pending.add(pool.submit(compile_job,job))
 pool.shutdown(wait=True,cancel_futures=failed)
 if failed:raise SystemExit(1)
