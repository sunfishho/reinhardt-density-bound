#!/usr/bin/env python3
"""Reconstruct the original degree-6 certificate and emit exact verification witnesses.
Floating point proposes factors only. All exported matrices and interval checks are exact.
The results of this script are not substitutes for the Lean proofs.
"""
from pathlib import Path
from fractions import Fraction as F
import contextlib,hashlib,io,json,math,os,sys,shutil,time
import numpy as np
ROOT=Path(__file__).resolve().parents[1]
DEST=ROOT/'data/source'
SRC=Path(os.environ.get('REINHARDT_SOURCE', str(DEST)))
old='/Users/matthewho/Downloads/Stanford/convex_problems/open_problems/trajectories/fable_5_1_review/semantic_overlap_review/main_results/recovered_audit_checks/reinhardt'
files=['m12lib.py','02_verify_exact.py','targets_recomputed.json','m12_problem.py','01_targets.py','certs/d4csdp_e7_meta.json']+[f'certs/d4csdp_e7_{i}.npz' for i in ['H1_0','H1_1','H1_2','H2']]
manifest=[]
for name in files:
 p=SRC/name;q=DEST/name;q.parent.mkdir(parents=True,exist_ok=True)
 if p.resolve()!=q.resolve():shutil.copyfile(p,q)
 manifest.append(dict(path=name,sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size))
(ROOT/'data/source_manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
sys.path.insert(0,str(DEST))
script=(DEST/'02_verify_exact.py').read_text().split('# ---- exact PSD')[0].replace(old,str(DEST))
scale=2**160;lo=math.isqrt(3*scale*scale);hi=lo+1
assert lo*lo<=3*scale*scale<=hi*hi
( ROOT/'data/exact').mkdir(exist_ok=True)
summary=[]
for ident in ['H1_0','H1_1','H1_2','H2']:
 start=time.monotonic();sys.argv=['02_verify_exact.py',ident,'40','d4csdp_e7',str(DEST/'targets_recomputed.json'),str(ROOT/'logs')]
 ns={};exec(compile(script,'inspected_exact_reconstruction','exec'),ns)
 assert ns['identity_ok']
 out=[]
 for idx,(name,Q,basis,q) in enumerate(ns['blocks']):
  n=len(Q);real=np.array([[float(v) for v in row] for row in Q]);real=(real+real.T)*.5
  eig=float(np.linalg.eigvalsh(real)[0]);assert eig>0,(ident,idx,eig)
  margin=2.**math.floor(math.log2(eig/4));floating=np.linalg.cholesky(real-margin*np.eye(n))
  for bits in [44,52,60]:
   ld=2**bits;L=[[round(float(v)*ld) for v in row] for row in floating];D=ld*ld
   for row in Q:
    for v in row:
     a=getattr(v,'a',v);b=getattr(v,'b',F(0));D=math.lcm(D,a.denominator,b.denominator)
   A=[[int(getattr(v,'a',v)*D) for v in row] for row in Q]
   B=[[int(getattr(v,'b',F(0))*D) for v in row] for row in Q]
   c=D//ld**2;slacks=[]
   for i in range(n):
    radius=0;diagonal=None
    for j in range(n):
     prod=sum(x*y for x,y in zip(L[i],L[j]));a=A[i][j]-c*prod;b=B[i][j]
     low=a*scale+min(b*lo,b*hi);up=a*scale+max(b*lo,b*hi)
     if i==j:diagonal=low
     else:radius+=max(abs(low),abs(up))
    slacks.append(diagonal-radius)
   if min(slacks)>0:break
  assert min(slacks)>0,(ident,idx,'interval witness failed')
  assert all(A[i][j]==A[j][i] and B[i][j]==B[j][i] for i in range(n) for j in range(n))
  def polynomial(p):return [[list(e),str(getattr(v,'a',v)),str(getattr(v,'b',F(0)))] for e,v in sorted(p.items())]
  out.append(dict(index=idx,name=name,n=n,basis=basis,multiplier=polynomial(q),denominator=D,c=c,factor_denominator=ld,A=A,B=B,L=L,min_integer_slack=str(min(slacks))))
  if idx%20==0:print(f'{ident}: proposed and exactly checked witnesses {idx+1}/{len(ns["blocks"])}',flush=True)
 gamma=ns.get('gamma');gamma=None if gamma is None else [str(gamma.a),str(gamma.b)]
 obj=dict(identity=ident,identity_python_exact=True,gamma=gamma,sqrt_scale=scale,sqrt_lo=lo,sqrt_hi=hi,blocks=out)
 path=ROOT/'data/exact'/f'{ident}.json';path.write_text(json.dumps(obj,separators=(',',':'))+'\n')
 summary.append(dict(identity=ident,blocks=len(out),shapes={str(n):sum(b['n']==n for b in out) for n in sorted({b['n'] for b in out})},gamma=gamma,sha256=hashlib.sha256(path.read_bytes()).hexdigest(),seconds=time.monotonic()-start))
 print(summary[-1],flush=True)
(ROOT/'data/exact/manifest.json').write_text(json.dumps(summary,indent=2)+'\n')
assert sum(s['blocks'] for s in summary)==248
