#!/usr/bin/env python3
"""Reconstruct the supplied Gram block, then propose a checkable PSD witness.
No optimization is run. Python/NumPy results are untrusted until checked in Lean.
"""
from pathlib import Path
from fractions import Fraction as F
import hashlib,json,math,sys,shutil
import numpy as np
ROOT=Path(__file__).resolve().parents[1]
SRC=Path('/Users/matthewho/Downloads/Stanford/ai-for-math/convex-lean-eval/convex_problems/open_problems/trajectories/fable_5_1_review/semantic_overlap_review/main_results/recovered_audit_checks/reinhardt')
DEST=ROOT/'data/source'
source_files=['m12lib.py','02_verify_exact.py','targets_recomputed.json','m12_problem.py','01_targets.py','certs/d4csdp_e7.json','certs/d4csdp_e7_H1_0.npz']
manifest=[]
for name in source_files:
 p=SRC/name
 if not p.exists():continue
 target=DEST/name;target.parent.mkdir(exist_ok=True,parents=True);shutil.copyfile(p,target)
 manifest.append(dict(path=name,sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size))
(ROOT/'data/source_manifest.json').write_text(json.dumps(manifest,indent=2))
sys.path.insert(0,str(DEST))
# Reuse only the inspected finite-data reconstruction portion of the old verifier.
script=(DEST/'02_verify_exact.py').read_text();script=script[:script.index('# ---- exact re-check')]
script=script.replace(str(SRC).replace('/ai-for-math/convex-lean-eval',''),str(DEST))
# The old code contains the pre-move path, replace it explicitly.
old='/Users/matthewho/Downloads/Stanford/convex_problems/open_problems/trajectories/fable_5_1_review/semantic_overlap_review/main_results/recovered_audit_checks/reinhardt'
script=script.replace(old,str(DEST))
sys.argv=['02_verify_exact.py','H1_0','40','d4csdp_e7',str(DEST/'targets_recomputed.json'),str(ROOT/'logs')]
ns={};exec(compile(script,'inspected_gram_reconstruction','exec'),ns)
_,Q,basis,_=ns['blocks'][0];n=len(Q);assert n==104
actual=np.array([[float(v) for v in row] for row in Q]);actual=(actual+actual.T)*.5
mineig=float(np.linalg.eigvalsh(actual)[0]);margin=2.**math.floor(math.log2(mineig/4))
L_float=np.linalg.cholesky(actual-margin*np.eye(n))
ld=2**44;L=[[round(float(v)*ld) for v in row] for row in L_float]
D=ld*ld
for row in Q:
 for v in row:
  a=getattr(v,'a',v);b=getattr(v,'b',F(0))
  D=math.lcm(D,a.denominator,b.denominator)
A=[[int(getattr(v,'a',v)*D) for v in row] for row in Q]
B=[[int(getattr(v,'b',F(0))*D) for v in row] for row in Q]
scale=2**160;slo=math.isqrt(3*scale*scale);shi=slo+1
assert slo*slo<=3*scale*scale<=shi*shi
c=D//ld**2;minrow=None
for i in range(n):
 diaglo=None;radius=0
 for j in range(n):
  dot=sum(x*y for x,y in zip(L[i],L[j]));a=A[i][j]-c*dot;b=B[i][j]
  lo=a*scale+min(b*slo,b*shi);hi=a*scale+max(b*slo,b*shi)
  if i==j:diaglo=lo
  else:radius+=max(abs(lo),abs(hi))
 slack=diaglo-radius;assert slack>0,(i,float(F(slack,D*scale)))
 minrow=slack if minrow is None else min(minrow,slack)
def ls(xs):return '['+', '.join(str(x) for x in xs)+']'
def mat(rows):return '[\n  '+',\n  '.join(ls(row) for row in rows)+'\n]'
data=dict(n=n,denominator=D,factor_denominator=ld,sqrt_scale=scale,sqrt_lo=slo,sqrt_hi=shi,A=A,B=B,L=L,basis=basis,proposed_margin=margin,min_diagonal_slack=float(F(minrow,D*scale)),original_min_eigenvalue=mineig)
(ROOT/'data/benchmark_H1_0_block0.json').write_text(json.dumps(data,separators=(',',':')))
lean='import Certificate.DiagonalCheck\nset_option maxHeartbeats 0\nset_option maxRecDepth 100000\nnamespace Certificate.Benchmark\n'
for key,value in [('n',n),('denominator',D),('factorDenominator',ld),('sqrtScale',scale),('sqrtLo',slo),('sqrtHi',shi)]:lean+=f'def {key} : '+('Nat' if key=='n' else 'Int')+f' := {value}\n'
for key,value in [('gramA',A),('gramB',B),('factor',L)]:lean+=f'def {key} : List (List Int) := {mat(value)}\n'
lean+='end Certificate.Benchmark\n';(ROOT/'Certificate/BenchmarkData.lean').write_text(lean)
print(json.dumps({k:data[k] for k in ['n','proposed_margin','min_diagonal_slack','original_min_eigenvalue']},indent=2),flush=True)
