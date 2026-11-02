#!/usr/bin/env python3
"""Emit the actual potential and semantic differentiation/substitution checks."""
from pathlib import Path
import json,sys
import sympy as sp
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'data/source'))
import m12_problem as mp
OUT=ROOT/'Certificate/Potential';OUT.mkdir(exist_ok=True)
def key(e):return sum(v*16**i for i,v in enumerate(e))
def terms(expr):
 vals=[]
 for e,c in sp.Poly(sp.expand(expr),*mp.SYMS,mp.s3).terms():
  assert c.q==1
  if c:vals.append((int(c),list(e)))
 return sorted(vals,key=lambda t:key(t[1]))
def ilit(c):
 c=int(c);return f'Int.ofNat {c}' if c>=0 else f'Int.negSucc {-c-1}'
def term(t):return '('+ilit(t[0])+', ⟨'+', '.join(map(str,t[1]))+'⟩)'
def poly(ts):return '['+', '.join(term(t) for t in ts)+']'
def emit(name,ts):return f'noncomputable def {name} : Polynomial := '+poly(ts)+'\n'
pv=json.loads((ROOT/'data/polynomials/potential.json').read_text());dv=pv['denominator']
s='''import Certificate.DirectionalPolynomial
import Certificate.PolynomialSubstitution
namespace Certificate.Potential
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
'''
chunks=[]
for i in range(0,len(pv['terms']),64):
 n=f'potential_{i//64}';chunks.append(n);s+=emit(n,pv['terms'][i:i+64])
s+='noncomputable def polynomial : Polynomial := '+' ++ '.join(chunks)+'\n'
s+=f'noncomputable def denominator : ℤ := {dv}\n'
s+='noncomputable def value (x : Fin 8 → ℝ) : ℝ := eval x polynomial / denominator\n'
s+='theorem degree_bound : ∀ term ∈ polynomial, term.2.totalDegree ≤ 4 := by decide +kernel\n'
s+='theorem denominator_pos : 0 < denominator := by decide +kernel\n'
gX=mp.gmat*mp.X;gv=list(gX)+[0,0,0,0]
s+='noncomputable def gVelocity : Fin 8 → Polynomial := !['+', '.join(poly(terms(v)) for v in gv)+']\n'
s+=emit('cost',terms(mp.L))
for k in range(3):
 s+=emit(f'r3_{k}',terms(3*mp.RHO[k]))
 nv=[0,0,0,0]+[3*v for v in mp.NK_COMPS[k]]+[0]
 s+=f'noncomputable def xVelocity3_{k} : Fin 8 → Polynomial := !['+', '.join(poly(terms(v)) for v in nv)+']\n'
 s+=f'''noncomputable def clearedTarget_{k} : Polynomial :=
  merge (mulFast r3_{k} (merge (scale denominator cost)
    (scale (-1) (directionalPolynomial polynomial gVelocity))))
    (scale (-1) (directionalPolynomial polynomial xVelocity3_{k}))
'''
a,p,h,t=mp.a,mp.p,mp.h,mp.s3
sigR=[1,-t,t,1,-a+t*p,-t*a-p,2*h,2*t]
sigI=[2,0,0,2,2*a,2*p,2*h,2*t]
for n,vs in [('rotatedCoordinates2',sigR),('initialCoordinates2',sigI)]:
 s+=f'noncomputable def {n} : Fin 8 → Polynomial := !['+', '.join(poly(terms(v)) for v in vs)+']\n'
s+='''noncomputable def boundaryTarget : Polynomial :=
  merge (scaledSubstitute polynomial rotatedCoordinates2 2 4)
    (scale (-1) (scaledSubstitute polynomial initialCoordinates2 2 4))
end Certificate.Potential
'''
(OUT/'Data.lean').write_text(s)
for ident in ['H1_0','H1_1','H1_2','H2']:
 data=json.loads((ROOT/f'data/polynomials/{ident}.json').read_text())
 fac=16 if ident=='H2' else 3
 assert data['global_denominator']%(fac*dv)==0
 scale=data['global_denominator']//(fac*dv)
 target='boundaryTarget' if ident=='H2' else 'clearedTarget_'+ident[-1]
 s=f'''import Certificate.Potential.Data
import Certificate.Identities.{ident}Data
namespace Certificate.Potential.{ident}
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
noncomputable def scaleFactor : ℤ := {scale}
theorem scale_positive : 0 < scaleFactor := by decide +kernel
/-- Exact differentiation/substitution of the stored potential, not an assumed target. -/
theorem semantic_check : checkEqual (scale scaleFactor {target}) Certificate.Identities.{ident}.target = true := by
  decide +kernel

theorem semantic_identity (x : Fin 8 → ℝ) :
    eval x Certificate.Identities.{ident}.target = (scaleFactor : ℝ)*eval x {target} := by
  have he := eq_of_check x _ _ semantic_check
  simpa only [eval_scale] using he.symm
#print axioms semantic_identity
end Certificate.Potential.{ident}
'''
 (OUT/f'{ident}.lean').write_text(s)
print('Generated potential and four semantic checks (not yet verified).')
