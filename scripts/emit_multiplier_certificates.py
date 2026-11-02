#!/usr/bin/env python3
"""Generate exact multiplier identities relative to the 19 primitive constraints."""
from pathlib import Path
from fractions import Fraction as F
import json,math
ROOT=Path(__file__).resolve().parents[1]
labels=['sector1','sector2','sector1Rot1','sector2Rot1','sector1Rot2','sector2Rot2','gNorm','denominator0','denominator1','denominator2','hLower','hUpper','xNorm','horoballY','horoballPlus','horoballMinus','halfplane0','halfplane1','halfplane2']
constraints=json.loads((ROOT/'data/source/targets_recomputed.json').read_text())['constraints'];labelmap=dict(zip(constraints,labels));assert len(labelmap)==19
zero=(0,)*8

def addto(p,e,c):
 if not c:return
 p[e]=p.get(e,0)+c
 if not p[e]:del p[e]
def mul(p,q):
 r={}
 for e,c in p.items():
  for f,d in q.items():addto(r,tuple(a+b for a,b in zip(e,f)),c*d)
 return r
def scaled(p,c):return {e:v*c for e,v in p.items() if v*c}
def from_constraint(vals):
 p={}
 for e,a,b in vals:
  addto(p,tuple(e)+(0,),F(a));addto(p,tuple(e)+(1,),F(b))
 den=math.lcm(*(v.denominator for v in p.values()))
 return den,{e:int(v*den) for e,v in p.items()}
def key(e):return sum(v*16**i for i,v in enumerate(e))
def serialize(p):return [[str(c),list(e)] for e,c in sorted(p.items(),key=lambda z:key(z[0]))]
def ilit(v):return f'Int.ofNat {v}' if v>=0 else f'Int.negSucc {-v-1}'
def lean(p):return '['+', '.join('('+ilit(c)+', ⟨'+', '.join(str(i) for i in e)+'⟩)' for e,c in sorted(p.items(),key=lambda z:key(z[0])))+']'
primitive={k:from_constraint(v) for k,v in constraints.items()}
s='import Certificate.MultiplierSoundness\nnamespace Certificate.PrimitiveData\nopen Certificate.Sparse\n'
for name,(den,p) in primitive.items():s+=f'noncomputable def {labelmap[name]} : Polynomial := {lean(p)}\n'
s+='noncomputable def polynomial : ConstraintLabel → Polynomial\n'
for name,label in labelmap.items():s+=f'  | .{label} => {label}\n'
s+='def Region (x : Fin 8 → ℝ) : Prop := ∀ label, 0 ≤ eval x (polynomial label)\nend Certificate.PrimitiveData\n'
(ROOT/'Certificate/PrimitiveData.lean').write_text(s)
unique={}
for ident in ['H1_0','H1_1','H1_2','H2']:
 for b in json.loads((ROOT/'data/polynomials'/f'{ident}.json').read_text())['blocks']:
  value=(b['multiplier_denominator'],b['multiplier_integer_poly'])
  if b['name'] in unique:assert unique[b['name']]==value
  else:unique[b['name']]=value
out=[];s='import Certificate.PrimitiveData\nnamespace Certificate.MultiplierProofs\nopen Certificate.Sparse\nset_option maxHeartbeats 0\nset_option maxRecDepth 100000\nset_option Elab.async false\n'
for idx,(name,(dq,qvals)) in enumerate(unique.items()):
 q={tuple(e):int(c) for c,e in qvals};names=[] if name=='1' else name.split('*');prod={zero:1};dp=1
 for nm in names:
  den,p=primitive[nm];dp*=den;prod=mul(prod,p)
 diff=scaled(q,dp)
 for e,c in prod.items():addto(diff,e,-dq*c)
 todo=dict(diff);quot={};rem={}
 while todo:
  e,c=todo.popitem()
  if e[7]>=2:
   f=list(e);f[7]-=2;f=tuple(f);addto(quot,f,c);addto(todo,f,3*c)
  else:addto(rem,e,c)
 assert not rem,(name,'nonzero square-root remainder',rem)
 out.append(dict(index=idx,name=name,labels=names,product_denominator=dp,multiplier_denominator=dq,polynomial=serialize(q),sqrt_correction=serialize(quot)))
 s+=f'namespace M{idx:03d}\nnoncomputable def certificate : MultiplierCertificate where\n'
 s+='  labels := ['+', '.join('.'+labelmap[n] for n in names)+']\n'
 s+=f'  polynomial := {lean(q)}\n  productDenominator := {dp}\n  multiplierDenominator := {dq}\n  sqrtCorrection := {lean(quot)}\n'
 s+='''theorem checked : certificate.check PrimitiveData.polynomial = true := by
  unfold MultiplierCertificate.check
  decide +kernel

theorem nonnegative (x : Fin 8 → ℝ) (hroot : (x 7)^2=3) (hregion : PrimitiveData.Region x) :
    0 ≤ eval x certificate.polynomial :=
  MultiplierCertificate.nonnegative certificate PrimitiveData.polynomial checked
    (by decide +kernel) (by decide +kernel) x hroot hregion
#print axioms nonnegative
'''
 s+=f'end M{idx:03d}\n'
s+='end Certificate.MultiplierProofs\n';(ROOT/'Certificate/MultiplierCertificates.lean').write_text(s)
(ROOT/'data/multipliers.json').write_text(json.dumps(out,indent=2)+'\n')
(ROOT/'data/primitives.json').write_text(json.dumps({k:dict(label=labelmap[k],denominator=d,polynomial=serialize(p)) for k,(d,p) in primitive.items()},indent=2)+'\n')
print('Generated',len(out),'distinct multiplier certificates from',len(primitive),'primitive constraints')
