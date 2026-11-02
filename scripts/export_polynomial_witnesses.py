#!/usr/bin/env python3
"""Mechanical ideal-membership witnesses for the four exact identities.
This is untrusted witness generation, not optimization and not a Lean proof.
"""
from pathlib import Path
from fractions import Fraction as F
import hashlib,json,math,sys,time
import sympy as sp
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'data/source'))
import m12_problem as mp
OUT=ROOT/'data/polynomials';OUT.mkdir(exist_ok=True)
zero=(0,)*8

def addto(p,e,c):
 if not c:return
 p[e]=p.get(e,0)+c
 if not p[e]:del p[e]
def add(p,q,scale=1):
 out=dict(p)
 for e,c in q.items():addto(out,e,c*scale)
 return out
def mul(p,q):
 out={}
 for e,c in p.items():
  for f,d in q.items():addto(out,tuple(a+b for a,b in zip(e,f)),c*d)
 return out
def scaled(p,c):return {e:v*c for e,v in p.items() if v*c}
def var(i,k=1):
 e=[0]*8;e[i]=k;return tuple(e)
def from_sympy(expr):
 return {tuple(e):F(int(c.p),int(c.q)) for e,c in sp.Poly(sp.expand(expr),*mp.SYMS,mp.s3).terms() if c}
def from_json(poly):
 p={}
 for e,a,b in poly:
  addto(p,tuple(e)+(0,),F(a));addto(p,tuple(e)+(1,),F(b))
 return p
def key(e):return sum(v*16**i for i,v in enumerate(e))
def terms(p):return [[str(c),list(e)] for e,c in sorted(p.items(),key=lambda z:key(z[0]))]
def integerize(p,den):
 out={}
 for e,c in p.items():
  v=c*den;assert v.denominator==1,(e,v);addto(out,e,v.numerator)
 return out
Gg={tuple([1,0,0,1,0,0,0,0]):1,tuple([0,1,1,0,0,0,0,0]):-1,zero:-1}
Gh={var(6,2):1,var(4,2):-1,var(5,2):-1,zero:-1}
Gt={var(7,2):1,zero:-3}

def divide(p):
 pending=dict(p);qs={k:{} for k in ['g','h','t']};rem={}
 while pending:
  e,c=pending.popitem()
  if e[7]>=2:
   lead=var(7,2);name='t';g=Gt
  elif e[6]>=2:
   lead=var(6,2);name='h';g=Gh
  elif e[0] and e[3]:
   lead=(1,0,0,1,0,0,0,0);name='g';g=Gg
  else:addto(rem,e,c);continue
  f=tuple(a-b for a,b in zip(e,lead));addto(qs[name],f,c)
  for mon,coef in g.items():
   if mon!=lead:addto(pending,tuple(a+b for a,b in zip(f,mon)),-c*coef)
 return qs,rem

V,meta=mp.load_V(str(ROOT/'data/source/certs/d4csdp_e7_meta.json'))
pV=from_sympy(V);DV=math.lcm(*(v.denominator for v in pV.values()))
(OUT/'potential.json').write_text(json.dumps(dict(denominator=DV,terms=terms(integerize(pV,DV))),separators=(',',':'))+'\n')
summary=[]
for ident in ['H1_0','H1_1','H1_2','H2']:
 start=time.monotonic();data=json.loads((ROOT/'data/exact'/f'{ident}.json').read_text())
 if ident.startswith('H1'):
  raw=mp.H_of_V_sympy(V,int(ident[-1]))
 else:
  ar,pr,hr=mp.conj_comps(mp.R)
  VR=V.subs({mp.g11:mp.R[0,0],mp.g12:mp.R[0,1],mp.g21:mp.R[1,0],mp.g22:mp.R[1,1]},simultaneous=True)
  VR=VR.subs({mp.a:ar,mp.p:pr,mp.h:hr},simultaneous=True)
  VI=V.subs({mp.g11:1,mp.g12:0,mp.g21:0,mp.g22:1},simultaneous=True)
  raw=VR-VI
 target=from_sympy(raw);gamma={}
 if data['gamma']:
  gamma={zero:F(data['gamma'][0]),var(7):F(data['gamma'][1])}
 S=math.lcm(*(v.denominator for v in list(target.values())+list(gamma.values())))
 blocks=[];total={}
 for b in data['blocks']:
  gram={};n=b['n'];den=b['denominator']
  for i in range(n):
   for j in range(i,n):
    e=tuple(x+y for x,y in zip(b['basis'][i],b['basis'][j]));fac=1 if i==j else 2
    addto(gram,e+(0,),fac*b['A'][i][j]);addto(gram,e+(1,),fac*b['B'][i][j])
  q=from_json(b['multiplier']);qd=math.lcm(*(v.denominator for v in q.values()));qi=integerize(q,qd)
  product=mul(gram,qi);denprod=den*qd;S=math.lcm(S,denprod)
  total=add(total,scaled(product,F(1,denprod)))
  blocks.append(dict(index=b['index'],name=b['name'],denominator_product=denprod,multiplier_denominator=qd,gram_integer_poly=terms(gram),multiplier_integer_poly=terms(qi),weighted_integer_poly=terms(product)))
 p=integerize(add(add(target,gamma,-1),total,-1),S)
 quotients,remainder=divide(p);assert not remainder,(ident,'nonzero remainder',terms(remainder)[:3])
 rebuilt=add(add(mul(quotients['g'],Gg),mul(quotients['h'],Gh)),mul(quotients['t'],Gt))
 assert rebuilt==p,(ident,'ideal identity replay failed')
 for b in blocks:
  assert S%b['denominator_product']==0
  b['scale_multiplier']=S//b['denominator_product']
 obj=dict(identity=ident,global_denominator=S,raw_target=terms(integerize(target,S)),gamma=terms(integerize(gamma,S)),summed_sos=terms(integerize(total,S)),quotients={k:terms(v) for k,v in quotients.items()},generators={k:terms(v) for k,v in [('g',Gg),('h',Gh),('t',Gt)]},blocks=blocks,python_ideal_identity_exact=True,lean_identity_verified=False)
 path=OUT/f'{ident}.json';path.write_text(json.dumps(obj,separators=(',',':'))+'\n')
 record=dict(identity=ident,target_terms=len(target),sos_terms=len(total),difference_terms=len(p),quotient_terms={k:len(v) for k,v in quotients.items()},scale_bits=S.bit_length(),sha256=hashlib.sha256(path.read_bytes()).hexdigest(),seconds=time.monotonic()-start)
 summary.append(record);print(json.dumps(record),flush=True)
(OUT/'manifest.json').write_text(json.dumps(summary,indent=2)+'\n')
