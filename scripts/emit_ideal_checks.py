#!/usr/bin/env python3
"""Generate ideal-identity checks against recorded SOS polynomials.
These are one stage of the proof; the recorded SOS polynomial must separately
be linked in Lean to the supplied Gram matrices and monomial bases.
"""
from pathlib import Path
import json
ROOT=Path(__file__).resolve().parents[1];OUT=ROOT/'Certificate/Identities';OUT.mkdir(exist_ok=True)
def lit(v):
 v=int(v);return f'Int.ofNat {v}' if v>=0 else f'Int.negSucc {-v-1}'
def term(t):
 c,e=t;return '('+lit(c)+', ⟨'+', '.join(str(i) for i in e)+'⟩)'
for ident in ['H1_0','H1_1','H1_2','H2']:
 path=ROOT/'data/polynomials'/f'{ident}.json'
 if not path.exists():continue
 d=json.loads(path.read_text());ns=f'Certificate.Identities.{ident}'
 s=f'import Certificate.SparsePolynomial\nnamespace {ns}\nopen Certificate.Sparse\nset_option maxHeartbeats 0\nset_option maxRecDepth 100000\n'
 vals=[('target',d['raw_target']),('gamma',d['gamma']),('recordedSOS',d['summed_sos'])]+[(f'q{k}',v) for k,v in d['quotients'].items()]+[(f'g{k}',v) for k,v in d['generators'].items()]
 for name,terms in vals:
  names=[]
  for i in range(0,len(terms),64):
   nm=f'{name}_{i//64}';names.append(nm)
   s+=f'noncomputable def {nm} : Polynomial := [\n  '+',\n  '.join(term(t) for t in terms[i:i+64])+']\n'
  s+=f'noncomputable def {name} : Polynomial := '+(' ++ '.join(names) if names else '[]')+'\n'
 s+=f'noncomputable def globalDenominator : ℤ := {d["global_denominator"]}\nend {ns}\n'
 (OUT/f'{ident}Data.lean').write_text(s)
 p=f'import Certificate.Identities.{ident}Data\nnamespace {ns}\nopen Certificate.Sparse\nset_option maxHeartbeats 0\nset_option maxRecDepth 100000\nset_option Elab.async false\n'
 p+='''/-- This checks the quotient/reduction stage only. The connection between
`recordedSOS` and the actual Gram blocks is a separate obligation. -/
theorem quotient_check : checkEqual target
    (merge gamma (merge recordedSOS (merge (mulFast qg gg)
      (merge (mulFast qh gh) (mulFast qt gt))))) = true := by
  decide +kernel

/-- A universal polynomial identity, with no geometric hypotheses. -/
theorem quotient_identity {R : Type*} [CommRing R] (x : Fin 8 → R) :
    eval x target = eval x gamma + eval x recordedSOS +
      eval x qg * eval x gg + eval x qh * eval x gh + eval x qt * eval x gt := by
  have h := eq_of_check x _ _ quotient_check
  simpa only [eval_merge,eval_mulFast,add_assoc] using h
#print axioms quotient_identity
'''
 p+='end '+ns+'\n';(OUT/f'{ident}Proof.lean').write_text(p)
print('Generated ideal checks')
