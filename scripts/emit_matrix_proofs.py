#!/usr/bin/env python3
"""Generate exact matrix data and kernel-reduced arithmetic proof obligations.
The generator is untrusted: Lean verifies every resulting positivity proof.
"""
from pathlib import Path
import json
ROOT=Path(__file__).resolve().parents[1]
OUT=ROOT/'Certificate/Generated';OUT.mkdir(exist_ok=True)
def lit(v):return f'Int.ofNat {v}' if v>=0 else f'Int.negSucc {-v-1}'
jobs=[]
for ident in ['H1_0','H1_1','H1_2','H2']:
 obj=json.loads((ROOT/'data/exact'/f'{ident}.json').read_text())
 for block in obj['blocks']:
  tag=f'{ident}B{block["index"]:03d}';ns='Certificate.Generated.'+tag;n=block['n']
  text='import Certificate.FastGram\n\nset_option maxHeartbeats 0\nset_option maxRecDepth 100000\nnamespace '+ns+'\n'
  for name,field in [('a','A'),('b','B'),('factor','L')]:
   for i,row in enumerate(block[field]):text+=f'noncomputable def {name}_{i} : List ℤ := ['+', '.join(lit(x) for x in row)+']\n'
   text+=f'noncomputable def {name} : List (List ℤ) := ['+', '.join(f'{name}_{i}' for i in range(n))+']\n'
  text+='noncomputable def data : GramData where\n'
  for key,value in [('size',n),('den',block['denominator']),('c',block['c']),('scale',obj['sqrt_scale']),('lo',obj['sqrt_lo']),('hi',obj['sqrt_hi'])]:text+=f'  {key} := {value}\n'
  text+='  a := a\n  b := b\n  factor := factor\nend '+ns+'\n'
  (OUT/(tag+'Data.lean')).write_text(text)
  p=f'import Certificate.Generated.{tag}Data\nimport Mathlib.Tactic.FinCases\nnamespace {ns}\nset_option maxHeartbeats 0\nset_option maxRecDepth 100000\nset_option Elab.async false\n'
  p+='theorem scalar_conditions : data.ScalarConditions := by\n  unfold GramData.ScalarConditions\n  decide +kernel\n'
  p+='theorem factor_shape : ∀ i, (data.factorRow i).length = data.size := by decide +kernel\n'
  p+='theorem symmetric_a : ∀ i j, data.A j i = data.A i j := data.symmetric_A\n'
  p+='theorem symmetric_b : ∀ i j, data.B j i = data.B i j := data.symmetric_B\n'
  for i in range(n):p+=f'theorem row_{i} : data.RowCondition (⟨{i}, by decide +kernel⟩ : Fin data.size) := by\n  unfold GramData.RowCondition\n  decide +kernel\n'
  p+='theorem all_rows : ∀ i, data.RowCondition i := by\n  intro i\n  fin_cases i\n'
  for i in range(n):p+=f'  · exact row_{i}\n'
  p+='theorem positive_semidefinite : (realGram data.A data.B data.den).PosSemidef :=\n  data.sound scalar_conditions factor_shape symmetric_a symmetric_b all_rows\n'
  p+='#print axioms positive_semidefinite\nend '+ns+'\n'
  (OUT/(tag+'Proof.lean')).write_text(p)
  jobs.append(dict(identity=ident,block=block['index'],name=block['name'],n=n,data_module=f'Certificate.Generated.{tag}Data',proof_module=f'Certificate.Generated.{tag}Proof',theorem=ns+'.positive_semidefinite'))
(OUT/'manifest.json').write_text(json.dumps(jobs,indent=2)+'\n')
print(f'Generated {len(jobs)} exact matrix data/proof pairs')
