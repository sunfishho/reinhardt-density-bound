#!/usr/bin/env python3
"""Emit checks linking recorded block polynomials to actual Gram matrices."""
from pathlib import Path
import json,subprocess,sys
ROOT=Path(__file__).resolve().parents[1];OUT=ROOT/'Certificate/SOS';OUT.mkdir(exist_ok=True)
def write_if_changed(path, text):
 if not path.exists() or path.read_text()!=text:path.write_text(text)
def ilit(v):
 v=int(v);return f'Int.ofNat {v}' if v>=0 else f'Int.negSucc {-v-1}'
def term(t):
 c,e=t;return '('+ilit(c)+', ⟨'+', '.join(str(i) for i in e)+'⟩)'
jobs=[]
for ident in ['H1_0','H1_1','H1_2','H2']:
 pd=json.loads((ROOT/'data/polynomials'/f'{ident}.json').read_text());md=json.loads((ROOT/'data/exact'/f'{ident}.json').read_text())
 for b,m in zip(pd['blocks'],md['blocks']):
  assert b['index']==m['index'];tag=f'{ident}B{b["index"]:03d}';ns='Certificate.SOS.'+tag;g='Certificate.Generated.'+tag
  s=f'import Certificate.Generated.{tag}Data\nimport Certificate.SOSPolynomial\nnamespace {ns}\nopen Certificate.Sparse\nset_option maxHeartbeats 0\nset_option maxRecDepth 100000\n'
  s+='noncomputable def basisList : List Exponent := ['+', '.join('⟨'+', '.join(str(v) for v in e+[0])+'⟩' for e in m['basis'])+']\n'
  s+=f'noncomputable def basis : Fin {g}.data.size → Exponent := fun i => basisList.getD i.val ⟨0,0,0,0,0,0,0,0⟩\n'
  for name,field in [('gram','gram_integer_poly'),('multiplier','multiplier_integer_poly'),('weighted','weighted_integer_poly')]:
   values=b[field];names=[]
   for i in range(0,len(values),64):
    nm=f'{name}_{i//64}';names.append(nm);s+=f'noncomputable def {nm} : Polynomial := [\n  '+',\n  '.join(term(t) for t in values[i:i+64])+']\n'
   s+=f'noncomputable def {name} : Polynomial := '+(' ++ '.join(names) if names else '[]')+'\n'
  s+=f'noncomputable def weight : ℤ := {b["scale_multiplier"]}\nend {ns}\n';write_if_changed(OUT/f'{tag}Data.lean',s)
  p=f'import Certificate.SOS.{tag}Data\nnamespace {ns}\nopen Certificate.Sparse\nset_option maxHeartbeats 0\nset_option maxRecDepth 100000\nset_option Elab.async false\n'
  p+=f'''theorem basis_shape : basisList.length = {g}.data.size := by decide +kernel
theorem den_positive : 0 < {g}.data.den := by decide +kernel
theorem weight_nonnegative : 0 ≤ weight := by decide +kernel

theorem gram_check : checkEqual (gramPolynomial {g}.data basis) gram = true := by
  decide +kernel

theorem weighted_check : checkEqual (mulFast gram multiplier) weighted = true := by
  decide +kernel

/-- The polynomial expansion is connected to the actual Gram matrix.
The matrix PSD proof and primitive-constraint nonnegativity are explicit inputs here. -/
theorem weighted_nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hPSD : (realGram {g}.data.A {g}.data.B {g}.data.den).PosSemidef)
    (hq : 0 ≤ eval x multiplier) : 0 ≤ eval x (scale weight weighted) := by
  have hg := eval_gramPolynomial_nonneg x hx {g}.data basis den_positive hPSD
  have eg := eq_of_check x _ _ gram_check
  rw [eg] at hg
  have ew := eq_of_check x _ _ weighted_check
  have hw : 0 ≤ eval x weighted := by
    rw [← ew,eval_mulFast]
    exact mul_nonneg hg hq
  have hweight : (0 : ℝ) ≤ weight := by exact_mod_cast weight_nonnegative
  simpa only [eval_scale] using mul_nonneg hweight hw

#print axioms weighted_nonnegative
end {ns}
'''
  # Ordinary blocks benefit from sparse merging; the three large correction
  # blocks use independently checked row/merge witnesses. Preserve H2 proofs.
  auxiliary=[]
  if ident.startswith('H1'):
   p=p.replace(f'import Certificate.SOS.{tag}Data\n',f'import Certificate.SOS.{tag}Data\nimport Certificate.ShortMultiplication\n')
   if b['index']>0:
    p=p.replace('import Certificate.ShortMultiplication','import Certificate.ShortMultiplication\nimport Certificate.SparseExpansion')
    p=p.replace('gramPolynomial ', 'sparseGramPolynomial ').replace('eval_gramPolynomial_nonneg','eval_sparseGramPolynomial_nonneg')
   else:
    subprocess.run([sys.executable,str(ROOT/'scripts/emit_chunked_sos.py'),'--identity',ident,'--block','0','--checks-per-module','128'],check=True,cwd=ROOT,stdout=subprocess.DEVNULL)
    manifest=json.loads((ROOT/f'Certificate/Chunked/{tag}/manifest.json').read_text())
    auxiliary=[entry['module'] for entry in manifest['sources']]
    p=p.replace('import Certificate.ShortMultiplication',f'import Certificate.ShortMultiplication\nimport Certificate.Chunked.{tag}.Proof')
    gram_check=f'theorem gram_check : checkEqual (gramPolynomial {g}.data basis) gram = true := by\n  decide +kernel\n\n'
    assert gram_check in p
    p=p.replace(gram_check,'')
    before=f'  have hg := eval_gramPolynomial_nonneg x hx {g}.data basis den_positive hPSD\n  have eg := eq_of_check x _ _ gram_check\n  rw [eg] at hg\n'
    assert before in p
    p=p.replace(before,f'  have hg := Certificate.Chunked.{tag}.gram_nonnegative x hx den_positive hPSD\n')
   p=p.replace('checkEqual','checkEqualMerged').replace('eq_of_check','eq_of_checkMerged')
   p=p.replace('mulFast','mulShort')
  write_if_changed(OUT/f'{tag}Proof.lean',p)
  job=dict(identity=ident,block=b['index'],matrix_data=f'Certificate.Generated.{tag}Data',data=f'Certificate.SOS.{tag}Data',proof=f'Certificate.SOS.{tag}Proof')
  if auxiliary:job['auxiliary']=auxiliary
  jobs.append(job)
write_if_changed(OUT/'manifest.json',json.dumps(jobs,indent=2)+'\n')
print('Generated',len(jobs),'Gram-polynomial checks')
