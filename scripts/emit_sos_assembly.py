#!/usr/bin/env python3
"""Join checked multiplier, matrix and expansion proofs; no new hypotheses for blocks."""
from pathlib import Path
import json
from emit_sum_tree import emit_sum_tree
ROOT=Path(__file__).resolve().parents[1]
OUT=ROOT/'Certificate/Assembly';OUT.mkdir(exist_ok=True)
def write_changed(path, text):
 if not path.exists() or path.read_text()!=text:path.write_text(text)
mult={m['name']:m for m in json.loads((ROOT/'data/multipliers.json').read_text())}
jobs=[]
bundles=[]
for ident in ['H1_0','H1_1','H1_2','H2']:
 data=json.loads((ROOT/f'data/polynomials/{ident}.json').read_text())
 tags=[]
 for b in data['blocks']:
  tag=f'{ident}B{b["index"]:03d}';tags.append(tag)
  m=mult[b['name']];assert m['polynomial']==b['multiplier_integer_poly']
  mns=f'Certificate.MultiplierProofs.M{m["index"]:03d}'
  s=f'''import Certificate.SOS.{tag}Proof
import Certificate.Generated.{tag}Proof
import Certificate.MultiplierCertificates
namespace Certificate.Assembly.{tag}
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem multiplier_identification : Certificate.SOS.{tag}.multiplier = {mns}.certificate.polynomial := by
  decide +kernel

/-- All new algebraic obligations are discharged; the remaining hypotheses describe the domain. -/
theorem nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x (scale Certificate.SOS.{tag}.weight Certificate.SOS.{tag}.weighted) := by
  have hroot : (x 7)^2=3 := by rw [hx]; exact Real.sq_sqrt (by norm_num)
  apply Certificate.SOS.{tag}.weighted_nonnegative x hx
    Certificate.Generated.{tag}.positive_semidefinite
  rw [multiplier_identification]
  exact {mns}.nonnegative x hroot hregion
#print axioms nonnegative
end Certificate.Assembly.{tag}
'''
  write_changed(OUT/f'{tag}.lean',s)
  jobs.append(dict(identity=ident,block=b['index'],module=f'Certificate.Assembly.{tag}'))
 s=''.join(f'import Certificate.SOS.{tag}Data\n' for tag in tags)
 s+=f'import Certificate.Identities.{ident}Data\nnamespace Certificate.Assembly.{ident}\nopen Certificate.Sparse\nset_option maxHeartbeats 0\nset_option maxRecDepth 100000\nset_option Elab.async false\n'
 s+='noncomputable def blocks : List Polynomial := [\n'+',\n'.join(f'  scale Certificate.SOS.{tag}.weight Certificate.SOS.{tag}.weighted' for tag in tags)+']\n'
 s+=f'''theorem sum_check : checkEqual (collapse 20 blocks) Certificate.Identities.{ident}.recordedSOS = true := by
  decide +kernel

theorem sum_identity (x : Fin 8 → ℝ) :
    eval x Certificate.Identities.{ident}.recordedSOS = (blocks.map (eval x)).sum := by
  have he := eq_of_check x _ _ sum_check
  simpa only [eval_collapse,evalMany_eq_sum_map] using he.symm
#print axioms sum_identity
end Certificate.Assembly.{ident}
'''
 if ident.startswith('H1_'):
  emit_sum_tree(ident,data,OUT)
 else:
  write_changed(OUT/f'{ident}Sum.lean',s)
 if ident.startswith('H1_'):
  bundle_modules=[]
  for start in range(0,len(tags),25):
   selected=tags[start:start+25]
   imports=set();bodies=[]
   for tag in selected:
    lines=(OUT/f'{tag}.lean').read_text().splitlines()
    imports.update(line for line in lines if line.startswith('import '))
    bodies.append('\n'.join(line for line in lines if not line.startswith('import ')))
   name=f'{ident}Blocks{start//25:03d}'
   write_changed(OUT/f'{name}.lean','\n'.join(sorted(imports))+'\n'+'\n'.join(bodies)+'\n')
   module=f'Certificate.Assembly.{name}'
   bundle_modules.append(module)
   bundles.append(dict(identity=ident,module=module,blocks=list(range(start,start+len(selected)))))
  s=''.join(f'import {mod}\n' for mod in bundle_modules)
 else:
  s=''.join(f'import Certificate.Assembly.{tag}\n' for tag in tags)
 s+=f'import Certificate.Assembly.{ident}Sum\nimport Certificate.Identities.{ident}Proof\nnamespace Certificate.Assembly.{ident}\nopen Certificate.Sparse\nset_option maxHeartbeats 0\n'
 s+=f'''theorem sos_nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x Certificate.Identities.{ident}.recordedSOS := by
  rw [sum_identity]
  have hp : ∀ p ∈ blocks, 0 ≤ eval x p := by
    intro p hp
    simp only [blocks,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with '''+' | '.join('rfl' for tag in tags)+'\n'
 s+=''.join(f'    · exact Certificate.Assembly.{tag}.nonnegative x hx hregion\n' for tag in tags)
 s+='  exact List.sum_nonneg (fun y hy => by\n    rcases List.mem_map.mp hy with ⟨p,hp,rfl⟩\n    exact hp p hp)\n' # fix below to avoid shadowing
 s=s.replace('rcases List.mem_map.mp hy with ⟨p,hp,rfl⟩\n    exact hp p hp','rcases List.mem_map.mp hy with ⟨p,hmem,rfl⟩\n    exact hp p hmem')
 s+=f'''
/-- The cleared target inequality on the exact determinant-one region. -/
theorem target_lower_bound (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hg : x 0*x 3-x 1*x 2=1) (hh : (x 6)^2-(x 4)^2-(x 5)^2=1)
    (hregion : Certificate.PrimitiveData.Region x) :
    eval x Certificate.Identities.{ident}.gamma ≤ eval x Certificate.Identities.{ident}.target := by
  have hgg : eval x Certificate.Identities.{ident}.gg = 0 := by
    norm_num [Certificate.Identities.{ident}.gg,Certificate.Identities.{ident}.gg_0,eval,Exponent.eval]
    nlinarith only [hg]
  have hgh : eval x Certificate.Identities.{ident}.gh = 0 := by
    norm_num [Certificate.Identities.{ident}.gh,Certificate.Identities.{ident}.gh_0,eval,Exponent.eval]
    nlinarith only [hh]
  have hgt : eval x Certificate.Identities.{ident}.gt = 0 := by
    norm_num [Certificate.Identities.{ident}.gt,Certificate.Identities.{ident}.gt_0,eval,Exponent.eval,hx,Real.sq_sqrt]
  rw [Certificate.Identities.{ident}.quotient_identity,hgg,hgh,hgt]
  have hs := sos_nonnegative x hx hregion
  linarith only [hs]
#print axioms sos_nonnegative
#print axioms target_lower_bound
end Certificate.Assembly.{ident}
'''
 write_changed(OUT/f'{ident}Proof.lean',s)
(OUT/'manifest.json').write_text(json.dumps(jobs,indent=2)+'\n')
(OUT/'block_bundles.json').write_text(json.dumps(bundles,indent=2)+'\n')
print(f'Generated {len(jobs)} block assemblies and four exact sum checks (not yet verified).')
