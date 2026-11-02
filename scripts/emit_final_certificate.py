#!/usr/bin/env python3
"""Emit final on-region inequalities; build only after every required audit passes."""
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
s='import Certificate.Potential.DifferentialSemantics\nimport Certificate.NumericBound\nimport Certificate.PrimitiveData\n'
for ident in ['H1_0','H1_1','H1_2','H2']:
 s+=f'import Certificate.Assembly.{ident}Proof\nimport Certificate.Potential.{ident}\n'
s+='''namespace Certificate.NewCertificate
open Certificate.Sparse Certificate.Potential
set_option maxHeartbeats 0

def OnRegion (x : State) : Prop :=
  x.determinantConstraints ∧ PrimitiveData.Region x.coordinates

'''
for k in range(3):
 ident=f'H1_{k}'
 s+=f'''theorem differential_{k} (x : State) (hx : OnRegion x) :
    0 ≤ denominatorAt x (vertex {k})*(x.cost-dG x)-dX x {k} := by
  have h := Assembly.{ident}.target_lower_bound x.coordinates (by rfl)
    hx.1.1 hx.1.2 hx.2
  have hz : eval x.coordinates Identities.{ident}.gamma = 0 := by
    norm_num [Identities.{ident}.gamma,eval]
  rw [hz,Potential.{ident}.semantic_identity] at h
  have hs : (0 : ℝ) < Potential.{ident}.scaleFactor := by
    exact_mod_cast Potential.{ident}.scale_positive
  have ht := (mul_nonneg_iff_of_pos_left hs).mp h
  have hselect : clearedTarget ({k} : Fin 3) = clearedTarget_{k} := by
    simp only [clearedTarget,Matrix.cons_val]
  have ht' : 0 ≤ eval x.coordinates (clearedTarget {k}) :=
    (congrArg (fun p : Polynomial => (0 : ℝ) ≤ eval x.coordinates p) hselect).mpr ht
  rw [clearedTarget_evaluation] at ht'
  have hd : (0 : ℝ) < 3*(Potential.denominator : ℝ) := by
    have hp : (0 : ℝ) < Potential.denominator := by exact_mod_cast denominator_pos
    exact mul_pos (by norm_num) hp
  exact (mul_nonneg_iff_of_pos_left hd).mp ht'

'''
s+='''theorem differential (x : State) (hx : OnRegion x) (k : Fin 3) :
    0 ≤ denominatorAt x (vertex k)*(x.cost-dG x)-dX x k := by
  fin_cases k
  · exact differential_0 x hx
  · exact differential_1 x hx
  · exact differential_2 x hx

theorem boundary_gamma (x : State) :
    eval x.coordinates Identities.H2.gamma =
      (Potential.H2.scaleFactor : ℝ)*16*(Potential.denominator : ℝ)*Certificate.gamma := by
  norm_num [Identities.H2.gamma,Identities.H2.gamma_0,eval,Exponent.eval,
    Potential.H2.scaleFactor,Potential.denominator,Certificate.gamma]
  <;> ring

/-- The exact boundary improvement for the supplied potential, on its stated region. -/
theorem boundary (x : State) (hx : OnRegion x) :
    Certificate.gamma ≤ stateValue (rotateState x)-stateValue (initialState x) := by
  have h := Assembly.H2.target_lower_bound x.coordinates (by rfl) hx.1.1 hx.1.2 hx.2
  rw [boundary_gamma,Potential.H2.semantic_identity,boundary_evaluation] at h
  have hs : (0 : ℝ) < Potential.H2.scaleFactor := by exact_mod_cast Potential.H2.scale_positive
  have hd : (0 : ℝ) < Potential.denominator := by exact_mod_cast denominator_pos
  have hp : (0 : ℝ) < (Potential.H2.scaleFactor : ℝ)*16*(Potential.denominator : ℝ) :=
    mul_pos (mul_pos hs (by norm_num)) hd
  have hgap : 0 ≤ ((Potential.H2.scaleFactor : ℝ)*16*(Potential.denominator : ℝ))*
      (stateValue (rotateState x)-stateValue (initialState x)-Certificate.gamma) := by
    nlinarith only [h]
  have hnonneg := (mul_nonneg_iff_of_pos_left hp).mp hgap
  linarith only [hnonneg]

#print axioms differential
#print axioms boundary
end Certificate.NewCertificate
'''
def write_changed(path,text):
 if not path.exists() or path.read_text()!=text:path.write_text(text)
prefix='namespace Certificate.NewCertificate\nopen Certificate.Sparse Certificate.Potential\nset_option maxHeartbeats 0\n'
suffix='end Certificate.NewCertificate\n'
definitions=s[s.index('def OnRegion'):s.index('theorem differential_0')]
write_changed(ROOT/'Certificate/NewCertificateDefinitions.lean',
 'import Certificate.Potential.DifferentialSemantics\nimport Certificate.NumericBound\nimport Certificate.PrimitiveData\n'+prefix+definitions+suffix)
for k in range(3):
 start=s.index(f'theorem differential_{k}')
 end=s.index(f'theorem differential_{k+1}') if k<2 else s.index('theorem differential (')
 write_changed(ROOT/f'Certificate/NewCertificateVertex{k}.lean',
  f'import Certificate.NewCertificateDefinitions\nimport Certificate.Assembly.H1_{k}Proof\nimport Certificate.Potential.H1_{k}\n'
  +prefix+s[start:end]+f'#print axioms differential_{k}\n'+suffix)
boundary=s[s.index('theorem boundary_gamma'):s.index('#print axioms differential')]
write_changed(ROOT/'Certificate/NewCertificateBoundary.lean',
 'import Certificate.NewCertificateDefinitions\nimport Certificate.Assembly.H2Proof\nimport Certificate.Potential.H2\n'
 +prefix+boundary+'#print axioms boundary\n'+suffix)
combined=s[s.index('theorem differential ('):s.index('theorem boundary_gamma')]
write_changed(ROOT/'Certificate/NewCertificate.lean',
 ''.join(f'import Certificate.NewCertificateVertex{k}\n' for k in range(3))
 +'import Certificate.NewCertificateBoundary\n'+prefix+combined
 +'#print axioms differential\n#print axioms boundary\n'+suffix)
print('Generated final on-region certificate theorem source; not yet verified.')
