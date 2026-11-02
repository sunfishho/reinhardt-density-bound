import Certificate.Potential.Data
import Certificate.Identities.H2Data
namespace Certificate.Potential.H2
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
noncomputable def scaleFactor : ℤ := 47498902319923200000000
theorem scale_positive : 0 < scaleFactor := by decide +kernel
/-- Exact differentiation/substitution of the stored potential, not an assumed target. -/
theorem semantic_check : checkEqual (scale scaleFactor boundaryTarget) Certificate.Identities.H2.target = true := by
  decide +kernel

theorem semantic_identity (x : Fin 8 → ℝ) :
    eval x Certificate.Identities.H2.target = (scaleFactor : ℝ)*eval x boundaryTarget := by
  have he := eq_of_check x _ _ semantic_check
  simpa only [eval_scale] using he.symm
#print axioms semantic_identity
end Certificate.Potential.H2
