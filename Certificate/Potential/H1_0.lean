import Certificate.Potential.Data
import Certificate.Identities.H1_0Data
namespace Certificate.Potential.H1_0
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
noncomputable def scaleFactor : ℤ := 253327479039590400000000
theorem scale_positive : 0 < scaleFactor := by decide +kernel
/-- Exact differentiation/substitution of the stored potential, not an assumed target. -/
theorem semantic_check : checkEqual (scale scaleFactor clearedTarget_0) Certificate.Identities.H1_0.target = true := by
  decide +kernel

theorem semantic_identity (x : Fin 8 → ℝ) :
    eval x Certificate.Identities.H1_0.target = (scaleFactor : ℝ)*eval x clearedTarget_0 := by
  have he := eq_of_check x _ _ semantic_check
  simpa only [eval_scale] using he.symm
#print axioms semantic_identity
end Certificate.Potential.H1_0
