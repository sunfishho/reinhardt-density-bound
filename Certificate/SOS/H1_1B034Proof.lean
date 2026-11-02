import Certificate.SOS.H1_1B034Data
import Certificate.ShortMultiplication
import Certificate.SparseExpansion
namespace Certificate.SOS.H1_1B034
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
theorem basis_shape : basisList.length = Certificate.Generated.H1_1B034.data.size := by decide +kernel
theorem den_positive : 0 < Certificate.Generated.H1_1B034.data.den := by decide +kernel
theorem weight_nonnegative : 0 ≤ weight := by decide +kernel

theorem gram_check : checkEqualMerged (sparseGramPolynomial Certificate.Generated.H1_1B034.data basis) gram = true := by
  decide +kernel

theorem weighted_check : checkEqualMerged (mulShort gram multiplier) weighted = true := by
  decide +kernel

/-- The polynomial expansion is connected to the actual Gram matrix.
The matrix PSD proof and primitive-constraint nonnegativity are explicit inputs here. -/
theorem weighted_nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hPSD : (realGram Certificate.Generated.H1_1B034.data.A Certificate.Generated.H1_1B034.data.B Certificate.Generated.H1_1B034.data.den).PosSemidef)
    (hq : 0 ≤ eval x multiplier) : 0 ≤ eval x (scale weight weighted) := by
  have hg := eval_sparseGramPolynomial_nonneg x hx Certificate.Generated.H1_1B034.data basis den_positive hPSD
  have eg := eq_of_checkMerged x _ _ gram_check
  rw [eg] at hg
  have ew := eq_of_checkMerged x _ _ weighted_check
  have hw : 0 ≤ eval x weighted := by
    rw [← ew,eval_mulShort]
    exact mul_nonneg hg hq
  have hweight : (0 : ℝ) ≤ weight := by exact_mod_cast weight_nonnegative
  simpa only [eval_scale] using mul_nonneg hweight hw

#print axioms weighted_nonnegative
end Certificate.SOS.H1_1B034
