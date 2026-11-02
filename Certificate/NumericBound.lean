import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace Certificate
/-- Exact constant from the degree-6 boundary certificate. -/
noncomputable def gamma : ℝ :=
  -(11322938895932849560433 : ℝ) / 1484340697497600000000 +
  (108969540019475 : ℝ) / 17592186044416 * Real.sqrt 3

/-- The displayed decimal is rounded down, not rounded to nearest. -/
theorem certified_density_bound : (8950112 : ℝ) / 10000000 < gamma / (2 * Real.sqrt 3) := by
  have hr : 0 < Real.sqrt (3 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hr2 : Real.sqrt (3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hlo : (1732050807568877 : ℝ) / 1000000000000000 ≤ Real.sqrt 3 := by
    nlinarith only [hr, hr2]
  apply (lt_div_iff₀ (mul_pos (by norm_num) hr)).mpr
  dsimp [gamma]
  nlinarith only [hlo]

#print axioms certified_density_bound
end Certificate
