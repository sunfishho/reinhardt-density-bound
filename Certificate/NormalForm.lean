import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.Real.Sqrt

namespace Certificate

/-- The two polynomial reductions used by the certificate preserve evaluation
on the determinant-one state variety. No completeness theorem is required. -/
theorem determinant_g_rewrite (g11 g12 g21 g22 : ℝ)
    (hdet : g11 * g22 - g12 * g21 = 1) : g11 * g22 = 1 + g12 * g21 := by
  linarith only [hdet]

theorem determinant_X_rewrite (a p h : ℝ)
    (hdet : h^2 - a^2 - p^2 = 1) : h^2 = 1 + a^2 + p^2 := by
  linarith only [hdet]

theorem sqrt3_rewrite : Real.sqrt (3 : ℝ)^2 = 3 := Real.sq_sqrt (by norm_num)

/-- Soundness of replacing an occurrence of `g11*g22` inside a monomial. -/
theorem g_monomial_rewrite (g11 g12 g21 g22 rest : ℝ)
    (hdet : g11 * g22 - g12 * g21 = 1) :
    rest * (g11 * g22) = rest + rest * (g12 * g21) := by
  rw [determinant_g_rewrite _ _ _ _ hdet]
  ring

/-- Soundness of replacing an occurrence of `h^2` inside a monomial. -/
theorem X_monomial_rewrite (a p h rest : ℝ)
    (hdet : h^2 - a^2 - p^2 = 1) :
    rest * h^2 = rest + rest * a^2 + rest * p^2 := by
  rw [determinant_X_rewrite _ _ _ hdet]
  ring

end Certificate
