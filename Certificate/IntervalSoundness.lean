import Certificate.MatrixPositivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace Certificate
open Matrix
open scoped ComplexOrder

/-- Integer endpoint bounds imply the corresponding real square-root enclosure. -/
theorem sqrt_three_enclosure (s l u : ℤ) (hs : 0 < s) (hl : 0 ≤ l)
    (hls : l*l ≤ 3*s*s) (hus : 3*s*s ≤ u*u) (hlu : l ≤ u) :
    (l : ℝ) ≤ (s : ℝ) * Real.sqrt 3 ∧ (s : ℝ) * Real.sqrt 3 ≤ (u : ℝ) := by
  have hr := Real.sqrt_nonneg (3 : ℝ)
  have hr2 : Real.sqrt (3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  have hl' : (0 : ℝ) ≤ l := by exact_mod_cast hl
  have hu' : (l : ℝ) ≤ u := by exact_mod_cast hlu
  have hls' : (l : ℝ)*(l : ℝ) ≤ 3*(s : ℝ)*(s : ℝ) := by exact_mod_cast hls
  have hus' : (3 : ℝ)*(s : ℝ)*(s : ℝ) ≤ (u : ℝ)*(u : ℝ) := by exact_mod_cast hus
  have hsq : ((s : ℝ) * Real.sqrt 3)^2 = 3 * (s : ℝ)^2 := by rw [mul_pow, hr2]; ring
  have hp := mul_nonneg hs'.le hr
  constructor
  · apply (sq_le_sq₀ hl' hp).mp
    nlinarith only [hls', hsq]
  · apply (sq_le_sq₀ hp (hl'.trans hu')).mp
    nlinarith only [hus', hsq]

/-- A linear expression in an enclosed real number lies between its endpoint values. -/
theorem linear_enclosure (a b l u r : ℝ) (hl : l ≤ r) (hu : r ≤ u) :
    a + min (b*l) (b*u) ≤ a + b*r ∧ a + b*r ≤ a + max (b*l) (b*u) := by
  by_cases hb : 0 ≤ b
  · have h1 := mul_le_mul_of_nonneg_left hl hb
    have h2 := mul_le_mul_of_nonneg_left hu hb
    constructor
    · exact add_le_add le_rfl (le_trans (min_le_left _ _) h1)
    · exact add_le_add le_rfl (le_trans h2 (le_max_right _ _))
  · have h1 := mul_le_mul_of_nonpos_left hl (le_of_not_ge hb)
    have h2 := mul_le_mul_of_nonpos_left hu (le_of_not_ge hb)
    constructor
    · exact add_le_add le_rfl (le_trans (min_le_right _ _) h2)
    · exact add_le_add le_rfl (le_trans h1 (le_max_left _ _))

/-- The endpoint radius safely bounds the absolute value of an enclosed entry. -/
theorem abs_le_endpoint_radius (x l u : ℝ) (hl : l ≤ x) (hu : x ≤ u) :
    |x| ≤ max |l| |u| := by
  rw [abs_le]
  constructor
  · have := neg_abs_le l
    have := le_max_left |l| |u|
    linarith
  · exact le_trans hu (le_trans (le_abs_self _) (le_max_right _ _))

/-- A Gram matrix plus a symmetric, diagonally dominant residual is positive semidefinite.
The scale `c` need only be nonnegative; the factor is a supplied witness. -/
theorem gram_plus_residual_posSemidef {n k : Type*} [Fintype n] [DecidableEq n]
    [Fintype k] (Q : Matrix n n ℝ) (L : Matrix n k ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hsym : (Q - c • (L * Lᴴ)).IsHermitian)
    (hrow : ∀ i, ∑ j ∈ Finset.univ.erase i, ‖(Q - c • (L * Lᴴ)) i j‖ ≤
      (Q - c • (L * Lᴴ)) i i) : Q.PosSemidef := by
  have hE := posSemidef_of_row_dominance _ hsym hrow
  have hG := (Matrix.posSemidef_self_mul_conjTranspose L).smul hc
  have h := hE.add hG
  simpa only [sub_add_cancel] using h

#print axioms sqrt_three_enclosure
#print axioms gram_plus_residual_posSemidef
end Certificate
