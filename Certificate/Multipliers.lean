import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Real.Basic

namespace Certificate
/-- The 19 primitive inequalities in the supplied certificate, in the order used
by `targets_recomputed.json`. Their geometric validity is a separate dependency. -/
inductive ConstraintLabel where
  | sector1 | sector2 | sector1Rot1 | sector2Rot1 | sector1Rot2 | sector2Rot2
  | gNorm | denominator0 | denominator1 | denominator2 | hLower | hUpper | xNorm
  | horoballY | horoballPlus | horoballMinus | halfplane0 | halfplane1 | halfplane2
  deriving DecidableEq, Repr

abbrev Multiplier := List ConstraintLabel

noncomputable def multiplierValue (q : ConstraintLabel → ℝ) (m : Multiplier) : ℝ :=
  (m.map q).prod

/-- Every supplied multiplier is a finite product of primitive nonnegative constraints. -/
theorem multiplier_nonneg (q : ConstraintLabel → ℝ) (hq : ∀ label, 0 ≤ q label)
    (m : Multiplier) : 0 ≤ multiplierValue q m := by
  induction m with
  | nil => simp [multiplierValue]
  | cons a m ih =>
    simpa only [multiplierValue, List.map_cons, List.prod_cons] using mul_nonneg (hq a) ih

end Certificate
