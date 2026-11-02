import Certificate.NumericBound
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

namespace Certificate
open MeasureTheory Set
open scoped BigOperators

/-- A simplex-weighted denominator retains a common positive lower bound. -/
theorem weighted_denominator_pos {ι : Type*} [Fintype ι]
    (u r : ι → ℝ) (δ : ℝ) (hδ : 0 < δ) (hu : ∀ i, 0 ≤ u i)
    (hsum : ∑ i, u i = 1) (hr : ∀ i, δ ≤ r i) :
    0 < ∑ i, u i * r i := by
  have h := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => mul_le_mul_of_nonneg_left (hr i) (hu i))
  have heq : ∑ i, u i * δ = δ := by rw [← Finset.sum_mul, hsum, one_mul]
  rw [heq] at h
  exact hδ.trans_le h

/-- The cleared vertex inequalities use `r = -tr(XZ)`. Their convex combination
bounds the derivative for the original, uncleared control vector field. -/
theorem cleared_vertex_inequalities {ι : Type*} [Fintype ι]
    (u r dX : ι → ℝ) (cost dG : ℝ)
    (hu : ∀ i, 0 ≤ u i) (hR : 0 < ∑ i, u i * r i)
    (hvertex : ∀ i, 0 ≤ r i * (cost - dG) - dX i) :
    dG + (∑ i, u i * dX i) / (∑ i, u i * r i) ≤ cost := by
  have h := Finset.sum_nonneg (s := Finset.univ)
    (fun i _ => mul_nonneg (hu i) (hvertex i))
  have heq : (∑ i, u i * (r i * (cost - dG) - dX i)) =
      (∑ i, u i * r i) * (cost - dG) - ∑ i, u i * dX i := by
    simp only [mul_sub, ← mul_assoc, Finset.sum_sub_distrib, Finset.sum_mul]
  rw [heq] at h
  have hdiv : (∑ i, u i * dX i) / (∑ i, u i * r i) ≤ cost - dG := by
    apply (div_le_iff₀ hR).mpr
    nlinarith only [h]
  linarith only [hdiv]

/-- Integration of a certificate along an absolutely continuous trajectory.
`potential` is the certificate evaluated along that trajectory. -/
theorem control_cost_lower_bound (potential cost : ℝ → ℝ) (a b bound : ℝ)
    (hab : a ≤ b) (hAC : AbsolutelyContinuousOnInterval potential a b)
    (hcost : IntervalIntegrable cost volume a b)
    (hderiv : deriv potential ≤ᵐ[volume.restrict (Icc a b)] cost)
    (hboundary : bound ≤ potential b - potential a) :
    bound ≤ ∫ t in a..b, cost t := by
  calc
    bound ≤ potential b - potential a := hboundary
    _ = ∫ t in a..b, deriv potential t := hAC.integral_deriv_eq_sub.symm
    _ ≤ ∫ t in a..b, cost t :=
      intervalIntegral.integral_mono_ae_restrict hab hAC.intervalIntegrable_deriv hcost hderiv

/-- The numerical conclusion once the published geometric reduction supplies
`density ≥ controlCost/(2√3)` and the new certificate supplies `controlCost ≥ gamma`. -/
theorem density_bound_from_control (density controlCost : ℝ)
    (hcost : gamma ≤ controlCost)
    (published_reduction : controlCost / (2 * Real.sqrt 3) ≤ density) :
    (8950112 : ℝ) / 10000000 < density := by
  have hden : 0 < 2 * Real.sqrt (3 : ℝ) := by positivity
  exact certified_density_bound.trans_le
    ((div_le_div_of_nonneg_right hcost hden.le).trans published_reduction)

#print axioms cleared_vertex_inequalities
#print axioms control_cost_lower_bound
#print axioms density_bound_from_control
end Certificate
