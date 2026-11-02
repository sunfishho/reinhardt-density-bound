import Certificate.NewCertificate
import Certificate.TrajectoryCost

namespace Certificate
open MeasureTheory Set
open scoped BigOperators
open Potential
set_option maxHeartbeats 0

/-- Certificate soundness for absolutely continuous admissible paths on the exact
region. Confinement in this region is an explicit geometric obligation. -/
theorem certified_control_cost (x : ℝ → State) (u : ℝ → Fin 3 → ℝ) (T : ℝ)
    (hT : 0 ≤ T)
    (hAC : ∀ i, AbsolutelyContinuousOnInterval (fun t => (x t).coordinates i) 0 T)
    (hcost : IntervalIntegrable (fun t => (x t).cost) volume 0 T)
    (hregion : ∀ t ∈ Icc 0 T, NewCertificate.OnRegion (x t))
    (hu : ∀ t ∈ Icc 0 T, ∀ k, 0 ≤ u t k)
    (hsum : ∀ t ∈ Icc 0 T, ∑ k, u t k = 1)
    (hvelocity : ∀ᵐ t ∂volume.restrict (Icc 0 T),
      ∀ i, HasDerivAt (fun s => (x s).coordinates i) (controlTangent (x t) (u t) i) t)
    (hstart : x 0 = initialState (x 0))
    (hend : x T = rotateState (x 0)) :
    gamma ≤ ∫ t in 0..T, (x t).cost := by
  have hb : gamma ≤ stateValue (x T)-stateValue (x 0) := by
    have h := NewCertificate.boundary (x 0) (hregion 0 (by simp [hT]))
    rw [hend]
    calc
      gamma ≤ stateValue (rotateState (x 0))-stateValue (initialState (x 0)) := h
      _ = stateValue (rotateState (x 0))-stateValue (x 0) := by rw [← hstart]
  exact control_cost_of_certificate_on_path x u T hT hAC hcost
    (fun t ht => (hregion t ht).2) hu hsum hvelocity
    (fun t ht => NewCertificate.differential (x t) (hregion t ht)) hb

#print axioms certified_control_cost
end Certificate
