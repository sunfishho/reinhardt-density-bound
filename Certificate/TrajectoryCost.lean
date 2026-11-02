import Certificate.Potential.RegionFacts
import Certificate.Potential.TrajectoryAlgebra
import Certificate.ControlCost

namespace Certificate
open MeasureTheory Set Potential
open scoped BigOperators
set_option maxHeartbeats 0

/-- Integrate the supplied potential along an admissible path. The two
certificate premises are instantiated by the actual SOS proofs in ControlTheorem. -/
theorem control_cost_of_certificate_on_path (x : ℝ → State) (u : ℝ → Fin 3 → ℝ)
    (T : ℝ) (hT : 0 ≤ T)
    (hAC : ∀ i, AbsolutelyContinuousOnInterval (fun t => (x t).coordinates i) 0 T)
    (hcost : IntervalIntegrable (fun t => (x t).cost) volume 0 T)
    (hregion : ∀ t ∈ Icc 0 T, PrimitiveData.Region (x t).coordinates)
    (hu : ∀ t ∈ Icc 0 T, ∀ k, 0 ≤ u t k)
    (hsum : ∀ t ∈ Icc 0 T, ∑ k, u t k = 1)
    (hvelocity : ∀ᵐ t ∂volume.restrict (Icc 0 T),
      ∀ i, HasDerivAt (fun s => (x s).coordinates i) (controlTangent (x t) (u t) i) t)
    (hvertex : ∀ t ∈ Icc 0 T, ∀ k,
      0 ≤ denominatorAt (x t) (vertex k) * ((x t).cost-dG (x t)) - dX (x t) k)
    (hboundary : gamma ≤ stateValue (x T)-stateValue (x 0)) :
    gamma ≤ ∫ t in 0..T, (x t).cost := by
  have hpotential := path_absolutelyContinuous (fun t => (x t).coordinates) 0 T hAC
  have hderiv : deriv (fun t => stateValue (x t)) ≤ᵐ[volume.restrict (Icc 0 T)]
      (fun t => (x t).cost) := by
    filter_upwards [hvelocity,ae_restrict_mem measurableSet_Icc] with t hv ht
    rw [(path_control_derivative x (u t) t hv).deriv]
    have hr : 0 < controlDenominator (x t) (u t) :=
      weighted_denominator_pos (u t) (fun k => denominatorAt (x t) (vertex k))
        (769/10000) (by norm_num) (hu t ht) (hsum t ht)
        (region_denominator (x t) (hregion t ht))
    exact cleared_vertex_inequalities (u t) (fun k => denominatorAt (x t) (vertex k))
      (dX (x t)) (x t).cost (dG (x t)) (hu t ht) hr (hvertex t ht)
  exact control_cost_lower_bound (fun t => stateValue (x t)) (fun t => (x t).cost)
    0 T gamma hT hpotential hcost hderiv hboundary

#print axioms control_cost_of_certificate_on_path
end Certificate
