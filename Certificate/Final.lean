import Certificate.ControlTheorem
import Certificate.Potential.ControlCoordinates
import Certificate.RegionSanity

namespace Certificate
open MeasureTheory Set Potential
open scoped BigOperators
set_option maxHeartbeats 0

/-- Exact hypotheses of the control-path theorem. In particular `region` is a
geometric confinement assumption, not a consequence supplied by the SOS proof.
The velocity is expressed using the original matrix ODE, not the potential. -/
structure AdmissibleTrajectory where
  state : ℝ → State
  control : ℝ → Fin 3 → ℝ
  duration : ℝ
  duration_nonneg : 0 ≤ duration
  coordinates_ac : ∀ i, AbsolutelyContinuousOnInterval
    (fun t => (state t).coordinates i) 0 duration
  cost_integrable : IntervalIntegrable (fun t => (state t).cost) volume 0 duration
  region : ∀ t ∈ Icc 0 duration, NewCertificate.OnRegion (state t)
  control_nonneg : ∀ t ∈ Icc 0 duration, ∀ k, 0 ≤ control t k
  control_sum : ∀ t ∈ Icc 0 duration, ∑ k, control t k = 1
  matrix_ode : ∀ᵐ t ∂volume.restrict (Icc 0 duration), ∀ i,
    HasDerivAt (fun s => (state s).coordinates i)
      (coordinateTangent ((state t).g * (state t).X)
        (controlField (state t) (control t)) i) t
  initial : state 0 = initialState (state 0)
  terminal : state duration = rotateState (state 0)

noncomputable def AdmissibleTrajectory.cost (path : AdmissibleTrajectory) : ℝ :=
  ∫ t in 0..path.duration, (path.state t).cost

/-- The specific degree-6 certificate, including all its matrix and polynomial
checks, bounds the cost of every path satisfying the displayed hypotheses. -/
theorem AdmissibleTrajectory.cost_lower_bound (path : AdmissibleTrajectory) :
    gamma ≤ path.cost := by
  apply certified_control_cost path.state path.control path.duration
    path.duration_nonneg path.coordinates_ac path.cost_integrable path.region
    path.control_nonneg path.control_sum ?_ path.initial path.terminal
  filter_upwards [path.matrix_ode, ae_restrict_mem measurableSet_Icc] with t hv ht
  have hr : 0 < controlDenominator (path.state t) (path.control t) :=
    weighted_denominator_pos (path.control t)
      (fun k => denominatorAt (path.state t) (vertex k)) (769 / 10000)
      (by norm_num) (path.control_nonneg t ht) (path.control_sum t ht)
      (region_denominator (path.state t) (path.region t ht).2)
  rw [controlDenominator_linear] at hr
  rw [controlTangent_coordinates _ _ (ne_of_gt hr)]
  exact hv

/-- Conditional density conclusion. The geometric reduction and existence of a
path in the certified region remain explicit inputs; neither is an added axiom. -/
theorem density_bound_of_admissible_trajectory (density : ℝ)
    (path : AdmissibleTrajectory)
    (geometric_reduction : path.cost / (2 * Real.sqrt 3) ≤ density) :
    (8950112 : ℝ) / 10000000 < density :=
  density_bound_from_control density path.cost path.cost_lower_bound geometric_reduction

/-- The algebraic domain of the certificate is nonempty. -/
theorem certificate_region_nonempty : ∃ x : State, NewCertificate.OnRegion x :=
  ⟨circleInitial, circleInitial_determinants, circleInitial_region⟩

#print axioms NewCertificate.differential
#print axioms NewCertificate.boundary
#print axioms certified_control_cost
#print axioms AdmissibleTrajectory.cost_lower_bound
#print axioms density_bound_of_admissible_trajectory
#print axioms certificate_region_nonempty
end Certificate
