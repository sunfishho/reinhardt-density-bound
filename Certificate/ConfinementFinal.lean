import Certificate.Final
import Certificate.ConfinementFromAC
import Certificate.ConfinementDomain

namespace Certificate
open MeasureTheory Set Potential Confinement
open scoped BigOperators
set_option maxHeartbeats 0

/-- Input from the published geometric reduction and compactness theorem.
The certificate's nineteen polynomial constraints are no longer assumptions:
the new deductions establishing them are proved in this project. -/
structure CompactTrajectory where
  state : ℝ → State
  control : ℝ → Fin 3 → ℝ
  duration : ℝ
  duration_nonneg : 0 ≤ duration
  coordinates_ac : ∀ i, AbsolutelyContinuousOnInterval
    (fun t => (state t).coordinates i) 0 duration
  cost_integrable : IntervalIntegrable (fun t => (state t).cost) volume 0 duration
  determinant : ∀ t ∈ Icc 0 duration, (state t).determinantConstraints
  compact_domain : ∀ t ∈ Icc 0 duration, HVCompact (state t)
  control_nonneg : ∀ t ∈ Icc 0 duration, ∀ k, 0 ≤ control t k
  control_sum : ∀ t ∈ Icc 0 duration, ∑ k, control t k = 1
  matrix_ode : ∀ᵐ t ∂volume.restrict (Icc 0 duration), ∀ i,
    HasDerivAt (fun s => (state s).coordinates i)
      (coordinateTangent ((state t).g*(state t).X)
        (controlField (state t) (control t)) i) t
  initial : state 0=initialState (state 0)
  terminal : state duration=rotateState (state 0)

noncomputable def CompactTrajectory.cost (path : CompactTrajectory) : ℝ :=
  ∫ t in 0..path.duration, (path.state t).cost

theorem gamma_lt_confinement_threshold : gamma < (311:ℝ)/100 := by
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)
  have hp := Real.sqrt_nonneg (3:ℝ)
  have hu : Real.sqrt (3:ℝ) ≤ 17321/10000 := by nlinarith
  dsimp [gamma]
  nlinarith only [hu]

theorem CompactTrajectory.group_derivative_ae (path : CompactTrajectory) :
    ∀ᵐ t ∂volume.restrict (Icc 0 path.duration), GroupDerivative path.state t := by
  filter_upwards [path.matrix_ode] with t ht
  constructor
  · simpa [State.coordinates,coordinateTangent,State.g,State.X,Matrix.mul_apply,
      Fin.sum_univ_two,sub_eq_add_neg] using ht 0
  · simpa [State.coordinates,coordinateTangent,State.g,State.X,Matrix.mul_apply,
      Fin.sum_univ_two,sub_eq_add_neg] using ht 1
  · simpa [State.coordinates,coordinateTangent,State.g,State.X,Matrix.mul_apply,
      Fin.sum_univ_two,sub_eq_add_neg] using ht 2
  · simpa [State.coordinates,coordinateTangent,State.g,State.X,Matrix.mul_apply,
      Fin.sum_univ_two,sub_eq_add_neg] using ht 3

/-- All nineteen certificate constraints, derived rather than assumed. Only
low-cost paths need this result; higher-cost paths already exceed gamma. -/
theorem CompactTrajectory.certificate_region (path : CompactTrajectory)
    (hcost : path.cost ≤ 311/100) :
    ∀ t ∈ Icc 0 path.duration, NewCertificate.OnRegion (path.state t) := by
  have hh : ∀ t ∈ Icc 0 path.duration, 0 ≤ (path.state t).h ∧ (path.state t).h ≤ 12/5 := by
    intro t ht
    have hh := height_bounds (path.state t) (path.determinant t ht).2 (path.compact_domain t ht)
    exact ⟨by linarith [hh.1],hh.2⟩
  have hg := group_bounds_of_ac path.state path.duration path.duration_nonneg
    path.coordinates_ac path.group_derivative_ae path.determinant hh path.initial path.terminal hcost
  intro t ht
  exact ⟨path.determinant t ht,
    region_of_hvCompact (path.state t) (path.determinant t ht).2 (path.compact_domain t ht) (hg t ht)⟩

noncomputable def CompactTrajectory.toAdmissible (path : CompactTrajectory)
    (hcost : path.cost ≤ 311/100) : AdmissibleTrajectory where
  state := path.state
  control := path.control
  duration := path.duration
  duration_nonneg := path.duration_nonneg
  coordinates_ac := path.coordinates_ac
  cost_integrable := path.cost_integrable
  region := path.certificate_region hcost
  control_nonneg := path.control_nonneg
  control_sum := path.control_sum
  matrix_ode := path.matrix_ode
  initial := path.initial
  terminal := path.terminal

/-- The completed new control theorem: no certificate-region hypothesis and
no upper cost bound are required in the conclusion. -/
theorem CompactTrajectory.cost_lower_bound (path : CompactTrajectory) : gamma ≤ path.cost := by
  by_cases hc : path.cost ≤ 311/100
  · exact (path.toAdmissible hc).cost_lower_bound
  · exact gamma_lt_confinement_threshold.le.trans (le_of_lt (lt_of_not_ge hc))

/-- The new density bound, conditional only on the stated published geometric
inputs (existence of a compact trajectory and its density comparison). -/
theorem density_bound_of_compact_trajectory (density : ℝ) (path : CompactTrajectory)
    (published_density_comparison : path.cost/(2*Real.sqrt 3) ≤ density) :
    (8950112:ℝ)/10000000 < density :=
  density_bound_from_control density path.cost path.cost_lower_bound published_density_comparison

#print axioms Confinement.height_bounds
#print axioms Confinement.state_bounds
#print axioms Confinement.energy_bound
#print axioms Confinement.row_polar_representation
#print axioms Confinement.row_sector
#print axioms Confinement.RegularPath.group_bounds
#print axioms Confinement.hasDerivAt_of_ac_continuous_rhs
#print axioms Confinement.cuspAndWall_chart_iff
#print axioms Confinement.hvCompact_iff_rotated
#print axioms CompactTrajectory.certificate_region
#print axioms CompactTrajectory.cost_lower_bound
#print axioms density_bound_of_compact_trajectory
end Certificate
