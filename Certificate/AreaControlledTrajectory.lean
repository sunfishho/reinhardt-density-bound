import Certificate.ConfinementFinal
import Certificate.CompactExclusion

/-! A normalized control trajectory before imposing the compact domain.
The new exclusion argument derives compactness in the only case requiring
it. The geometric area estimate is stated explicitly as an input, rather
than silently assuming the published compact-domain theorem. -/
namespace Certificate
open MeasureTheory Set Potential Confinement
open scoped BigOperators
set_option maxHeartbeats 0

structure NormalizedTrajectory where
  state : ℝ → State
  control : ℝ → Fin 3 → ℝ
  duration : ℝ
  duration_nonneg : 0 ≤ duration
  coordinates_ac : ∀ i, AbsolutelyContinuousOnInterval
    (fun t => (state t).coordinates i) 0 duration
  cost_integrable : IntervalIntegrable (fun t => (state t).cost) volume 0 duration
  determinant : ∀ t ∈ Icc 0 duration, (state t).determinantConstraints
  star_nonneg : ∀ t ∈ Icc 0 duration,
    0 ≤ rho0 (state t) ∧ 0 ≤ rho1 (state t) ∧ 0 ≤ rho2 (state t)
  control_nonneg : ∀ t ∈ Icc 0 duration, ∀ k, 0 ≤ control t k
  control_sum : ∀ t ∈ Icc 0 duration, ∑ k, control t k = 1
  matrix_ode : ∀ᵐ t ∂volume.restrict (Icc 0 duration), ∀ i,
    HasDerivAt (fun s => (state s).coordinates i)
      (coordinateTangent ((state t).g*(state t).X)
        (controlField (state t) (control t)) i) t
  initial : state 0=initialState (state 0)
  terminal : state duration=rotateState (state 0)

noncomputable def NormalizedTrajectory.cost (path : NormalizedTrajectory) : ℝ :=
  ∫ t in 0..path.duration, (path.state t).cost

/-- The normalized pointwise area lower estimate from HV Theorem 5.0.6.
Its derivation from a balanced convex disc remains a geometric proof obligation. -/
def NormalizedTrajectory.HasAreaEstimate (path : NormalizedTrajectory) : Prop :=
  ∀ t ∈ Icc 0 path.duration,
    areaScore (rho0 (path.state t)) (rho1 (path.state t)) (rho2 (path.state t)) ≤
      path.cost/(2*Real.sqrt 3)

noncomputable def NormalizedTrajectory.toCompact (path : NormalizedTrajectory)
    (ha : path.HasAreaEstimate) (hc : path.cost/(2*Real.sqrt 3) < 269/300) :
    CompactTrajectory where
  state := path.state
  control := path.control
  duration := path.duration
  duration_nonneg := path.duration_nonneg
  coordinates_ac := path.coordinates_ac
  cost_integrable := path.cost_integrable
  determinant := path.determinant
  compact_domain := by
    intro t ht
    obtain ⟨h0,h1,h2⟩ := path.star_nonneg t ht
    exact compact_of_areaScore (path.state t) (path.determinant t ht).2
      h0 h1 h2 ((ha t ht).trans_lt hc)
  control_nonneg := path.control_nonneg
  control_sum := path.control_sum
  matrix_ode := path.matrix_ode
  initial := path.initial
  terminal := path.terminal

/-- Compact-domain membership is now a consequence, not a hypothesis.
Only the earlier geometric area estimate is required. -/
theorem NormalizedTrajectory.cost_lower_bound (path : NormalizedTrajectory)
    (ha : path.HasAreaEstimate) : gamma ≤ path.cost := by
  by_cases hc : path.cost/(2*Real.sqrt 3) < 269/300
  · exact (path.toCompact ha hc).cost_lower_bound
  · have hh := certified_density_lt_exclusion_threshold.le.trans (le_of_not_gt hc)
    exact (div_le_div_iff_of_pos_right (by positivity : 0 < 2*Real.sqrt (3:ℝ))).mp hh

#print axioms NormalizedTrajectory.cost_lower_bound
end Certificate
