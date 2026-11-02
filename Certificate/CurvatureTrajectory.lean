import Certificate.AreaControlledTrajectory
import Certificate.CurvatureControl

/-! Constructing the control ODE from an AC frame path with nonnegative
curvature. The derivative of det X = 1 is derived almost everywhere. Neither
simplex controls nor the X-control equation are assumptions of this interface. -/
namespace Certificate
open MeasureTheory Set Filter Potential Confinement Curvature
open scoped BigOperators
set_option maxHeartbeats 0

noncomputable def stateDa (x : ℝ → State) (t : ℝ) := deriv (fun s => (x s).a) t
noncomputable def stateDp (x : ℝ → State) (t : ℝ) := deriv (fun s => (x s).p) t
noncomputable def stateDh (x : ℝ → State) (t : ℝ) := deriv (fun s => (x s).h) t

structure CurvatureTrajectory where
  state : ℝ → State
  duration : ℝ
  duration_nonneg : 0 ≤ duration
  coordinates_ac : ∀ i, AbsolutelyContinuousOnInterval
    (fun t => (state t).coordinates i) 0 duration
  determinant : ∀ t ∈ Icc 0 duration, (state t).determinantConstraints
  star_nonneg : ∀ t ∈ Icc 0 duration,
    0 ≤ rho0 (state t) ∧ 0 ≤ rho1 (state t) ∧ 0 ≤ rho2 (state t)
  group_ode : ∀ᵐ t ∂volume.restrict (Icc 0 duration), GroupDerivative state t
  curvature_nonneg : ∀ᵐ t ∂volume.restrict (Icc 0 duration), ∀ k,
    0 ≤ detPair ((state t).X.mulVec (direction k))
      ((tangent (stateDa state t) (stateDp state t) (stateDh state t)-1).mulVec (direction k))
  initial : state 0=initialState (state 0)
  terminal : state duration=rotateState (state 0)

namespace CurvatureTrajectory

theorem derivatives_ae (path : CurvatureTrajectory) :
    ∀ᵐ t ∂volume.restrict (Icc 0 path.duration),
      HasDerivAt (fun s => (path.state s).a) (stateDa path.state t) t ∧
      HasDerivAt (fun s => (path.state s).p) (stateDp path.state t) t ∧
      HasDerivAt (fun s => (path.state s).h) (stateDh path.state t) t := by
  rw [ae_restrict_iff' measurableSet_Icc]
  have ha : AbsolutelyContinuousOnInterval (fun s => (path.state s).a) 0 path.duration := by
    simpa [State.coordinates] using path.coordinates_ac 4
  have hp : AbsolutelyContinuousOnInterval (fun s => (path.state s).p) 0 path.duration := by
    simpa [State.coordinates] using path.coordinates_ac 5
  have hh : AbsolutelyContinuousOnInterval (fun s => (path.state s).h) 0 path.duration := by
    simpa [State.coordinates] using path.coordinates_ac 6
  filter_upwards [ha.ae_differentiableAt,hp.ae_differentiableAt,hh.ae_differentiableAt]
    with t hat hpt hht ht
  have ht' : t ∈ uIcc 0 path.duration := by rwa [uIcc_of_le path.duration_nonneg]
  exact ⟨(hat ht').hasDerivAt,(hpt ht').hasDerivAt,(hht ht').hasDerivAt⟩

/-- Tangency to the determinant-one surface follows from the actual derivatives. -/
theorem determinant_tangent_ae (path : CurvatureTrajectory) :
    ∀ᵐ t ∂volume.restrict (Icc 0 path.duration),
      (path.state t).h*stateDh path.state t-(path.state t).a*stateDa path.state t-
        (path.state t).p*stateDp path.state t=0 := by
  rw [ae_restrict_iff' measurableSet_Icc]
  filter_upwards [ae_imp_of_ae_restrict path.derivatives_ae,volume.ae_ne (0:ℝ),
    volume.ae_ne path.duration] with t ht h0 hT hmem
  obtain ⟨ha,hp,hh⟩ := ht hmem
  have hder := ((hh.pow 2).sub (ha.pow 2)).sub (hp.pow 2)
  have hconst : HasDerivAt
      (fun s => (path.state s).h^2-(path.state s).a^2-(path.state s).p^2) 0 t := by
    apply (hasDerivAt_const t (1:ℝ)).congr_of_eventuallyEq
    filter_upwards [Ioo_mem_nhds (lt_of_le_of_ne hmem.1 (Ne.symm h0))
      (lt_of_le_of_ne hmem.2 hT)] with s hs
    exact (path.determinant s ⟨hs.1.le,hs.2.le⟩).2
  have heq := hder.unique hconst
  norm_num only [Nat.reduceSub,pow_one,Nat.cast_ofNat] at heq
  nlinarith only [heq]

def PointControl (path : CurvatureTrajectory) (t : ℝ) (u : Fin 3 → ℝ) : Prop :=
  (∀ k, 0 ≤ u k) ∧ (∑ k, u k=1) ∧
    0 < denominatorAt (path.state t) u ∧
    controlField (path.state t) u=tangent (stateDa path.state t) (stateDp path.state t) (stateDh path.state t)

theorem pointControl_ae (path : CurvatureTrajectory) :
    ∀ᵐ t ∂volume.restrict (Icc 0 path.duration), ∃ u, path.PointControl t u := by
  filter_upwards [path.determinant_tangent_ae,path.curvature_nonneg,
    ae_restrict_mem measurableSet_Icc] with t ht hc hmem
  exact controls_of_nonnegative_curvature (path.state t) _ _ _
    (path.determinant t hmem).2 ht hc

/-- Choose a valid control where it exists, and a fixed simplex point elsewhere.
The exceptional set is null; the chosen controls satisfy simplex constraints everywhere. -/
noncomputable def control (path : CurvatureTrajectory) (t : ℝ) : Fin 3 → ℝ := by
  classical
  exact if h : ∃ u, path.PointControl t u then Classical.choose h else fun _ => 1/3

theorem control_nonneg (path : CurvatureTrajectory) (t : ℝ) : ∀ k, 0 ≤ path.control t k := by
  classical
  unfold control
  split_ifs with h
  · exact (Classical.choose_spec h).1
  · intro k; norm_num

theorem control_sum (path : CurvatureTrajectory) (t : ℝ) : ∑ k, path.control t k=1 := by
  classical
  unfold control
  split_ifs with h
  · exact (Classical.choose_spec h).2.1
  · norm_num [Fin.sum_univ_three]

theorem control_field_ae (path : CurvatureTrajectory) :
    ∀ᵐ t ∂volume.restrict (Icc 0 path.duration),
      controlField (path.state t) (path.control t)=
        tangent (stateDa path.state t) (stateDp path.state t) (stateDh path.state t) := by
  filter_upwards [path.pointControl_ae] with t ht
  classical
  simp only [control,dif_pos ht]
  exact (Classical.choose_spec ht).2.2.2

theorem matrix_ode (path : CurvatureTrajectory) :
    ∀ᵐ t ∂volume.restrict (Icc 0 path.duration), ∀ i,
      HasDerivAt (fun s => (path.state s).coordinates i)
        (coordinateTangent ((path.state t).g*(path.state t).X)
          (controlField (path.state t) (path.control t)) i) t := by
  filter_upwards [path.control_field_ae,path.derivatives_ae,path.group_ode] with t hc hx hg
  intro i
  rw [hc]
  fin_cases i
  · simpa [State.coordinates,coordinateTangent,State.g,State.X,Matrix.mul_apply,
      Fin.sum_univ_two] using hg.g11
  · simpa [State.coordinates,coordinateTangent,State.g,State.X,Matrix.mul_apply,
      Fin.sum_univ_two,sub_eq_add_neg] using hg.g12
  · simpa [State.coordinates,coordinateTangent,State.g,State.X,Matrix.mul_apply,
      Fin.sum_univ_two] using hg.g21
  · simpa [State.coordinates,coordinateTangent,State.g,State.X,Matrix.mul_apply,
      Fin.sum_univ_two,sub_eq_add_neg] using hg.g22
  · simpa [State.coordinates,coordinateTangent,tangent] using hx.1
  · convert! hx.2.1 using 1
    simp [coordinateTangent,tangent]
  · convert! hx.2.2 using 1
    simp [coordinateTangent,tangent]
  · simpa [State.coordinates,coordinateTangent] using hasDerivAt_const t (Real.sqrt (3:ℝ))

theorem cost_integrable (path : CurvatureTrajectory) :
    IntervalIntegrable (fun t => (path.state t).cost) volume 0 path.duration := by
  have hh : ContinuousOn (fun t => (path.state t).h) (uIcc 0 path.duration) := by
    simpa [State.coordinates] using (path.coordinates_ac 6).continuousOn
  exact (hh.const_mul 3).intervalIntegrable

noncomputable def toNormalized (path : CurvatureTrajectory) : NormalizedTrajectory where
  state := path.state
  control := path.control
  duration := path.duration
  duration_nonneg := path.duration_nonneg
  coordinates_ac := path.coordinates_ac
  cost_integrable := path.cost_integrable
  determinant := path.determinant
  star_nonneg := path.star_nonneg
  control_nonneg := fun t _ => path.control_nonneg t
  control_sum := fun t _ => path.control_sum t
  matrix_ode := path.matrix_ode
  initial := path.initial
  terminal := path.terminal

noncomputable def cost (path : CurvatureTrajectory) : ℝ := ∫ t in 0..path.duration, (path.state t).cost

theorem cost_lower_bound (path : CurvatureTrajectory)
    (ha : path.toNormalized.HasAreaEstimate) : gamma ≤ path.cost :=
  path.toNormalized.cost_lower_bound ha

#print axioms determinant_tangent_ae
#print axioms matrix_ode
#print axioms cost_lower_bound
end CurvatureTrajectory
end Certificate
