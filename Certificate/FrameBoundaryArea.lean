import Certificate.BoundaryArcArea
import Certificate.FrameBoundaryCalculus

/-! HV Section 3.2: actual Lebesgue area equals control-trajectory cost when
the six frame arcs describe the convex boundary once. -/
namespace Certificate.Packing
open MeasureTheory Set Confinement HVGeometry
set_option maxHeartbeats 0

lemma symmetricConvexDisc_zero_interior {K : Set E} (hK : IsSymmetricConvexDisc K) :
    (0:E) ∈ interior K := by
  obtain ⟨x,hx⟩ := hK.2.2.1
  have hm : -x ∈ K := (hK.2.2.2 x).1 (interior_subset hx)
  have hh := hK.1.combo_interior_self_mem_interior hx hm
    (by norm_num : (0:ℝ) < 1/2) (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
  simpa using hh

/-- Geometric boundary coverage and nonoverlap. No area or cost equality is
a field. Derivatives follow from the trajectory's existing AC/ODE data. -/
structure FrameBoundary (path : NormalizedTrajectory) (K : Set E) : Prop where
  boundary : ∀ i : Fin 6, ∀ t ∈ Icc 0 path.duration,
    stateAction (path.state t) (root i) ∈ frontier K
  covers : ∀ p ∈ frontier K, ∃ i : Fin 6, ∃ t ∈ Icc 0 path.duration,
    stateAction (path.state t) (root i) = p
  simple : ∀ i j : Fin 6, ∀ s t, s ∈ Ioo 0 path.duration → t ∈ Ioo 0 path.duration →
    stateAction (path.state s) (root i) = stateAction (path.state t) (root j) →
      i = j ∧ s = t

theorem FrameBoundary.cost_eq_area {K : Set E} (hK : IsSymmetricConvexDisc K)
    {path : NormalizedTrajectory} (data : FrameBoundary path K) :
    path.cost = (volume K).toReal := by
  let γ := fun i : Fin 6 => fun t => stateAction (path.state t) (root i)
  let γ' := fun i : Fin 6 => fun t =>
    stateAction (path.state t) (stateTangent (path.state t) (root i))
  let f := fun i : Fin 6 => fun t => det2 (γ i t) (γ' i t)
  have harea := area_eq_sum_boundary_integrals hK.2.1 hK.1
    (mem_interior_iff_mem_nhds.1 (symmetricConvexDisc_zero_interior hK)) γ γ' path.duration
    data.boundary data.covers data.simple
    (fun i t ht => stateAction_hasDerivAt (normalized_group_derivative path t ht) (root i))
  have hc : ∀ i, ContinuousOn (fun t => (path.state t).coordinates i) (Icc 0 path.duration) := by
    intro i
    simpa only [uIcc_of_le path.duration_nonneg] using (path.coordinates_ac i).continuousOn
  have c11 : ContinuousOn (fun t => (path.state t).g11) (Icc 0 path.duration) := by
    simpa [State.coordinates] using hc 0
  have c12 : ContinuousOn (fun t => (path.state t).g12) (Icc 0 path.duration) := by
    simpa [State.coordinates] using hc 1
  have c21 : ContinuousOn (fun t => (path.state t).g21) (Icc 0 path.duration) := by
    simpa [State.coordinates] using hc 2
  have c22 : ContinuousOn (fun t => (path.state t).g22) (Icc 0 path.duration) := by
    simpa [State.coordinates] using hc 3
  have ca : ContinuousOn (fun t => (path.state t).a) (Icc 0 path.duration) := by
    simpa [State.coordinates] using hc 4
  have cp : ContinuousOn (fun t => (path.state t).p) (Icc 0 path.duration) := by
    simpa [State.coordinates] using hc 5
  have ch : ContinuousOn (fun t => (path.state t).h) (Icc 0 path.duration) := by
    simpa [State.coordinates] using hc 6
  have hfcont : ∀ i, ContinuousOn (f i) (Icc 0 path.duration) := by
    intro i
    dsimp [f,γ,γ',det2,stateAction,stateTangent,point]
    fun_prop
  have hfi : ∀ i, IntegrableOn (f i) (Ioo 0 path.duration) := fun i =>
    ((hfcont i).integrableOn_Icc).mono_set Ioo_subset_Icc_self
  have hnonneg : ∀ i t, t ∈ Ioo 0 path.duration → 0 ≤ f i t := by
    intro i t ht
    have ht' : t ∈ Icc 0 path.duration := ⟨ht.1.le,ht.2.le⟩
    dsimp [f,γ,γ']
    rw [det2_stateAction,(path.determinant t ht').1,one_mul]
    obtain ⟨h0,h1,h2⟩ := path.star_nonneg t ht'
    exact root_area_integrands_nonneg _ h0 h1 h2 i
  have heq : ∑ i, (1/2:ℝ) * (∫ t in Ioo 0 path.duration, |det2 (γ i t) (γ' i t)|) =
      ∑ i, (1/2:ℝ) * (∫ t in Ioo 0 path.duration, f i t) := by
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    exact setIntegral_congr_fun measurableSet_Ioo (fun t ht => abs_of_nonneg (hnonneg i t ht))
  rw [heq,← Finset.mul_sum,← integral_finsetSum _ (fun i _ => hfi i),← integral_const_mul] at harea
  have heq' : (∫ t in Ioo 0 path.duration, (1/2:ℝ) * ∑ i, f i t) = path.cost := by
    rw [NormalizedTrajectory.cost,intervalIntegral.integral_of_le path.duration_nonneg,
      integral_Ioc_eq_integral_Ioo]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro t ht
    exact frame_area_integrand_sum _ (path.determinant t ⟨ht.1.le,ht.2.le⟩).1
  exact (harea.trans heq').symm

#print axioms FrameBoundary.cost_eq_area
end Certificate.Packing
