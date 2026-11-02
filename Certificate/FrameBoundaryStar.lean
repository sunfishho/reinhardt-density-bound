import Certificate.FrameBoundarySupport

/-! Strict star conditions in the interior follow from convex boundary
geometry and the two determinant constraints. Equality would force adjacent
boundary tangents to be parallel. -/
namespace Certificate.Packing
open MeasureTheory Set Filter Confinement HVGeometry
set_option maxHeartbeats 0

noncomputable def detLinear (v : E) : E →ₗ[ℝ] ℝ := v 0 • coord 1-v 1 • coord 0

@[simp] lemma detLinear_apply (v z : E) : detLinear v z = det2 v z := by
  simp [detLinear,det2]

theorem FrameBoundary.strict_tangent_contact {K : Set E} (hK : IsSymmetricConvexDisc K)
    {path : NormalizedTrajectory} (data : FrameBoundary path K)
    (i j : Fin 6) (hij : 0 < det2 (root i) (root j))
    (t : ℝ) (ht : t ∈ Ioo 0 path.duration) :
    0 < det2 (stateTangent (path.state t) (root i)) (root j-root i) := by
  have ht' : t ∈ Icc 0 path.duration := ⟨ht.1.le,ht.2.le⟩
  let p := stateAction (path.state t) (root i)
  let v := stateAction (path.state t) (stateTangent (path.state t) (root i))
  let w := stateAction (path.state t) (stateTangent (path.state t) (root j))
  let γ := fun s => stateAction (path.state s) (root j)
  have hn : 0 ≤ det2 v (γ t-p) := data.tangent_support hK i t ht' (γ t)
    (hK.2.1.isClosed.closure_eq ▸ frontier_subset_closure (data.boundary j t ht'))
  have heq : det2 v (γ t-p) = det2 (stateTangent (path.state t) (root i)) (root j-root i) := by
    dsimp [v,γ,p]
    rw [← stateAction_sub,det2_stateAction,(path.determinant t ht').1,one_mul]
  rw [← heq]
  by_contra h
  have he : det2 v (γ t-p) = 0 := le_antisymm (le_of_not_gt h) hn
  have hmin : IsLocalMin (fun s => det2 v (γ s-p)) t := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
    rw [he]
    exact data.tangent_support hK i t ht' (γ s)
      (hK.2.1.isClosed.closure_eq ▸ frontier_subset_closure (data.boundary j s ⟨hs.1.le,hs.2.le⟩))
  have hd : HasDerivAt (fun s => det2 v (γ s-p)) (det2 v w) t := by
    have hdγ : HasDerivAt γ w t := stateAction_hasDerivAt
      (normalized_group_derivative path t ht) (root j)
    have hh := (detLinear v).toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t (hdγ.sub_const p)
    convert! hh using 1
  have hzero := hmin.hasDerivAt_eq_zero hd
  have hpositive : 0 < det2 v w := by
    dsimp [v,w]
    rw [det2_stateAction,(path.determinant t ht').1,one_mul,
      stateTangent_det,(path.determinant t ht').2,one_mul]
    exact hij
  linarith

theorem FrameBoundary.star_pos_interior {K : Set E} (hK : IsSymmetricConvexDisc K)
    {path : NormalizedTrajectory} (data : FrameBoundary path K)
    (t : ℝ) (ht : t ∈ Ioo 0 path.duration) :
    0 < rho0 (path.state t) ∧ 0 < rho1 (path.state t) ∧ 0 < rho2 (path.state t) := by
  have hs : 0 < Real.sqrt (3:ℝ) := Real.sqrt_pos.2 (by norm_num)
  have h01 : 0 < det2 (root 0) (root 1) := by
    dsimp [root,s0,s1,pt,det2]; nlinarith
  have h12 : 0 < det2 (root 1) (root 2) := by
    dsimp [root,s1,s2,pt,det2]; nlinarith
  have h23 : 0 < det2 (root 2) (root 3) := by
    dsimp [root,s0,s2,pt,det2]; nlinarith
  have ha := data.strict_tangent_contact hK 0 1 h01 t ht
  have hb := data.strict_tangent_contact hK 1 2 h12 t ht
  have hc := data.strict_tangent_contact hK 2 3 h23 t ht
  obtain ⟨e0,e1,e2⟩ := adjacent_tangent_contacts (path.state t)
  change 0 < det2 (stateTangent (path.state t) s0) (s1-s0) at ha
  change 0 < det2 (stateTangent (path.state t) s1) (s2-s1) at hb
  change 0 < det2 (stateTangent (path.state t) s2) (-s0-s2) at hc
  rw [e0] at ha
  rw [e1] at hb
  rw [e2] at hc
  exact ⟨pos_of_mul_pos_right ha (by positivity),pos_of_mul_pos_right hb (by positivity),
    pos_of_mul_pos_right hc (by positivity)⟩

#print axioms FrameBoundary.strict_tangent_contact
#print axioms FrameBoundary.star_pos_interior
end Certificate.Packing
