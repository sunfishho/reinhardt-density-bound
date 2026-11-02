import Certificate.ConvexBoundarySupport
import Certificate.StateLinearFrame
import Certificate.TangentHexagonSides
import Certificate.NormalizedHexagon
import Mathlib.MeasureTheory.Measure.OpenPos

/-! Construction of the normalized enclosing hexagons directly from a convex
frame boundary. Contact and supporting-strip containment are conclusions. -/
namespace Certificate.Packing
open MeasureTheory Set Confinement HVGeometry
set_option maxHeartbeats 0

theorem FrameBoundary.duration_pos {K : Set E} (hK : IsSymmetricConvexDisc K)
    {path : NormalizedTrajectory} (data : FrameBoundary path K) : 0 < path.duration := by
  have hp : 0 < (volume K).toReal := ENNReal.toReal_pos
    (Measure.measure_pos_of_nonempty_interior volume hK.2.2.1).ne' hK.2.1.measure_lt_top.ne
  by_contra h
  have ht : path.duration = 0 := le_antisymm (le_of_not_gt h) path.duration_nonneg
  have he := data.cost_eq_area hK
  simp only [NormalizedTrajectory.cost,ht,intervalIntegral.integral_same] at he
  linarith

lemma normalized_support_continuous (path : NormalizedTrajectory) (v z : E) :
    ContinuousOn (fun t => det2 (stateAction (path.state t) (stateTangent (path.state t) v))
      (z-stateAction (path.state t) v)) (Icc 0 path.duration) := by
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
  dsimp [det2,stateAction,stateTangent,point]
  fun_prop

theorem FrameBoundary.tangent_support {K : Set E} (hK : IsSymmetricConvexDisc K)
    {path : NormalizedTrajectory} (data : FrameBoundary path K) :
    ∀ i : Fin 6, ∀ t ∈ Icc 0 path.duration, ∀ z ∈ K,
      0 ≤ det2 (stateAction (path.state t) (stateTangent (path.state t) (root i)))
        (z-stateAction (path.state t) (root i)) := by
  intro i t ht z hz
  have hclosure : closure (Ioo 0 path.duration) = Icc 0 path.duration :=
    closure_Ioo (data.duration_pos hK).ne
  apply le_on_closure (s:=Ioo 0 path.duration) (f:=fun _ => (0:ℝ))
    (g:=fun s => det2 (stateAction (path.state s) (stateTangent (path.state s) (root i)))
      (z-stateAction (path.state s) (root i))) (x:=t) _ continuousOn_const
    (by rw [hclosure]; exact normalized_support_continuous path (root i) z)
    (by rwa [hclosure])
  intro s hs
  have hs' : s ∈ Icc 0 path.duration := ⟨hs.1.le,hs.2.le⟩
  apply convex_boundary_tangent_support hK.1 hK.2.1.isClosed
    (symmetricConvexDisc_zero_interior hK) hs
    (fun r hr => data.boundary i r ⟨hr.1.le,hr.2.le⟩)
    (stateAction_hasDerivAt (normalized_group_derivative path s hs) (root i)) _ z hz
  rw [det2_stateAction,(path.determinant s hs').1,one_mul]
  obtain ⟨h0,h1,h2⟩ := path.star_nonneg s hs'
  exact root_area_integrands_pos_of_normalized _ (path.determinant s hs').2 h0 h1 h2 i

/-- The canonical inverse frame sends the body inside the three explicit
normalized strips. It is obtained from the state's matrix, not extra data. -/
theorem FrameBoundary.normalized_enclosure {K : Set E} (hK : IsSymmetricConvexDisc K)
    {path : NormalizedTrajectory} (data : FrameBoundary path K)
    (t : ℝ) (ht : t ∈ Icc 0 path.duration)
    (hstar : 0 < rho0 (path.state t) ∧ 0 < rho1 (path.state t) ∧ 0 < rho2 (path.state t)) :
    InHexagon ((stateFrame (path.state t) (path.determinant t ht).1).symm '' K)
      (rho0 (path.state t)) (rho1 (path.state t)) (rho2 (path.state t)) := by
  let L := stateFrame (path.state t) (path.determinant t ht).1
  obtain ⟨h0,h1,h2⟩ := hstar
  have hsupp : ∀ i : Fin 6, ∀ z ∈ L.symm '' K,
      0 ≤ det2 (stateTangent (path.state t) (root i)) (z-root i) := by
    intro i z hz
    have hzK : L z ∈ K := by
      obtain ⟨w,hw,rfl⟩ := hz
      simpa using hw
    have hh := data.tangent_support hK i t ht (L z) hzK
    change 0 ≤ det2 (stateAction (path.state t) (stateTangent (path.state t) (root i)))
      (stateAction (path.state t) z-stateAction (path.state t) (root i)) at hh
    rw [← stateAction_sub,det2_stateAction,(path.determinant t ht).1,one_mul] at hh
    exact hh
  exact inHexagon_of_tangent_support
    (symmetric_linear_image hK.2.2.2 (L.symm : E →ₗ[ℝ] E)) (path.state t) h0 h1 h2
    (hsupp 0) (hsupp 1) (hsupp 2)

#print axioms FrameBoundary.tangent_support
#print axioms FrameBoundary.normalized_enclosure
end Certificate.Packing
