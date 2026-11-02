import Certificate.FrameBoundaryStar
import Certificate.PackingFromFrameBoundary

/-! The final bound from a normalized convex frame boundary and hexagon-area
minimality. Strict star conditions and all supporting geometry are derived. -/
namespace Certificate.Packing
open MeasureTheory Set Confinement HVGeometry
set_option maxHeartbeats 0

theorem FrameBoundary.area_estimate_interior {K : Set E} (hK : IsSymmetricConvexDisc K)
    {path : NormalizedTrajectory} (data : FrameBoundary path K)
    (hmin : HexAreaLowerBound K (2*Real.sqrt 3)) (t : ℝ) (ht : t ∈ Ioo 0 path.duration) :
    areaScore (rho0 (path.state t)) (rho1 (path.state t)) (rho2 (path.state t)) ≤
      path.cost/(2*Real.sqrt 3) := by
  have ht' : t ∈ Icc 0 path.duration := ⟨ht.1.le,ht.2.le⟩
  let L := (stateFrame (path.state t) (path.determinant t ht').1).symm
  have hd : |LinearMap.det (L : E →ₗ[ℝ] E)|=1 := inverse_stateFrame_det _ _
  have hm : HexAreaLowerBound (L '' K) (2*Real.sqrt 3) := by
    have hh := hmin.linear_image L
    rwa [hd,one_mul] at hh
  obtain ⟨h0,h1,h2⟩ := data.star_pos_interior hK t ht
  have hh := hales_vajjha_area_bound (L '' K)
    (hK.2.1.image L.toContinuousLinearEquiv.continuous)
    (hK.1.linear_image (L : E →ₗ[ℝ] E))
    (symmetric_linear_image hK.2.2.2 (L : E →ₗ[ℝ] E))
    _ _ _ h0 h1 h2 (rho_e2 _ (path.determinant t ht').2)
    (data.normalized_enclosure hK t ht' ⟨h0,h1,h2⟩)
    (inverse_stateFrame_contact hK.2.1.isClosed _ _ s0 (data.boundary 0 t ht'))
    (inverse_stateFrame_contact hK.2.1.isClosed _ _ s1 (data.boundary 1 t ht'))
    (inverse_stateFrame_contact hK.2.1.isClosed _ _ s2 (data.boundary 2 t ht')) hm
  have hv : volume (L '' K) = volume K := by
    have hh := Measure.addHaar_image_linearMap volume (L : E →ₗ[ℝ] E) K
    rwa [hd,ENNReal.ofReal_one,one_mul] at hh
  rwa [hv,← data.cost_eq_area hK] at hh

/-- The scalar area estimate extends to endpoints by continuity. No strict
star or tangent differentiability at the two endpoints is required. -/
theorem FrameBoundary.hasAreaEstimate_of_minimum {K : Set E} (hK : IsSymmetricConvexDisc K)
    {path : NormalizedTrajectory} (data : FrameBoundary path K)
    (hmin : HexAreaLowerBound K (2*Real.sqrt 3)) : path.HasAreaEstimate := by
  have hc : ∀ i, ContinuousOn (fun t => (path.state t).coordinates i) (Icc 0 path.duration) := by
    intro i
    simpa only [uIcc_of_le path.duration_nonneg] using (path.coordinates_ac i).continuousOn
  have ca : ContinuousOn (fun t => (path.state t).a) (Icc 0 path.duration) := by
    simpa [State.coordinates] using hc 4
  have cp : ContinuousOn (fun t => (path.state t).p) (Icc 0 path.duration) := by
    simpa [State.coordinates] using hc 5
  have ch : ContinuousOn (fun t => (path.state t).h) (Icc 0 path.duration) := by
    simpa [State.coordinates] using hc 6
  have hcont : ContinuousOn (fun t => areaScore (rho0 (path.state t))
      (rho1 (path.state t)) (rho2 (path.state t))) (Icc 0 path.duration) := by
    dsimp [areaScore,areaTerm,rho0,rho1,rho2]
    fun_prop
  have hclosure : closure (Ioo 0 path.duration) = Icc 0 path.duration :=
    closure_Ioo (data.duration_pos hK).ne
  intro t ht
  exact le_on_closure
    (f:=fun s => areaScore (rho0 (path.state s)) (rho1 (path.state s)) (rho2 (path.state s)))
    (g:=fun _ => path.cost/(2*Real.sqrt 3)) (x:=t) (data.area_estimate_interior hK hmin)
    (by rwa [hclosure]) continuousOn_const (by rwa [hclosure])

theorem packing_density_bound_of_normalized_convex_boundary
    (K : Set E) (hK : IsSymmetricConvexDisc K) (path : NormalizedTrajectory)
    (data : FrameBoundary path K) (hmin : HexAreaLowerBound K (2*Real.sqrt 3)) :
    (8950112:ℝ)/10000000 < packingDensity K := by
  apply density_bound_from_control (packingDensity K) path.cost
    (path.cost_lower_bound (data.hasAreaEstimate_of_minimum hK hmin))
  rw [data.cost_eq_area hK]
  have hT := data.duration_pos hK
  have ht : path.duration/2 ∈ Ioo 0 path.duration := ⟨by linarith,by linarith⟩
  have ht' : path.duration/2 ∈ Icc 0 path.duration := ⟨ht.1.le,ht.2.le⟩
  obtain ⟨h0,h1,h2⟩ := data.star_pos_interior hK _ ht
  exact packingDensity_ge_area_of_normalized_frame K hK
    (stateFrame (path.state (path.duration/2)) (path.determinant _ ht').1).symm
    (inverse_stateFrame_det _ _) _ _ _ h0 h1 h2
    (rho_e2 _ (path.determinant _ ht').2)
    (data.normalized_enclosure hK _ ht' ⟨h0,h1,h2⟩)

/-- The strongest current theorem: controls, strict interior stars, supporting
hexagons, area identity, area estimate, and packing comparison are all derived. -/
theorem packing_density_bound_of_curvature_convex_boundary
    (K : Set E) (hK : IsSymmetricConvexDisc K) (path : CurvatureTrajectory)
    (data : FrameBoundary path.toNormalized K)
    (hmin : HexAreaLowerBound K (2*Real.sqrt 3)) :
    (8950112:ℝ)/10000000 < packingDensity K :=
  packing_density_bound_of_normalized_convex_boundary K hK path.toNormalized data hmin

#print axioms FrameBoundary.hasAreaEstimate_of_minimum
#print axioms packing_density_bound_of_normalized_convex_boundary
#print axioms packing_density_bound_of_curvature_convex_boundary
end Certificate.Packing
