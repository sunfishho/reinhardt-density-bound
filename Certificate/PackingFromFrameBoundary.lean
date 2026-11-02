import Certificate.FrameBoundarySupport
import Certificate.PackingFromBoundary
import Certificate.NormalizedHexagonArea

/-! The frame boundary now constructs the enclosing critical-hexagon family.
No supporting maps, contacts, or enclosing strips are supplied separately. -/
namespace Certificate.Packing
open MeasureTheory Set Confinement HVGeometry
set_option maxHeartbeats 0

noncomputable def FrameBoundary.criticalHexagons {K : Set E} (hK : IsSymmetricConvexDisc K)
    {path : NormalizedTrajectory} (data : FrameBoundary path K)
    (hstar : ∀ t ∈ Icc 0 path.duration,
      0 < rho0 (path.state t) ∧ 0 < rho1 (path.state t) ∧ 0 < rho2 (path.state t))
    (hmin : HexAreaLowerBound K (2*Real.sqrt 3)) : BoundaryCriticalHexagonFamily path K where
  toFrameBoundary := data
  frame t := if ht : t ∈ Icc 0 path.duration then
    (stateFrame (path.state t) (path.determinant t ht).1).symm else LinearEquiv.refl ℝ E
  frame_det := by
    intro t ht
    rw [dif_pos ht]
    exact inverse_stateFrame_det _ _
  star_pos := hstar
  enclosed := by
    intro t ht
    rw [dif_pos ht]
    exact data.normalized_enclosure hK t ht (hstar t ht)
  midpoint0 := by
    intro t ht
    rw [dif_pos ht]
    exact inverse_stateFrame_contact hK.2.1.isClosed _ _ s0 (data.boundary 0 t ht)
  midpoint1 := by
    intro t ht
    rw [dif_pos ht]
    exact inverse_stateFrame_contact hK.2.1.isClosed _ _ s1 (data.boundary 1 t ht)
  midpoint2 := by
    intro t ht
    rw [dif_pos ht]
    exact inverse_stateFrame_contact hK.2.1.isClosed _ _ s2 (data.boundary 2 t ht)
  minimum_area := hmin

theorem packing_density_bound_of_frame_boundary
    (K : Set E) (hK : IsSymmetricConvexDisc K) (path : NormalizedTrajectory)
    (data : FrameBoundary path K)
    (hstar : ∀ t ∈ Icc 0 path.duration,
      0 < rho0 (path.state t) ∧ 0 < rho1 (path.state t) ∧ 0 < rho2 (path.state t))
    (hmin : HexAreaLowerBound K (2*Real.sqrt 3)) :
    (8950112:ℝ)/10000000 < packingDensity K :=
  packing_density_bound_of_boundary_critical_hexagons K hK path (data.criticalHexagons hK hstar hmin)

theorem packing_density_bound_of_curvature_frame_boundary
    (K : Set E) (hK : IsSymmetricConvexDisc K) (path : CurvatureTrajectory)
    (data : FrameBoundary path.toNormalized K)
    (hstar : ∀ t ∈ Icc 0 path.duration,
      0 < rho0 (path.state t) ∧ 0 < rho1 (path.state t) ∧ 0 < rho2 (path.state t))
    (hmin : HexAreaLowerBound K (2*Real.sqrt 3)) :
    (8950112:ℝ)/10000000 < packingDensity K :=
  packing_density_bound_of_frame_boundary K hK path.toNormalized data hstar hmin

#print axioms FrameBoundary.criticalHexagons
#print axioms packing_density_bound_of_frame_boundary
#print axioms packing_density_bound_of_curvature_frame_boundary
end Certificate.Packing
