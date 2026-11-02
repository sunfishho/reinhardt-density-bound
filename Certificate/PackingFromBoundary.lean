import Certificate.FrameBoundaryArea
import Certificate.PackingFromCriticalHexagons

/-! Density bound from a geometric boundary presentation. The former
cost-equals-area assumption is now a theorem of that presentation. -/
namespace Certificate.Packing
open MeasureTheory Set Confinement HVGeometry

/-- The remaining geometry, with boundary coverage replacing the area identity.
Existence of this presentation for a minimizing disc is not asserted here. -/
structure BoundaryCriticalHexagonFamily (path : NormalizedTrajectory) (K : Set E)
    extends FrameBoundary path K where
  frame : ℝ → (E ≃ₗ[ℝ] E)
  frame_det : ∀ t ∈ Icc 0 path.duration,
    |LinearMap.det (frame t : E →ₗ[ℝ] E)| = 1
  star_pos : ∀ t ∈ Icc 0 path.duration,
    0 < rho0 (path.state t) ∧ 0 < rho1 (path.state t) ∧ 0 < rho2 (path.state t)
  enclosed : ∀ t ∈ Icc 0 path.duration,
    InHexagon (frame t '' K) (rho0 (path.state t)) (rho1 (path.state t)) (rho2 (path.state t))
  midpoint0 : ∀ t ∈ Icc 0 path.duration, s0 ∈ frame t '' K
  midpoint1 : ∀ t ∈ Icc 0 path.duration, s1 ∈ frame t '' K
  midpoint2 : ∀ t ∈ Icc 0 path.duration, s2 ∈ frame t '' K
  minimum_area : HexAreaLowerBound K (2*Real.sqrt 3)

noncomputable def BoundaryCriticalHexagonFamily.toCriticalHexagonFamily
    {K : Set E} (hK : IsSymmetricConvexDisc K) {path : NormalizedTrajectory}
    (data : BoundaryCriticalHexagonFamily path K) : CriticalHexagonFamily path K where
  frame := data.frame
  frame_det := data.frame_det
  star_pos := data.star_pos
  enclosed := data.enclosed
  midpoint0 := data.midpoint0
  midpoint1 := data.midpoint1
  midpoint2 := data.midpoint2
  minimum_area := data.minimum_area
  cost_eq_area := data.toFrameBoundary.cost_eq_area hK

/-- Both the HV area estimate and the area/cost identity are derived.
Only the boundary and critical-hexagon geometry remain as inputs. -/
theorem packing_density_bound_of_boundary_critical_hexagons
    (K : Set E) (hK : IsSymmetricConvexDisc K) (path : NormalizedTrajectory)
    (data : BoundaryCriticalHexagonFamily path K) :
    (8950112:ℝ)/10000000 < packingDensity K :=
  packing_density_bound_of_critical_hexagon_family K hK path
    (data.toCriticalHexagonFamily hK)

theorem packing_density_bound_of_curvature_boundary_critical_hexagons
    (K : Set E) (hK : IsSymmetricConvexDisc K) (path : CurvatureTrajectory)
    (data : BoundaryCriticalHexagonFamily path.toNormalized K) :
    (8950112:ℝ)/10000000 < packingDensity K :=
  packing_density_bound_of_boundary_critical_hexagons K hK path.toNormalized data

#print axioms packing_density_bound_of_boundary_critical_hexagons
#print axioms packing_density_bound_of_curvature_boundary_critical_hexagons
end Certificate.Packing
