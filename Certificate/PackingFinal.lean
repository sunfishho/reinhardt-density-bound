import Certificate.AreaControlledTrajectory
import Certificate.PackingGeometry
import Certificate.CurvatureTrajectory

/-! The checked certificate now concludes a theorem about the original packing
density definition. The remaining inputs describe the geometric reduction to
a balanced boundary trajectory and the HV geometric area estimate. No packing
density/cost comparison or compact-domain membership is assumed here. -/
namespace Certificate.Packing
open MeasureTheory Set

/-- Body-level result for a normalized balanced-disc presentation.
The hypotheses about the trajectory and its area estimate are explicit: this
is not yet an unconditional result for every centrally symmetric convex disc. -/
theorem packing_density_bound_of_geometric_data
    (K : Set E) (hK : IsSymmetricConvexDisc K)
    (path : NormalizedTrajectory) (ha : path.HasAreaEstimate)
    (harea : path.cost ≤ (volume K).toReal)
    (H : Hex) (hKH : K ⊆ H.set) (x : State)
    (hd : x.g11*x.g22-x.g12*x.g21=1)
    (h0 : (1/2:ℝ) • (H.a+H.b)=stateAction x circlePoint0)
    (h1 : (1/2:ℝ) • (H.b+H.c)=stateAction x circlePoint1) :
    (8950112:ℝ)/10000000 < packingDensity K := by
  apply density_bound_from_control (packingDensity K) path.cost (path.cost_lower_bound ha)
  exact (div_le_div_of_nonneg_right harea (by positivity)).trans
    (packingDensity_ge_normalized_area K hK H hKH x hd h0 h1)

/-- The same body-level bound with controls and the X-ODE reconstructed from
nonnegative curvature, rather than supplied as geometric inputs. -/
theorem packing_density_bound_of_curvature_data
    (K : Set E) (hK : IsSymmetricConvexDisc K)
    (path : CurvatureTrajectory) (ha : path.toNormalized.HasAreaEstimate)
    (harea : path.cost ≤ (volume K).toReal)
    (H : Hex) (hKH : K ⊆ H.set) (x : State)
    (hd : x.g11*x.g22-x.g12*x.g21=1)
    (h0 : (1/2:ℝ) • (H.a+H.b)=stateAction x circlePoint0)
    (h1 : (1/2:ℝ) • (H.b+H.c)=stateAction x circlePoint1) :
    (8950112:ℝ)/10000000 < packingDensity K :=
  packing_density_bound_of_geometric_data K hK path.toNormalized ha harea H hKH x hd h0 h1

#print axioms packing_density_bound_of_geometric_data
#print axioms packing_density_bound_of_curvature_data
end Certificate.Packing
