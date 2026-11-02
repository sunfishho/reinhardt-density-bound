import Certificate.MinimizerFrameReduction
import Certificate.PackingFromHexagonInfimum

/-! The original universal packing-density conclusion now follows from a
balanced frame for an area-preserving image of the constructed minimizing body.
No density/hexagon comparison or minimizing-body existence remains an input. -/
namespace Certificate.Packing
open Set

theorem all_discs_packing_bound_of_minimizer_frame
    (L : E ≃ₗ[ℝ] E) (hdet : |LinearMap.det (L : E →ₗ[ℝ] E)|=1)
    (path : FrameTrajectory) (data : FrameTrace path (L '' ratioMinimizingBody)) :
    ∀ K : Set E, IsSymmetricConvexDisc K → (8950112:ℝ)/10000000 < packingDensity K := by
  intro K hK
  exact (all_discs_ratio_bound_of_minimizer_frame L hdet path data K hK).trans_le
    (hexagonRatio_le_packingDensity K hK)

#print axioms all_discs_packing_bound_of_minimizer_frame
end Certificate.Packing
