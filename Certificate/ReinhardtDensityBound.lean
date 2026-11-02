import Certificate.MinimizerFrameTrace
import Certificate.PackingFromConstructedMinimizer

/-! The unconditional improved Reinhardt lower bound for the original packing
density definition. Every geometric input is now constructed and proved;
only the stated symmetric convex disc hypothesis remains. -/
namespace Certificate.Packing
open Set

theorem reinhardt_density_lower_bound (K : Set E) (hK : IsSymmetricConvexDisc K) :
    (8950112 : ℝ)/10000000 < packingDensity K :=
  all_discs_packing_bound_of_minimizer_frame minimizerInitialInverseFrame
    (by rw [minimizerInitialInverseFrame_det,abs_one])
    minimizerFrameTrajectory minimizerFrameTrace K hK

theorem reinhardt_hexagon_ratio_lower_bound (K : Set E) (hK : IsSymmetricConvexDisc K) :
    (8950112 : ℝ)/10000000 < hexagonRatio K :=
  all_discs_ratio_bound_of_minimizer_frame minimizerInitialInverseFrame
    (by rw [minimizerInitialInverseFrame_det,abs_one])
    minimizerFrameTrajectory minimizerFrameTrace K hK

#print axioms reinhardt_density_lower_bound
#print axioms reinhardt_hexagon_ratio_lower_bound
end Certificate.Packing
