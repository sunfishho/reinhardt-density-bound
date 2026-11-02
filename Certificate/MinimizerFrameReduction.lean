import Certificate.MinimizerConstruction
import Certificate.PackingFromConvexFrame

/-! The global ratio comparison is now proved, conditional only on constructing
the special balanced frame for an area-preserving linear image of the chosen
minimizing body. The free coordinates avoid assuming its initial frame is fixed. This does not
silently identify the geometric hexagon ratio with the original packing density. -/
namespace Certificate.Packing
open Set MeasureTheory

theorem all_discs_ratio_bound_of_minimizer_frame
    (L : E ≃ₗ[ℝ] E) (hdet : |LinearMap.det (L : E →ₗ[ℝ] E)|=1)
    (path : FrameTrajectory) (data : FrameTrace path (L '' ratioMinimizingBody)) :
    ∀ L : Set E, IsSymmetricConvexDisc L → (8950112:ℝ)/10000000 < hexagonRatio L := by
  have hK := symmetricConvexDisc_linear_image ratioMinimizingBody_properties.1 L
  have hmin : HexAreaLowerBound (L '' ratioMinimizingBody) (2*Real.sqrt 3) := by
    have hh := ratioMinimizingBody_properties.2.2.1.linear_image L
    simpa only [hdet,one_mul] using hh
  have he : criticalHexArea (L '' ratioMinimizingBody) = ENNReal.ofReal (2*Real.sqrt 3) := by
    rw [criticalHexArea_linear_image,hdet,ENNReal.ofReal_one,one_mul,
      ratioMinimizingBody_properties.2.1]
  have hframe := data.toFrameBoundary hK
  have hcost := (data.toCurvature hK).toNormalized.cost_lower_bound
    (hframe.hasAreaEstimate_of_minimum hK hmin)
  rw [hframe.cost_eq_area hK] at hcost
  have hA : 0 < 2*Real.sqrt 3 := by positivity
  have hratio : (8950112:ℝ)/10000000 < hexagonRatio (L '' ratioMinimizingBody) := by
    unfold hexagonRatio
    rw [he,ENNReal.toReal_ofReal hA.le]
    exact certified_density_bound.trans_le (div_le_div_of_nonneg_right hcost hA.le)
  rw [hexagonRatio_linear_image] at hratio
  intro K hK
  exact hratio.trans_le (ratioMinimizingBody_properties.2.2.2.1 K hK)

#print axioms all_discs_ratio_bound_of_minimizer_frame
end Certificate.Packing
