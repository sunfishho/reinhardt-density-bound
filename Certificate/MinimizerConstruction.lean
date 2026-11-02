import Certificate.NormalizedMinimizer
import Certificate.RadialBoundaryRegularity

/-! A chosen, constructed ratio-minimizing disc and its normalized radial
boundary. Choice only selects an object from the existence theorem proved by
compactness; no minimizing-body hypothesis or geometric axiom is introduced.
The radial boundary is not yet the balanced frame boundary. -/
namespace Certificate.Packing
open Set Metric MeasureTheory
open scoped NNReal ENNReal

noncomputable def ratioMinimizingBody : Set E :=
  Classical.choose exists_reinhardt_normalized_minimizer

theorem ratioMinimizingBody_properties :
    IsSymmetricConvexDisc ratioMinimizingBody ∧
    criticalHexArea ratioMinimizingBody = ENNReal.ofReal (2*Real.sqrt 3) ∧
    HexAreaLowerBound ratioMinimizingBody (2*Real.sqrt 3) ∧
    (∀ L : Set E, IsSymmetricConvexDisc L → hexagonRatio ratioMinimizingBody ≤ hexagonRatio L) ∧
    (∀ L : Set E, IsSymmetricConvexDisc L → HexAreaLowerBound L (2*Real.sqrt 3) →
      (volume ratioMinimizingBody).toReal ≤ (volume L).toReal) :=
  Classical.choose_spec exists_reinhardt_normalized_minimizer

noncomputable def ratioMinimizingBoundary : E ≃ₜ E :=
  discRadialHomeomorph ratioMinimizingBody ratioMinimizingBody_properties.1

/-- This boundary is continuous and injective (a homeomorphism restricted to
the circle), is antipodal, covers the entire frontier, and is Lipschitz there. -/
theorem ratioMinimizingBoundary_properties :
    ratioMinimizingBoundary '' sphere 0 1 = frontier ratioMinimizingBody ∧
    (∀ u : E, ratioMinimizingBoundary (-u) = -ratioMinimizingBoundary u) ∧
    (∀ u ∈ sphere 0 1, ratioMinimizingBoundary u = (gauge ratioMinimizingBody u)⁻¹ • u) ∧
    (∃ C : ℝ≥0, LipschitzOnWith C ratioMinimizingBoundary (sphere 0 1)) :=
  ⟨discRadialHomeomorph_sphere ratioMinimizingBody_properties.1,
    discRadialHomeomorph_neg ratioMinimizingBody_properties.1,
    fun _ hu => discRadialHomeomorph_on_sphere ratioMinimizingBody_properties.1 hu,
    discRadialHomeomorph_lipschitz_sphere ratioMinimizingBody_properties.1⟩

#print axioms ratioMinimizingBody_properties
#print axioms ratioMinimizingBoundary_properties
end Certificate.Packing
