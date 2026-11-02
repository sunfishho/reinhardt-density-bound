import Certificate.CriticalHexagonAttainment
import Certificate.MinimizerIrreducibility

/-! An actual minimum-area enclosing hexagon for the constructed normalized
minimizer, with exact area and covolume. Midpoint contact and the smooth balanced
boundary are not asserted by the attainment theorem. -/
namespace Certificate.Packing
open Set MeasureTheory

noncomputable def ratioMinimizingHexagon : Hex :=
  Classical.choose (criticalHexArea_attained ratioMinimizingBody ratioMinimizingBody_properties.1)

theorem ratioMinimizingHexagon_properties :
    ratioMinimizingBody ⊆ ratioMinimizingHexagon.set ∧
    volume ratioMinimizingHexagon.set = ENNReal.ofReal (2*Real.sqrt 3) ∧
    |det2 ratioMinimizingHexagon.v ratioMinimizingHexagon.w| = 2*Real.sqrt 3 ∧
    (∀ H : Hex, ratioMinimizingBody ⊆ H.set → volume ratioMinimizingHexagon.set ≤ volume H.set) := by
  obtain ⟨hsub,he⟩ := Classical.choose_spec
    (criticalHexArea_attained ratioMinimizingBody ratioMinimizingBody_properties.1)
  change ratioMinimizingBody ⊆ ratioMinimizingHexagon.set at hsub
  change volume ratioMinimizingHexagon.set = criticalHexArea ratioMinimizingBody at he
  have hvol : volume ratioMinimizingHexagon.set = ENNReal.ofReal (2*Real.sqrt 3) :=
    he.trans ratioMinimizingBody_properties.2.1
  refine ⟨hsub,hvol,?_,fun H hH => he.le.trans (criticalHexArea_le H hH)⟩
  have hh := congrArg ENNReal.toReal hvol
  rw [ratioMinimizingHexagon.volume_eq_covolume,ENNReal.toReal_ofReal (abs_nonneg _),
    ENNReal.toReal_ofReal (by positivity)] at hh
  exact hh

#print axioms ratioMinimizingHexagon_properties
end Certificate.Packing
