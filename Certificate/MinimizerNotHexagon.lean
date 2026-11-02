import Certificate.MinimizerIrreducibility
import Certificate.CriticalHexagonAttainment
import Mathlib.Analysis.InnerProductSpace.Convex

/-! The ratio minimizer is not itself a hexagon. A strictly convex comparison
body has ratio strictly below one; no numerical circle-area formula is needed. -/
namespace Certificate.Packing
open Set MeasureTheory
set_option maxHeartbeats 0

theorem Hex.not_strictConvex (H : Hex) : ¬ StrictConvex ℝ H.set := by
  intro hs
  have ha : H.a ∈ H.set := H.fan_vertex_mem 0
  have hb : H.b ∈ H.set := H.fan_vertex_mem 1
  have hc : H.c ∈ H.set := H.fan_vertex_mem 2
  by_cases hab : H.a=H.b
  · have hbc : H.b ≠ H.c := by
      intro he
      have hh := H.ha₃
      rw [hab,he,H.hc₃] at hh
      norm_num at hh
    have hi := hs hb hc hbc (a:=(1/2:ℝ)) (b:=(1/2:ℝ))
      (by norm_num) (by norm_num) (by norm_num)
    have hh := (H.interior_set_subset hi).2.1
    norm_num [map_add,map_smul,H.hb₂,H.hc₂] at hh
  · have hi := hs ha hb hab (a:=(1/2:ℝ)) (b:=(1/2:ℝ))
      (by norm_num) (by norm_num) (by norm_num)
    have hh := (H.interior_set_subset hi).1
    norm_num [map_add,map_smul,H.ha₁,H.hb₁] at hh

theorem hexagonRatio_lt_one_of_strictConvex {K : Set E} (hK : IsSymmetricConvexDisc K)
    (hs : StrictConvex ℝ K) : hexagonRatio K < 1 := by
  obtain ⟨H,hH,he⟩ := criticalHexArea_attained K hK
  have hproper : K ⊂ H.set := by
    refine ⟨hH,?_⟩
    intro hh
    have heq := Subset.antisymm hH hh
    exact H.not_strictConvex (heq ▸ hs)
  have harea := disc_area_strict_mono H.isSymmetricConvexDisc hK hproper
  rw [he] at harea
  have hp : 0 < (criticalHexArea K).toReal :=
    ENNReal.toReal_pos (criticalHexArea_pos hK).ne' (criticalHexArea_finite hK)
  exact (div_lt_one hp).2 harea

theorem unitDisc_isSymmetricConvexDisc : IsSymmetricConvexDisc (Metric.closedBall (0:E) 1) := by
  refine ⟨convex_closedBall _ _,isCompact_closedBall _ _,?_,?_⟩
  · refine ⟨0,?_⟩
    rw [interior_closedBall _ (by norm_num : (1:ℝ) ≠ 0)]
    simp
  · intro x
    simp [Metric.mem_closedBall,dist_zero_right,norm_neg]

theorem ratioMinimizingBody_ratio_lt_one : hexagonRatio ratioMinimizingBody < 1 := by
  exact (ratioMinimizingBody_properties.2.2.2.1 _ unitDisc_isSymmetricConvexDisc).trans_lt
    (hexagonRatio_lt_one_of_strictConvex unitDisc_isSymmetricConvexDisc (strictConvex_closedBall ℝ _ _))

theorem Hex.hexagonRatio_eq_one (H : Hex) : hexagonRatio H.set=1 := by
  have he : criticalHexArea H.set=volume H.set :=
    le_antisymm (criticalHexArea_le H Subset.rfl) (volume_le_criticalHexArea H.set)
  have hp : 0 < (volume H.set).toReal :=
    ENNReal.toReal_pos (Measure.measure_pos_of_nonempty_interior volume H.isSymmetricConvexDisc.2.2.1).ne'
      H.isCompact_set.measure_lt_top.ne
  simp [hexagonRatio,he,hp.ne']

theorem ratioMinimizingBody_ne_hexagon (H : Hex) : ratioMinimizingBody ≠ H.set := by
  intro he
  have hh := ratioMinimizingBody_ratio_lt_one
  rw [he,H.hexagonRatio_eq_one] at hh
  exact lt_irrefl _ hh

#print axioms hexagonRatio_lt_one_of_strictConvex
#print axioms ratioMinimizingBody_ne_hexagon
end Certificate.Packing
