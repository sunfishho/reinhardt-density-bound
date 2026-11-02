import Certificate.HexagonDegeneracy
import Certificate.SquareCornerCut
import Certificate.MinimizerNotHexagon
import Certificate.StrictHexagonBoundaryContacts

/-! Every critical hexagon of the constructed ratio minimizer has six genuine
sides and all six side midpoints belong to the body's boundary. -/
namespace Certificate.Packing
open Set MeasureTheory
set_option maxHeartbeats 0

theorem Hex.strict_of_minimum_of_proper (H : Hex) {K : Set E}
    (hK : IsSymmetricConvexDisc K) (hs : K ⊂ H.set)
    (hmin : ∀ G : Hex, K ⊆ G.set → volume H.set ≤ volume G.set) : H.Strict := by
  by_contra h
  obtain ⟨L,hL⟩ := H.exists_square_image_of_not_strict h
  have hp : L '' K ⊂ square := by
    rw [← hL]
    refine ⟨image_mono hs.1,?_⟩
    intro hh
    apply hs.2
    intro x hx
    obtain ⟨y,hy,he⟩ := hh (mem_image_of_mem L hx)
    exact L.injective he ▸ hy
  have hcrit : criticalHexArea K=volume H.set := by
    refine le_antisymm (criticalHexArea_le H hs.1) ?_
    exact le_iInf (fun G => le_iInf (fun hG => hmin G hG))
  have he : criticalHexArea (L '' K)=4 := by
    rw [criticalHexArea_linear_image,hcrit,← H.volume_map L,Hex.map_set,hL,volume_square]
  have hh := criticalHexArea_lt_four_of_proper_square (symmetricConvexDisc_linear_image hK L) hp
  rw [he] at hh
  exact lt_irrefl _ hh

theorem criticalHexagon_of_minimizer_strict (H : Hex)
    (hs : ratioMinimizingBody ⊆ H.set) (he : volume H.set=criticalHexArea ratioMinimizingBody) :
    H.Strict := by
  apply H.strict_of_minimum_of_proper ratioMinimizingBody_properties.1
    ⟨hs,fun hr => ratioMinimizingBody_ne_hexagon H (Subset.antisymm hs hr)⟩
  intro G hG
  rw [he]
  exact criticalHexArea_le G hG

theorem criticalHexagon_of_minimizer_midpoint_frontier (H : Hex)
    (hs : ratioMinimizingBody ⊆ H.set) (he : volume H.set=criticalHexArea ratioMinimizingBody)
    (i : Fin 6) : H.midpoint i ∈ frontier ratioMinimizingBody := by
  apply H.midpoint_frontier_of_strict_critical (criticalHexagon_of_minimizer_strict H hs he)
    ratioMinimizingBody_properties.1 hs
  intro G hG
  rw [he]
  exact criticalHexArea_le G hG

theorem ratioMinimizingHexagon_strict : ratioMinimizingHexagon.Strict := by
  apply criticalHexagon_of_minimizer_strict _ ratioMinimizingHexagon_properties.1
  rw [ratioMinimizingHexagon_properties.2.1,ratioMinimizingBody_properties.2.1]

theorem ratioMinimizingHexagon_all_midpoints_on_boundary (i : Fin 6) :
    ratioMinimizingHexagon.midpoint i ∈ frontier ratioMinimizingBody :=
  ratioMinimizingHexagon_midpoint_frontier ratioMinimizingHexagon_strict i

theorem initiallyNormalizedMinimizer_root_mem (i : Fin 6) :
    HVGeometry.root i ∈ initiallyNormalizedMinimizer := by
  refine ⟨ratioMinimizingHexagon.midpoint i,?_,ratioMinimizingHexagon.midpointFrame_all i⟩
  exact frontier_subset_iff_isClosed.2 ratioMinimizingBody_properties.1.2.1.isClosed
    (ratioMinimizingHexagon_all_midpoints_on_boundary i)

theorem initiallyNormalizedMinimizer_root_frontier (i : Fin 6) :
    HVGeometry.root i ∈ frontier initiallyNormalizedMinimizer := by
  have he := ratioMinimizingInitialFrame.toContinuousLinearEquiv.toHomeomorph.image_frontier
    ratioMinimizingBody
  change ratioMinimizingInitialFrame '' frontier ratioMinimizingBody =
    frontier (ratioMinimizingInitialFrame '' ratioMinimizingBody) at he
  rw [initiallyNormalizedMinimizer,← he]
  exact ⟨ratioMinimizingHexagon.midpoint i,ratioMinimizingHexagon_all_midpoints_on_boundary i,
    ratioMinimizingHexagon.midpointFrame_all i⟩

theorem initiallyNormalizedMinimizer_contains_regular_hexagon :
    convexHull ℝ (range HVGeometry.root) ⊆ initiallyNormalizedMinimizer := by
  apply convexHull_min _ initiallyNormalizedMinimizer_properties.1.1
  rintro x ⟨i,rfl⟩
  exact initiallyNormalizedMinimizer_root_mem i

#print axioms Hex.strict_of_minimum_of_proper
#print axioms criticalHexagon_of_minimizer_midpoint_frontier
#print axioms ratioMinimizingHexagon_all_midpoints_on_boundary
#print axioms initiallyNormalizedMinimizer_root_mem
#print axioms initiallyNormalizedMinimizer_root_frontier
#print axioms initiallyNormalizedMinimizer_contains_regular_hexagon
end Certificate.Packing
