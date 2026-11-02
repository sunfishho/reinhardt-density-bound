import Certificate.HexagonMidpointContact
import Certificate.HexagonRelabeling
import Certificate.CriticalHexagonNormalization

/-! All six side midpoints of a nondegenerate minimum enclosing hexagon lie
on the body's boundary. The nondegeneracy hypothesis remains explicit. -/
namespace Certificate.Packing
open Set MeasureTheory
set_option maxHeartbeats 0

namespace Hex

theorem first_midpoint_mem_of_strict_critical (H : Hex) (hs : H.Strict)
    {K : Set E} (hK : IsSymmetricConvexDisc K) (hKH : K ⊆ H.set)
    (hmin : ∀ G : Hex, K ⊆ G.set → volume H.set ≤ volume G.set) :
    (1/2:ℝ) • (H.a+H.b) ∈ K := by
  rcases lt_or_gt_of_ne H.hdet with hd | hd
  · change det2 H.v H.w < 0 at hd
    have hsub : K ⊆ H.flip.set := by rwa [H.flip_set]
    have hm : ∀ G : Hex, K ⊆ G.set → volume H.flip.set ≤ volume G.set := by
      simpa only [H.flip_set] using hmin
    have hh := H.flip.first_midpoint_mem_of_strict_minimum (H.flip_strict hs)
      (by rw [H.flip_det]; linarith) hK hsub hm
    rwa [H.flip_first] at hh
  · exact H.first_midpoint_mem_of_strict_minimum hs hd hK hKH hmin

lemma midpoint_mem_of_strict_critical (H : Hex) (hs : H.Strict)
    {K : Set E} (hK : IsSymmetricConvexDisc K) (hKH : K ⊆ H.set)
    (hmin : ∀ G : Hex, K ⊆ G.set → volume H.set ≤ volume G.set) (i : Fin 6) :
    H.midpoint i ∈ K := by
  have h0 := H.first_midpoint_mem_of_strict_critical hs hK hKH hmin
  have hsub1 : K ⊆ H.rotate.set := by rwa [H.rotate_set]
  have hmin1 : ∀ G : Hex, K ⊆ G.set → volume H.rotate.set ≤ volume G.set := by
    simpa only [H.rotate_set] using hmin
  have h1 := H.rotate.first_midpoint_mem_of_strict_critical (H.rotate_strict hs) hK hsub1 hmin1
  have hsub2 : K ⊆ H.rotate.rotate.set := by rwa [rotate_set]
  have hmin2 : ∀ G : Hex, K ⊆ G.set → volume H.rotate.rotate.set ≤ volume G.set := by
    simpa only [rotate_set] using hmin
  have h2 := H.rotate.rotate.first_midpoint_mem_of_strict_critical
    (H.rotate.rotate_strict (H.rotate_strict hs)) hK hsub2 hmin2
  change (1/2:ℝ) • (H.b+H.c) ∈ K at h1
  change (1/2:ℝ) • (H.c+-H.a) ∈ K at h2
  fin_cases i
  · exact h0
  · exact h1
  · simpa [midpoint,sub_eq_add_neg] using h2
  · simpa [midpoint,neg_smul,add_comm] using (hK.2.2.2 _).1 h0
  · simpa [midpoint,neg_smul,sub_eq_add_neg,add_comm] using (hK.2.2.2 _).1 h1
  · simpa [midpoint,neg_smul,sub_eq_add_neg,add_comm] using (hK.2.2.2 _).1 h2

lemma midpoint_not_interior (H : Hex) (i : Fin 6) : H.midpoint i ∉ interior H.set := by
  intro hi
  obtain ⟨h1,h2,h3⟩ := H.interior_set_subset hi
  fin_cases i
  · norm_num [midpoint,map_add,H.ha₁,H.hb₁] at h1
  · norm_num [midpoint,map_add,H.hb₂,H.hc₂] at h2
  · norm_num [midpoint,map_sub,H.hc₃,H.ha₃] at h3
  · norm_num [midpoint,map_add,H.ha₁,H.hb₁] at h1
  · norm_num [midpoint,map_add,H.hb₂,H.hc₂] at h2
  · norm_num [midpoint,map_sub,H.hc₃,H.ha₃] at h3

/-- Contact on every side, as opposed to mere enclosure of the body. -/
theorem midpoint_frontier_of_strict_critical (H : Hex) (hs : H.Strict)
    {K : Set E} (hK : IsSymmetricConvexDisc K) (hKH : K ⊆ H.set)
    (hmin : ∀ G : Hex, K ⊆ G.set → volume H.set ≤ volume G.set) (i : Fin 6) :
    H.midpoint i ∈ frontier K := by
  refine ⟨hK.2.1.isClosed.closure_eq.symm ▸ H.midpoint_mem_of_strict_critical hs hK hKH hmin i,?_⟩
  intro hi
  exact H.midpoint_not_interior i (interior_mono hKH hi)

end Hex

theorem ratioMinimizingHexagon_midpoint_frontier (hs : ratioMinimizingHexagon.Strict) (i : Fin 6) :
    ratioMinimizingHexagon.midpoint i ∈ frontier ratioMinimizingBody :=
  ratioMinimizingHexagon.midpoint_frontier_of_strict_critical hs ratioMinimizingBody_properties.1
    ratioMinimizingHexagon_properties.1 ratioMinimizingHexagon_properties.2.2.2 i

#print axioms Hex.midpoint_frontier_of_strict_critical
#print axioms ratioMinimizingHexagon_midpoint_frontier
end Certificate.Packing
