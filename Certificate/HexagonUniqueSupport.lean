import Certificate.HexagonSecondVariation
import Certificate.HexagonAdmissibleVariation
import Certificate.HexagonDegeneracy

/-! A minimum enclosing hexagon's midpoint has a unique normalized support
form. A different support gives a strictly smaller enclosing hexagon by the
exact quadratic side variation. -/
namespace Certificate.Packing
open Set MeasureTheory Filter Topology
set_option maxHeartbeats 0
namespace Hex

theorem first_support_unique_oriented (H : Hex) (hs : H.Strict)
    (hD : 0 < det2 H.v H.w) {K : Set E} (hKH : K ⊆ H.set)
    (hmin : ∀ G : Hex, K ⊆ G.set → volume H.set ≤ volume G.set)
    (ψ : E →ₗ[ℝ] ℝ) (hψ : ∀ x ∈ K, |ψ x| ≤ 1)
    (hm : ψ ((1/2:ℝ) • (H.a+H.b))=1) : ψ=H.φ₁ := by
  by_contra hne
  let ζ := ψ-H.φ₁
  have hz : ζ H.a+ζ H.b=0 := by
    simp only [map_smul,map_add,smul_eq_mul] at hm
    simp [ζ,H.ha₁,H.hb₁]
    linarith
  have hza : ζ H.a ≠ 0 := by
    intro hzero
    have hzb : ζ H.b=0 := by linarith
    apply hne
    apply linear_forms_eq_of_pair _ _ H.a H.b (H.strict_first_det_pos hs hD).ne'
    · simpa [ζ,sub_eq_zero] using hzero
    · simpa [ζ,sub_eq_zero] using hzb
  have ev := H.eventually_sideVariationValid hs hD ζ
  have et : ∀ᶠ t in 𝓝 (0:ℝ), t < 1 :=
    continuousAt_id.eventually_lt continuousAt_const (by norm_num)
  obtain ⟨t,ht,hv,ht1⟩ :=
    ((show ∀ᶠ t in 𝓝[>] (0:ℝ), 0 < t from self_mem_nhdsWithin).and
      (nhdsWithin_le_nhds (ev.and et))).exists
  let G := H.vary hs ζ t hv
  have hG : K ⊆ G.set := H.vary_encloses_of_support hs hKH ψ hψ t ht.le ht1.le hv
  have hdec : H.variationDet ζ t < det2 H.v H.w := by
    have he := H.moved_det_difference_of_midpoint_fixed hs ζ hz t hv.denA_pos.ne' hv.denB_pos.ne'
    have hn : t^2*(ζ H.a)^2*det2 H.slideA H.slideB /
        ((1+t*ζ H.slideA)*(1+t*ζ H.slideB)) < 0 :=
      div_neg_of_neg_of_pos
        (mul_neg_of_pos_of_neg (mul_pos (sq_pos_of_pos ht) (sq_pos_of_ne_zero hza))
          (H.slide_pair_det_neg hs hD)) (mul_pos hv.denA_pos hv.denB_pos)
    change H.variationDet ζ t-det2 H.v H.w = _ at he
    linarith
  have hlt : volume G.set < volume H.set := by
    rw [G.volume_eq_covolume,H.volume_eq_covolume]
    change ENNReal.ofReal |H.variationDet ζ t| < ENNReal.ofReal |det2 H.v H.w|
    rw [abs_of_pos hv.determinant_pos,abs_of_pos hD]
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hv.determinant_pos.le).2 hdec
  exact (not_lt_of_ge (hmin G hG)) hlt

theorem first_support_unique (H : Hex) (hs : H.Strict) {K : Set E} (hKH : K ⊆ H.set)
    (hmin : ∀ G : Hex, K ⊆ G.set → volume H.set ≤ volume G.set)
    (ψ : E →ₗ[ℝ] ℝ) (hψ : ∀ x ∈ K, |ψ x| ≤ 1)
    (hm : ψ ((1/2:ℝ) • (H.a+H.b))=1) : ψ=H.φ₁ := by
  rcases lt_or_gt_of_ne H.hdet with hd | hd
  · change det2 H.v H.w < 0 at hd
    have hsub : K ⊆ H.flip.set := by rwa [H.flip_set]
    have hmin' : ∀ G : Hex, K ⊆ G.set → volume H.flip.set ≤ volume G.set := by
      simpa only [H.flip_set] using hmin
    exact H.flip.first_support_unique_oriented (H.flip_strict hs)
      (by rw [H.flip_det]; linarith) hsub hmin' ψ hψ (by rwa [H.flip_first])
  · exact H.first_support_unique_oriented hs hd hKH hmin ψ hψ hm

#print axioms first_support_unique_oriented
#print axioms first_support_unique
end Hex
end Certificate.Packing
