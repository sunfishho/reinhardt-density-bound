import Certificate.HexagonUniqueSupport

/-! Quantitative side variation. Minimality controls the squared change of
the support form by its deficit at the old side midpoint. This is the
coercive estimate needed for tangent regularity, with no envelope assumption. -/
namespace Certificate.Packing
open Set MeasureTheory Filter Topology
set_option maxHeartbeats 0
namespace Hex

/-- Polarization of the exact quadratic term, without fixing the midpoint. -/
lemma side_quadratic_polarization (H : Hex) (hs : H.Strict) (ζ : E →ₗ[ℝ] ℝ) :
    2 * (det2 H.a H.b * (ζ H.a * ζ H.slideB + ζ H.b * ζ H.slideA) -
      ζ H.a * ζ H.b * det2 H.slideA H.slideB) =
    det2 H.a H.b * (ζ H.a + ζ H.b) * (ζ H.slideA + ζ H.slideB) -
      det2 H.slideA H.slideB * ((ζ H.a)^2 + (ζ H.b)^2) := by
  let F := HVGeometry.pairLinear H.φ₁ ζ
  have hab : LinearMap.det F * det2 H.a H.b = ζ H.b - ζ H.a := by
    rw [← det2_linearMap]
    simp [F, HVGeometry.pairLinear, det2, point, H.ha₁, H.hb₁]
  obtain ⟨hA, _, hB, _⟩ := H.slide_evaluations hs
  have hAB : LinearMap.det F * det2 H.slideA H.slideB =
      ζ H.slideB - ζ H.slideA := by
    rw [← det2_linearMap]
    simp [F, HVGeometry.pairLinear, det2, point, hA, hB]
  have hr : det2 H.a H.b * (ζ H.slideB - ζ H.slideA) =
      (ζ H.b - ζ H.a) * det2 H.slideA H.slideB := by
    rw [← hAB, ← hab]; ring
  nlinarith [congrArg (fun s : ℝ => (ζ H.a - ζ H.b) * s) hr]

/-- Minimality forbids a negative area variation for an admissible support. -/
lemma support_variation_det_nonneg (H : Hex) (hs : H.Strict)
    (hD : 0 < det2 H.v H.w) {K : Set E} (hKH : K ⊆ H.set)
    (hmin : ∀ G : Hex, K ⊆ G.set → volume H.set ≤ volume G.set)
    (ψ : E →ₗ[ℝ] ℝ) (hψ : ∀ x ∈ K, |ψ x| ≤ 1)
    (hv : H.SideVariationValid (ψ - H.φ₁) 1) :
    0 ≤ H.variationDet (ψ - H.φ₁) 1 - det2 H.v H.w := by
  let G := H.vary hs (ψ - H.φ₁) 1 hv
  have hG : K ⊆ G.set := H.vary_encloses_of_support hs hKH ψ hψ 1 (by norm_num) le_rfl hv
  have hm := hmin G hG
  rw [G.volume_eq_covolume, H.volume_eq_covolume] at hm
  change ENNReal.ofReal |det2 H.v H.w| ≤ ENNReal.ofReal |H.variationDet (ψ - H.φ₁) 1| at hm
  rw [abs_of_pos hD, abs_of_pos hv.determinant_pos] at hm
  have hh := (ENNReal.ofReal_le_ofReal_iff hv.determinant_pos.le).1 hm
  linarith

/-- Exact coercivity inequality. The coefficient on the left is strictly
positive for a strict positively oriented hexagon. -/
theorem support_deficit_coercivity (H : Hex) (hs : H.Strict)
    (hD : 0 < det2 H.v H.w) {K : Set E} (hKH : K ⊆ H.set)
    (hmin : ∀ G : Hex, K ⊆ G.set → volume H.set ≤ volume G.set)
    (ψ : E →ₗ[ℝ] ℝ) (hψ : ∀ x ∈ K, |ψ x| ≤ 1)
    (hv : H.SideVariationValid (ψ - H.φ₁) 1) :
    -det2 H.slideA H.slideB * (((ψ-H.φ₁) H.a)^2 + ((ψ-H.φ₁) H.b)^2) ≤
      2 * det2 H.a H.b * (1 - ψ ((1/2:ℝ) • (H.a+H.b))) *
        (2 + (ψ-H.φ₁) H.slideA + (ψ-H.φ₁) H.slideB) := by
  let ζ := ψ - H.φ₁
  have hn := H.support_variation_det_nonneg hs hD hKH hmin ψ hψ hv
  have he := H.moved_det_difference hs ζ 1 hv.denA_pos.ne' hv.denB_pos.ne'
  change H.variationDet ζ 1 - det2 H.v H.w = _ at he
  rw [he] at hn
  have hden := mul_pos hv.denA_pos hv.denB_pos
  have hnum := mul_nonneg hn hden.le
  rw [div_mul_cancel₀ _ hden.ne'] at hnum
  have hpol := H.side_quadratic_polarization hs ζ
  have hmid : 2 * (1 - ψ ((1/2:ℝ) • (H.a+H.b))) = -(ζ H.a + ζ H.b) := by
    simp [ζ, map_smul, map_add, H.ha₁, H.hb₁]; ring
  change -det2 H.slideA H.slideB * ((ζ H.a)^2 + (ζ H.b)^2) ≤ _
  rw [show 2 * det2 H.a H.b * (1 - ψ ((1/2:ℝ) • (H.a+H.b))) =
      det2 H.a H.b * (2 * (1 - ψ ((1/2:ℝ) • (H.a+H.b)))) by ring, hmid]
  nlinarith only [hnum, hpol]

/-- A uniform coefficient after bounding the two slide evaluations. -/
theorem support_deficit_square_bound (H : Hex) (hs : H.Strict)
    (hD : 0 < det2 H.v H.w) {K : Set E} (hKH : K ⊆ H.set)
    (hmin : ∀ G : Hex, K ⊆ G.set → volume H.set ≤ volume G.set)
    (hm : (1/2:ℝ) • (H.a+H.b) ∈ K)
    (ψ : E →ₗ[ℝ] ℝ) (hψ : ∀ x ∈ K, |ψ x| ≤ 1)
    (hv : H.SideVariationValid (ψ - H.φ₁) 1)
    (hslide : (ψ-H.φ₁) H.slideA + (ψ-H.φ₁) H.slideB ≤ 2) :
    ((ψ-H.φ₁) H.a)^2 + ((ψ-H.φ₁) H.b)^2 ≤
      (8 * det2 H.a H.b / (-det2 H.slideA H.slideB)) *
        (1 - ψ ((1/2:ℝ) • (H.a+H.b))) := by
  have hδ : 0 ≤ 1 - ψ ((1/2:ℝ) • (H.a+H.b)) := by
    have hh := (le_abs_self _).trans (hψ _ hm); linarith
  have hd := H.strict_first_det_pos hs hD
  have hc : 0 < -det2 H.slideA H.slideB := neg_pos.2 (H.slide_pair_det_neg hs hD)
  have hb := H.support_deficit_coercivity hs hD hKH hmin ψ hψ hv
  have hu := mul_le_mul_of_nonneg_left (show
      2 + (ψ-H.φ₁) H.slideA + (ψ-H.φ₁) H.slideB ≤ 4 by linarith)
      (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hd.le) hδ)
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hc).2
  nlinarith only [hb, hu]

end Hex
end Certificate.Packing
