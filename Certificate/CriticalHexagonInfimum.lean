import Certificate.DiscAffineNormalization
import Certificate.NormalizedDiscInterior
import Certificate.HVFirstCorner

/-! The infimum of circumscribed hexagon areas and its exact affine covariance.
Attainment by a hexagon is not assumed or asserted in this module. -/
namespace Certificate.Packing
open Set MeasureTheory Pointwise
open scoped ENNReal
set_option maxHeartbeats 0

noncomputable def squareHex : Hex where
  φ₁ := coord 1
  φ₂ := coord 0
  φ₃ := -coord 1
  a := point (-1) 1
  b := point 1 1
  c := point 1 (-1)
  ha₁ := by norm_num [point]
  ha₃ := by norm_num [point]
  hb₁ := by norm_num [point]
  hb₂ := by norm_num [point]
  hc₂ := by norm_num [point]
  hc₃ := by norm_num [point]
  hin_a := by norm_num [point]
  hin_b := by norm_num [point]
  hin_c := by norm_num [point]
  hdet := by norm_num [point,det2]

lemma squareHex_set : squareHex.set = square := by
  ext x
  simp [squareHex,Hex.set,square,and_comm,and_left_comm]

noncomputable def criticalHexArea (K : Set E) : ℝ≥0∞ :=
  ⨅ (H : Hex) (_ : K ⊆ H.set), volume H.set

lemma criticalHexArea_le {K : Set E} (H : Hex) (h : K ⊆ H.set) :
    criticalHexArea K ≤ volume H.set := iInf_le_of_le H (iInf_le _ h)

lemma volume_le_criticalHexArea (K : Set E) : volume K ≤ criticalHexArea K := by
  apply le_iInf; intro H
  apply le_iInf; intro h
  exact measure_mono h

lemma criticalHexArea_mono {K L : Set E} (h : K ⊆ L) : criticalHexArea K ≤ criticalHexArea L := by
  apply le_iInf; intro H
  apply le_iInf; intro hL
  exact criticalHexArea_le H (h.trans hL)

lemma criticalHexArea_le_four {K : Set E} (h : K ⊆ square) : criticalHexArea K ≤ 4 := by
  simpa only [squareHex_set,volume_square] using criticalHexArea_le squareHex (squareHex_set.symm ▸ h)

lemma criticalHexArea_linear_le (K : Set E) (L : E ≃ₗ[ℝ] E) :
    criticalHexArea (L '' K) ≤ ENNReal.ofReal |LinearMap.det (L : E →ₗ[ℝ] E)| * criticalHexArea K := by
  have hj : 0 < |LinearMap.det (L : E →ₗ[ℝ] E)| := abs_pos.mpr (linearEquiv_det_ne_zero L)
  unfold criticalHexArea
  rw [ENNReal.mul_iInf_of_ne (ENNReal.ofReal_ne_zero_iff.2 hj) ENNReal.ofReal_ne_top]
  apply le_iInf; intro H
  rw [ENNReal.mul_iInf_of_ne (ENNReal.ofReal_ne_zero_iff.2 hj) ENNReal.ofReal_ne_top]
  apply le_iInf; intro hH
  have hsub : L '' K ⊆ (H.map L).set := by rw [Hex.map_set]; exact image_mono hH
  exact (criticalHexArea_le (H.map L) hsub).trans_eq (H.volume_map L)

theorem criticalHexArea_linear_image (K : Set E) (L : E ≃ₗ[ℝ] E) :
    criticalHexArea (L '' K) = ENNReal.ofReal |LinearMap.det (L : E →ₗ[ℝ] E)| * criticalHexArea K := by
  apply le_antisymm (criticalHexArea_linear_le K L)
  have hh := criticalHexArea_linear_le (L '' K) L.symm
  have hs : L.symm '' (L '' K) = K := by ext x; simp
  rw [hs] at hh
  have hp : |LinearMap.det (L : E →ₗ[ℝ] E)| * |LinearMap.det (L.symm : E →ₗ[ℝ] E)|=1 := by
    rw [LinearEquiv.det_coe_symm,abs_inv,mul_inv_cancel₀ (abs_ne_zero.mpr (linearEquiv_det_ne_zero L))]
  have ht := mul_le_mul' (le_refl (ENNReal.ofReal |LinearMap.det (L : E →ₗ[ℝ] E)|)) hh
  simpa only [← mul_assoc,← ENNReal.ofReal_mul (abs_nonneg _),hp,ENNReal.ofReal_one,one_mul] using ht

theorem criticalHexArea_finite {K : Set E} (hK : IsSymmetricConvexDisc K) : criticalHexArea K ≠ ⊤ := by
  obtain ⟨L,hL,hd,hs⟩ := exists_affine_normalized_disc K hK
  have hf : criticalHexArea (L '' K) ≠ ⊤ := (criticalHexArea_le_four hs).trans_lt (by norm_num) |>.ne
  rw [criticalHexArea_linear_image] at hf
  intro ht
  rw [ht,ENNReal.mul_top (ENNReal.ofReal_ne_zero_iff.2
    (abs_pos.mpr (linearEquiv_det_ne_zero L)))] at hf
  exact hf rfl

theorem criticalHexArea_pos {K : Set E} (hK : IsSymmetricConvexDisc K) : 0 < criticalHexArea K :=
  (Measure.measure_pos_of_nonempty_interior volume hK.2.2.1).trans_le (volume_le_criticalHexArea K)

noncomputable def hexagonRatio (K : Set E) : ℝ :=
  (volume K).toReal/(criticalHexArea K).toReal

theorem hexagonRatio_linear_image (K : Set E) (L : E ≃ₗ[ℝ] E) :
    hexagonRatio (L '' K) = hexagonRatio K := by
  have hv : volume (L '' K) = ENNReal.ofReal |LinearMap.det (L : E →ₗ[ℝ] E)| * volume K := by
    convert! Measure.addHaar_image_linearMap volume (L : E →ₗ[ℝ] E) K
  rw [hexagonRatio,hv,
    criticalHexArea_linear_image,ENNReal.toReal_mul,ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (abs_nonneg _)]
  exact mul_div_mul_left _ _ (abs_ne_zero.mpr (linearEquiv_det_ne_zero L))

noncomputable def dilationFrame (r : ℝ) (hr : r ≠ 0) : E ≃ₗ[ℝ] E :=
  pairFrame (point r 0) (point 0 r) (by simpa [det2,point] using mul_ne_zero hr hr)

lemma dilationFrame_apply (r : ℝ) (hr : r ≠ 0) (x : E) : dilationFrame r hr x = r • x := by
  ext i; fin_cases i <;> simp [dilationFrame,point] <;> ring

theorem criticalHexArea_smul (K : Set E) {r : ℝ} (hr : 0 < r) :
    criticalHexArea (r • K) = ENNReal.ofReal (r^2)*criticalHexArea K := by
  have he : (dilationFrame r hr.ne') '' K = r • K := by
    change (fun x => dilationFrame r hr.ne' x) '' K = r • K
    simp_rw [dilationFrame_apply]
    rfl
  rw [← he,criticalHexArea_linear_image]
  congr 1
  change ENNReal.ofReal |LinearMap.det (pairFrameLinear (point r 0) (point 0 r))| = _
  rw [pairFrameLinear_det]
  simp [det2,point,pow_two,abs_of_pos hr]

#print axioms criticalHexArea_linear_image
#print axioms criticalHexArea_finite
#print axioms hexagonRatio_linear_image
end Certificate.Packing
