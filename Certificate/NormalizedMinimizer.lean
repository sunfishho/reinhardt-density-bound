import Certificate.MinimizingDisc

/-! An actual global ratio minimizer, scaled so its circumscribed-hexagon
area infimum equals a prescribed positive number. -/
namespace Certificate.Packing
open Set MeasureTheory Pointwise
open scoped ENNReal
set_option maxHeartbeats 0

lemma symmetricConvexDisc_linear_image {K : Set E} (hK : IsSymmetricConvexDisc K)
    (L : E ≃ₗ[ℝ] E) : IsSymmetricConvexDisc (L '' K) := by
  refine ⟨hK.1.linear_image (L : E →ₗ[ℝ] E),
    hK.2.1.image L.toContinuousLinearEquiv.continuous,?_,?_⟩
  · have hn := hK.2.2.1.image L.toContinuousLinearEquiv.toHomeomorph
    rw [L.toContinuousLinearEquiv.toHomeomorph.image_interior K] at hn
    convert! hn
  · intro z
    constructor <;> rintro ⟨x,hx,he⟩
    · exact ⟨-x,(hK.2.2.2 x).1 hx,by rw [map_neg,he]⟩
    · exact ⟨-x,(hK.2.2.2 x).1 hx,by rw [map_neg,he,neg_neg]⟩

lemma dilationFrame_image (K : Set E) (r : ℝ) (hr : r ≠ 0) :
    dilationFrame r hr '' K = r • K := by
  change (fun x => dilationFrame r hr x) '' K = r • K
  simp_rw [dilationFrame_apply]
  rfl

lemma hexAreaLowerBound_iff_criticalHexArea {K : Set E} {A : ℝ} :
    HexAreaLowerBound K A ↔ ENNReal.ofReal A ≤ criticalHexArea K := by
  constructor
  · intro h; exact le_iInf (fun H => le_iInf (fun hh => h H hh))
  · intro h H hh; exact h.trans (criticalHexArea_le H hh)

/-- No minimizing body is an input: it is obtained by compactness and then scaled. -/
theorem exists_normalized_minimizing_disc (A : ℝ) (hA : 0 < A) :
    ∃ K : Set E, IsSymmetricConvexDisc K ∧
      criticalHexArea K = ENNReal.ofReal A ∧
      (∀ L : Set E, IsSymmetricConvexDisc L → hexagonRatio K ≤ hexagonRatio L) := by
  obtain ⟨K,hK,hmin⟩ := exists_minimizing_disc
  let m := (criticalHexArea K).toReal
  have hm : 0 < m := ENNReal.toReal_pos (criticalHexArea_pos hK).ne' (criticalHexArea_finite hK)
  let r := Real.sqrt (A/m)
  have hr : 0 < r := Real.sqrt_pos.2 (div_pos hA hm)
  have hr2 : r^2 = A/m := Real.sq_sqrt (div_nonneg hA.le hm.le)
  have he := dilationFrame_image K r hr.ne'
  refine ⟨r • K,?_,?_,?_⟩
  · rw [← he]; exact symmetricConvexDisc_linear_image hK _
  · rw [criticalHexArea_smul K hr,hr2,← ENNReal.ofReal_toReal (criticalHexArea_finite hK),
      ← ENNReal.ofReal_mul (div_nonneg hA.le hm.le)]
    exact congrArg ENNReal.ofReal (div_mul_cancel₀ A hm.ne')
  · intro L hL
    rw [← he,hexagonRatio_linear_image]
    exact hmin L hL

/-- Minimality among all bodies whose circumscribed hexagons have area at least `A`. -/
theorem normalized_minimizer_area_minimal {K : Set E} {A : ℝ} (hA : 0 < A)
    (he : criticalHexArea K = ENNReal.ofReal A)
    (hmin : ∀ L : Set E, IsSymmetricConvexDisc L → hexagonRatio K ≤ hexagonRatio L)
    {L : Set E} (hL : IsSymmetricConvexDisc L) (hbound : HexAreaLowerBound L A) :
    (volume K).toReal ≤ (volume L).toReal := by
  have hAL : A ≤ (criticalHexArea L).toReal := by
    have hh := ENNReal.toReal_mono (criticalHexArea_finite hL)
      (hexAreaLowerBound_iff_criticalHexArea.1 hbound)
    simpa [ENNReal.toReal_ofReal hA.le] using hh
  have hh := hmin L hL
  unfold hexagonRatio at hh
  rw [he,ENNReal.toReal_ofReal hA.le] at hh
  have hdiv : (volume L).toReal/(criticalHexArea L).toReal ≤ (volume L).toReal/A :=
    div_le_div_of_nonneg_left ENNReal.toReal_nonneg hA hAL
  exact (div_le_div_iff_of_pos_right hA).1 (hh.trans hdiv)

/-- The normalization used by the Reinhardt control problem. This does not
assert existence of an attaining hexagon or a smooth frame boundary. -/
theorem exists_reinhardt_normalized_minimizer : ∃ K : Set E,
    IsSymmetricConvexDisc K ∧ criticalHexArea K = ENNReal.ofReal (2*Real.sqrt 3) ∧
    HexAreaLowerBound K (2*Real.sqrt 3) ∧
    (∀ L : Set E, IsSymmetricConvexDisc L → hexagonRatio K ≤ hexagonRatio L) ∧
    (∀ L : Set E, IsSymmetricConvexDisc L → HexAreaLowerBound L (2*Real.sqrt 3) →
      (volume K).toReal ≤ (volume L).toReal) := by
  have hA : 0 < 2*Real.sqrt 3 := by positivity
  obtain ⟨K,hK,he,hm⟩ := exists_normalized_minimizing_disc _ hA
  exact ⟨K,hK,he,hexAreaLowerBound_iff_criticalHexArea.2 he.ge,hm,
    fun L hL hb => normalized_minimizer_area_minimal hA he hm hL hb⟩

#print axioms exists_reinhardt_normalized_minimizer
end Certificate.Packing
