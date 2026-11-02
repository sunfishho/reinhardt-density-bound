import Certificate.HexagonCovolumeArea
import Certificate.CriticalHexagonInfimum

/-! General comparison with the original benchmark packing density. No
critical-hexagon attainment, regular boundary, or balanced frame is needed. -/
namespace Certificate.Packing
open Set MeasureTheory
open scoped ENNReal
set_option maxHeartbeats 0

lemma exists_enclosing_hexagon (K : Set E) (hK : IsSymmetricConvexDisc K) :
    ∃ H : Hex, K ⊆ H.set := by
  obtain ⟨L,hL,hd,hs⟩ := exists_affine_normalized_disc K hK
  refine ⟨squareHex.map L.symm,?_⟩
  rw [Hex.map_set,squareHex_set]
  intro x hx
  exact ⟨L x,hs ⟨x,hx,rfl⟩,L.symm_apply_apply x⟩

lemma packingDensity_pos (K : Set E) (hK : IsSymmetricConvexDisc K) : 0 < packingDensity K := by
  obtain ⟨H,hH⟩ := exists_enclosing_hexagon K hK
  have ha : 0 < (volume K).toReal := ENNReal.toReal_pos
    (Measure.measure_pos_of_nonempty_interior volume hK.2.2.1).ne' hK.2.1.measure_lt_top.ne
  exact (div_pos ha (abs_pos.2 H.hdet)).trans_le (packingDensity_ge_hexagon K hK H hH)

/-- The geometric hexagon ratio is a lower bound for the original packing
supremum over congruent copies, for every symmetric convex disc. -/
theorem hexagonRatio_le_packingDensity (K : Set E) (hK : IsSymmetricConvexDisc K) :
    hexagonRatio K ≤ packingDensity K := by
  have hp := packingDensity_pos K hK
  have hm : 0 < (criticalHexArea K).toReal :=
    ENNReal.toReal_pos (criticalHexArea_pos hK).ne' (criticalHexArea_finite hK)
  have hh : ENNReal.ofReal ((volume K).toReal/packingDensity K) ≤ criticalHexArea K := by
    apply le_iInf; intro H
    apply le_iInf; intro hH
    have hc := packingDensity_ge_hexagon K hK H hH
    have hcov : (volume K).toReal/packingDensity K ≤ |det2 H.v H.w| := by
      apply (div_le_iff₀ hp).2
      have h := (div_le_iff₀ (abs_pos.2 H.hdet)).1 hc
      simpa only [Hex.v,Hex.w,mul_comm] using h
    exact (ENNReal.ofReal_le_ofReal hcov).trans H.volume_ge_covolume
  have hreal := ENNReal.toReal_mono (criticalHexArea_finite hK) hh
  rw [ENNReal.toReal_ofReal (div_nonneg ENNReal.toReal_nonneg hp.le)] at hreal
  apply (div_le_iff₀ hm).2
  have h := (div_le_iff₀ hp).1 hreal
  simpa only [mul_comm] using h

#print axioms hexagonRatio_le_packingDensity
end Certificate.Packing
