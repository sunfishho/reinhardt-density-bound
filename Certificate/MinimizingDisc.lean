import Certificate.DiscHausdorffComparison
import Certificate.CriticalHexagonInfimum

/-! Existence of a global minimizer of area divided by the infimum of
circumscribed symmetric hexagon areas. No minimizer is supplied as input. -/
namespace Certificate.Packing
open Set Metric MeasureTheory Filter Topology TopologicalSpace
set_option maxHeartbeats 0

theorem normalized_disc_is_disc {K : Compacts E} (hK : K ∈ normalizedDiscs) :
    IsSymmetricConvexDisc (K : Set E) :=
  ⟨hK.1,K.isCompact,⟨0,zero_interior_of_diamond_subset hK.2.2.1⟩,hK.2.1⟩

lemma convex_coordinate_square : Convex ℝ square := by
  have h0 := (convex_Icc (-1:ℝ) 1).linear_preimage (coord 0)
  have h1 := (convex_Icc (-1:ℝ) 1).linear_preimage (coord 1)
  have he : square = (coord 0) ⁻¹' Icc (-1) 1 ∩ (coord 1) ⁻¹' Icc (-1) 1 := by
    ext x
    simp [square,abs_le,Set.mem_Icc]
  rw [he]
  exact h0.inter h1

lemma normalizedDiscs_nonempty : normalizedDiscs.Nonempty := by
  refine ⟨⟨square,isCompact_square⟩,convex_coordinate_square,?_,?_,Subset.rfl⟩
  · intro x
    simp [square]
  · apply convexHull_min ?_ convex_coordinate_square
    intro x hx
    simp only [mem_insert_iff,mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> norm_num [square,point]

theorem normalized_ratio_comparison {K L : Compacts E}
    (hK : K ∈ normalizedDiscs) (hL : L ∈ normalizedDiscs) {r : ℝ} (hr : 1 < r)
    (hd : edist K L < ENNReal.ofReal ((r-1)/2)) :
    hexagonRatio (K : Set E) ≤ r^4*hexagonRatio (L : Set E) := by
  have hr0 : 0 < r := by linarith
  have hKd := normalized_disc_is_disc hK
  have hLd := normalized_disc_is_disc hL
  have hcp : 0 < (criticalHexArea (K : Set E)).toReal :=
    ENNReal.toReal_pos (criticalHexArea_pos hKd).ne' (criticalHexArea_finite hKd)
  have hlp : 0 < (criticalHexArea (L : Set E)).toReal :=
    ENNReal.toReal_pos (criticalHexArea_pos hLd).ne' (criticalHexArea_finite hLd)
  have ha := area_le_of_subset_dilation hr0 (normalized_near_dilation hL hr hd)
  have hm := criticalHexArea_mono (normalized_near_dilation hK hr (by rwa [edist_comm]))
  rw [criticalHexArea_smul _ hr0] at hm
  have hf : ENNReal.ofReal (r^2)*criticalHexArea (K : Set E) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (criticalHexArea_finite hKd)
  have hmreal : (criticalHexArea (L : Set E)).toReal ≤ r^2*(criticalHexArea (K : Set E)).toReal := by
    simpa [ENNReal.toReal_mul,ENNReal.toReal_ofReal (sq_nonneg r)] using ENNReal.toReal_mono hf hm
  unfold hexagonRatio
  calc
    (volume (K : Set E)).toReal/(criticalHexArea (K : Set E)).toReal ≤
        (r^2*(volume (L : Set E)).toReal)/(criticalHexArea (K : Set E)).toReal :=
      div_le_div_of_nonneg_right ha hcp.le
    _ = r^4*((volume (L : Set E)).toReal/(r^2*(criticalHexArea (K : Set E)).toReal)) := by
      field_simp
    _ ≤ r^4*((volume (L : Set E)).toReal/(criticalHexArea (L : Set E)).toReal) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact div_le_div_of_nonneg_left ENNReal.toReal_nonneg hlp hmreal

theorem lowerSemicontinuousOn_hexagonRatio :
    LowerSemicontinuousOn (fun K : Compacts E => hexagonRatio (K : Set E)) normalizedDiscs := by
  intro K hK b hb
  have he : ∀ᶠ r in 𝓝 (1:ℝ), r^4*b < hexagonRatio (K : Set E) := by
    exact (show Continuous (fun r : ℝ => r^4*b) from by fun_prop).continuousAt.eventually
      (gt_mem_nhds (by simpa using hb))
  obtain ⟨r,hr,hbr⟩ := ((show ∀ᶠ r in 𝓝[>] (1:ℝ), 1 < r from self_mem_nhdsWithin).and
    (nhdsWithin_le_nhds he)).exists
  have heps : 0 < ENNReal.ofReal ((r-1)/2) := ENNReal.ofReal_pos.2 (by linarith)
  filter_upwards [nhdsWithin_le_nhds (Metric.eball_mem_nhds K heps),self_mem_nhdsWithin] with L hL hLn
  have hcomp := normalized_ratio_comparison hK hLn hr (by simpa [Metric.mem_eball,edist_comm] using hL)
  by_contra h
  have hh : r^4*hexagonRatio (L : Set E) ≤ r^4*b :=
    mul_le_mul_of_nonneg_left (le_of_not_gt h) (by positivity)
  linarith

/-- A genuine minimizer exists over all symmetric convex discs. The objective
is the geometric area/hexagon-infimum ratio; equality with the original
packing-density definition is a separate theorem, not assumed here. -/
theorem exists_minimizing_disc : ∃ K : Set E, IsSymmetricConvexDisc K ∧
    ∀ L : Set E, IsSymmetricConvexDisc L → hexagonRatio K ≤ hexagonRatio L := by
  obtain ⟨C,hC,hmin⟩ := LowerSemicontinuousOn.exists_isMinOn normalizedDiscs_nonempty
    isCompact_normalizedDiscs lowerSemicontinuousOn_hexagonRatio
  refine ⟨C,normalized_disc_is_disc hC,?_⟩
  intro K hK
  obtain ⟨L,D,hD,himage⟩ := exists_normalized_representative K hK
  have hh := hmin hD
  change hexagonRatio (C : Set E) ≤ hexagonRatio (D : Set E) at hh
  rwa [himage,hexagonRatio_linear_image] at hh

#print axioms lowerSemicontinuousOn_hexagonRatio
#print axioms exists_minimizing_disc
end Certificate.Packing
