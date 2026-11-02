import Certificate.CriticalFamilyRegularity

/-! A common neighborhood of admissible support-normal perturbations for
the entire compact critical family, and a uniform contact-displacement bound. -/
namespace Certificate.Packing
open Set Filter Topology MeasureTheory
set_option maxHeartbeats 0

theorem eventually_positiveCritical_variation (d : positiveCriticalFamily) :
    ∀ᶠ z : (E →L[ℝ] ℝ) × positiveCriticalFamily in 𝓝 (0,d),
      (positiveCriticalHex z.2).SideVariationValid z.1.toLinearMap 1 ∧
        z.1 (positiveCriticalHex z.2).slideA + z.1 (positiveCriticalHex z.2).slideB ≤ 2 := by
  have hproj : Continuous (fun z : (E →L[ℝ] ℝ) × positiveCriticalFamily => z.2) := continuous_snd
  have ha := (continuous_positiveCritical_vertex 0).comp hproj
  have hb := (continuous_positiveCritical_vertex 1).comp hproj
  have hc := (continuous_positiveCritical_vertex 2).comp hproj
  have hA := continuous_positiveCritical_slideA.comp hproj
  have hB := continuous_positiveCritical_slideB.comp hproj
  have hφ (i : Fin 3) := (continuous_positiveCritical_form i).comp
    (continuous_snd : Continuous (fun z : (E →L[ℝ] ℝ) × positiveCriticalFamily => z.2))
  have hmA : ContinuousAt (fun z : (E →L[ℝ] ℝ) × positiveCriticalFamily =>
      (positiveCriticalHex z.2).movedA z.1.toLinearMap 1) (0,d) := by
    change ContinuousAt (fun z : (E →L[ℝ] ℝ) × positiveCriticalFamily => z.2.val.vertex 0 -
      (1 * z.1 (z.2.val.vertex 0) / (1 + 1 * z.1 (positiveCriticalHex z.2).slideA)) •
        (positiveCriticalHex z.2).slideA) (0,d)
    simp only [one_mul]
    exact ha.continuousAt.sub (((continuous_fst.clm_apply ha).continuousAt.div
      (continuous_const.add (continuous_fst.clm_apply hA)).continuousAt (by simp)).smul hA.continuousAt)
  have hmB : ContinuousAt (fun z : (E →L[ℝ] ℝ) × positiveCriticalFamily =>
      (positiveCriticalHex z.2).movedB z.1.toLinearMap 1) (0,d) := by
    change ContinuousAt (fun z : (E →L[ℝ] ℝ) × positiveCriticalFamily => z.2.val.vertex 1 -
      (1 * z.1 (z.2.val.vertex 1) / (1 + 1 * z.1 (positiveCriticalHex z.2).slideB)) •
        (positiveCriticalHex z.2).slideB) (0,d)
    simp only [one_mul]
    exact hb.continuousAt.sub (((continuous_fst.clm_apply hb).continuousAt.div
      (continuous_const.add (continuous_fst.clm_apply hB)).continuousAt (by simp)).smul hB.continuousAt)
  have hdet : ContinuousAt (fun z : (E →L[ℝ] ℝ) × positiveCriticalFamily =>
      (positiveCriticalHex z.2).variationDet z.1.toLinearMap 1) (0,d) := by
    unfold Hex.variationDet det2
    change ContinuousAt (fun z : (E →L[ℝ] ℝ) × positiveCriticalFamily =>
      (((positiveCriticalHex z.2).movedA z.1.toLinearMap 1 +
        (positiveCriticalHex z.2).movedB z.1.toLinearMap 1) 0) *
        (((positiveCriticalHex z.2).movedB z.1.toLinearMap 1 + z.2.val.vertex 2) 1) -
      (((positiveCriticalHex z.2).movedA z.1.toLinearMap 1 +
        (positiveCriticalHex z.2).movedB z.1.toLinearMap 1) 1) *
        (((positiveCriticalHex z.2).movedB z.1.toLinearMap 1 + z.2.val.vertex 2) 0)) (0,d)
    have hsumA := hmA.add hmB
    have hsumB := hmB.add hc.continuousAt
    exact (((PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0).continuousAt.comp hsumA).mul
      ((PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 1).continuousAt.comp hsumB)).sub
      (((PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 1).continuousAt.comp hsumA).mul
        ((PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0).continuousAt.comp hsumB))
  have eD := continuousAt_const.eventually_lt hdet
    (show (0:ℝ) < (positiveCriticalHex d).variationDet (0 : E →L[ℝ] ℝ).toLinearMap 1 by
      simpa [Hex.variationDet, Hex.movedA, Hex.movedB, Hex.v, Hex.w] using positiveCriticalHex_det_pos d)
  have eA : ∀ᶠ z : (E →L[ℝ] ℝ) × positiveCriticalFamily in 𝓝 (0,d),
      0 < 1 + 1 * z.1 (positiveCriticalHex z.2).slideA :=
    continuousAt_const.eventually_lt (by fun_prop) (by norm_num)
  have eB : ∀ᶠ z : (E →L[ℝ] ℝ) × positiveCriticalFamily in 𝓝 (0,d),
      0 < 1 + 1 * z.1 (positiveCriticalHex z.2).slideB :=
    continuousAt_const.eventually_lt (by fun_prop) (by norm_num)
  have eα := (((hφ 1).continuousAt.clm_apply hmA).abs).eventually_lt continuousAt_const
    (show |(d.val.form 1).toContinuousLinearMap
      ((positiveCriticalHex d).movedA (0 : E →L[ℝ] ℝ).toLinearMap 1)| < 1 by
      simpa [Hex.movedA, positiveCriticalHex, HexParameters.toHex] using (positiveCriticalHex_strict d).1)
  have eβ := (((hφ 2).continuousAt.clm_apply hmB).abs).eventually_lt continuousAt_const
    (show |(d.val.form 2).toContinuousLinearMap
      ((positiveCriticalHex d).movedB (0 : E →L[ℝ] ℝ).toLinearMap 1)| < 1 by
      simpa [Hex.movedB, positiveCriticalHex, HexParameters.toHex] using (positiveCriticalHex_strict d).2.1)
  have hec : ContinuousAt (fun z : (E →L[ℝ] ℝ) × positiveCriticalFamily =>
      |((z.2.val.form 0).toContinuousLinearMap + z.1) (z.2.val.vertex 2)|) (0,d) := by
    fun_prop
  have eγ := hec.eventually_lt continuousAt_const
    (show |((d.val.form 0).toContinuousLinearMap + (0 : E →L[ℝ] ℝ)) (d.val.vertex 2)| < 1 by
      simpa [positiveCriticalHex, HexParameters.toHex] using (positiveCriticalHex_strict d).2.2)
  have eS : ∀ᶠ z : (E →L[ℝ] ℝ) × positiveCriticalFamily in 𝓝 (0,d),
      z.1 (positiveCriticalHex z.2).slideA + z.1 (positiveCriticalHex z.2).slideB < 2 :=
    (show ContinuousAt (fun z : (E →L[ℝ] ℝ) × positiveCriticalFamily =>
      z.1 (positiveCriticalHex z.2).slideA + z.1 (positiveCriticalHex z.2).slideB) (0,d) by
      fun_prop).eventually_lt continuousAt_const (by norm_num)
  filter_upwards [eA,eB,eα,eβ,eγ,eD,eS] with z hdenA hdenB hα hβ hγ hD hS
  refine ⟨⟨hdenA,hdenB,?_,?_,?_,hD⟩,hS.le⟩
  · simpa [Function.comp_def, positiveCriticalHex, HexParameters.toHex] using hα
  · simpa [Function.comp_def, positiveCriticalHex, HexParameters.toHex] using hβ
  · simpa [positiveCriticalHex, HexParameters.toHex] using hγ

theorem eventually_uniform_critical_variation :
    ∀ᶠ ζ : E →L[ℝ] ℝ in 𝓝 0, ∀ d : positiveCriticalFamily,
      (positiveCriticalHex d).SideVariationValid ζ.toLinearMap 1 ∧
        ζ (positiveCriticalHex d).slideA + ζ (positiveCriticalHex d).slideB ≤ 2 := by
  letI : CompactSpace positiveCriticalFamily := isCompact_iff_compactSpace.1 isCompact_positiveCriticalFamily
  have hh := isCompact_univ.eventually_forall_of_forall_eventually
    (x₀ := (0 : E →L[ℝ] ℝ))
    (P := fun ζ d => (positiveCriticalHex d).SideVariationValid ζ.toLinearMap 1 ∧
      ζ (positiveCriticalHex d).slideA + ζ (positiveCriticalHex d).slideB ≤ 2)
    (fun d (_ : d ∈ (Set.univ : Set positiveCriticalFamily)) => eventually_positiveCritical_variation d)
  filter_upwards [hh] with ζ hζ
  exact fun d => hζ d (mem_univ d)

theorem uniform_critical_support_contact_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ ζ : E →L[ℝ] ℝ in 𝓝 0,
      ∀ (d : positiveCriticalFamily) (ψ : E →L[ℝ] ℝ) (q : E),
      ζ = ψ - (positiveCriticalHex d).φ₁.toContinuousLinearMap →
      q ∈ ratioMinimizingBody → (∀ x ∈ ratioMinimizingBody, |ψ x| ≤ 1) → ψ q = 1 →
      ‖ζ‖ ≤ C * ‖q-(positiveCriticalHex d).midpoint 0‖ := by
  obtain ⟨A,hA,hcoeff⟩ := criticalSupportCoefficient_uniform_bound
  obtain ⟨B,hB,heval⟩ := critical_normal_evaluation_uniform_bound
  refine ⟨B*A, mul_pos hB hA, ?_⟩
  filter_upwards [eventually_uniform_critical_variation] with ζ hv
  intro d ψ q hζ hq hψ hψq
  let H := positiveCriticalHex d
  have hs := positiveCriticalHex_strict d
  have hp := positiveCriticalHex_det_pos d
  have hH : ratioMinimizingBody ⊆ H.set := d.property.1.2.1
  have he : volume H.set = criticalHexArea ratioMinimizingBody := critical_parameter_area d.property.1
  have hm : H.midpoint 0 ∈ ratioMinimizingBody :=
    frontier_subset_iff_isClosed.2 ratioMinimizingBody_properties.1.2.1.isClosed
      (criticalHexagon_of_minimizer_midpoint_frontier H hH he 0)
  have hmin : ∀ G : Hex, ratioMinimizingBody ⊆ G.set → volume H.set ≤ volume G.set := by
    intro G hG; rw [he]; exact criticalHexArea_le G hG
  have hvd := hv d
  rw [hζ] at hvd
  have hsmall : H.SideVariationValid (ψ.toLinearMap-H.φ₁) 1 := by simpa using hvd.1
  have hslide : (ψ.toLinearMap-H.φ₁) H.slideA + (ψ.toLinearMap-H.φ₁) H.slideB ≤ 2 := by
    simpa using hvd.2
  have hsq := H.support_deficit_square_bound hs hp hH hmin hm ψ.toLinearMap hψ hsmall hslide
  have hδ : 0 ≤ 1 - ψ (H.midpoint 0) := by
    have hh := (le_abs_self _).trans (hψ _ hm); linarith
  have hc := mul_le_mul_of_nonneg_right (hcoeff d) hδ
  have hnorm := heval d ζ
  have hsq' : (ζ H.a)^2 + (ζ H.b)^2 ≤ A * (1-ψ (H.midpoint 0)) := by
    rw [hζ]
    exact (by simpa [H, Hex.midpoint, criticalSupportCoefficient] using hsq.trans hc)
  have hnormsq : ‖ζ‖^2 ≤ (B*A) * (1-ψ (H.midpoint 0)) :=
    hnorm.trans (by simpa [mul_assoc] using mul_le_mul_of_nonneg_left hsq' hB.le)
  have hmφ : H.φ₁ (H.midpoint 0) = 1 := by
    norm_num [Hex.midpoint, map_smul, map_add, H.ha₁, H.hb₁]
  have hqφ : H.φ₁ q ≤ 1 := (le_abs_self _).trans (hH hq).1
  have hd : 1-ψ (H.midpoint 0) ≤ ζ (q-H.midpoint 0) := by
    rw [hζ]
    simp only [ContinuousLinearMap.sub_apply, map_sub, LinearMap.coe_toContinuousLinearMap']
    change 1 - ψ (H.midpoint 0) ≤ ψ q - H.φ₁ q - (ψ (H.midpoint 0) - H.φ₁ (H.midpoint 0))
    rw [hψq, hmφ]; linarith
  have hdn := hd.trans ((le_abs_self _).trans (ζ.le_opNorm _))
  have hmul := mul_le_mul_of_nonneg_left hdn (mul_pos hB hA).le
  by_cases hz : ‖ζ‖ = 0
  · rw [hz]; positivity
  · have hpos := lt_of_le_of_ne (norm_nonneg ζ) (Ne.symm hz)
    nlinarith only [hnormsq, hmul, hpos]

end Certificate.Packing
