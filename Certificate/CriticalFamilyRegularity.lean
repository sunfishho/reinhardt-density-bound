import Certificate.MinimizerPointwiseRegularity

/-! Uniform quantitative coefficients on the compact family of positively
oriented critical hexagons. No continuous choice of representatives is needed. -/
namespace Certificate.Packing
open Set Filter Topology MeasureTheory
set_option maxHeartbeats 0

lemma continuous_det2_comp {α : Type*} [TopologicalSpace α] {f g : α → E}
    (hf : Continuous f) (hg : Continuous g) : Continuous (fun x => det2 (f x) (g x)) := by
  exact (((PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0).comp hf).mul
    ((PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 1).comp hg)).sub
    (((PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 1).comp hf).mul
      ((PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0).comp hg))

noncomputable def positiveCriticalHex (d : positiveCriticalFamily) : Hex :=
  d.val.toHex d.property.1.1

lemma positiveCriticalHex_strict (d : positiveCriticalFamily) : (positiveCriticalHex d).Strict :=
  criticalHexagon_of_minimizer_strict _ d.property.1.2.1 (critical_parameter_area d.property.1)

lemma positiveCriticalHex_det_pos (d : positiveCriticalFamily) :
    0 < det2 (positiveCriticalHex d).v (positiveCriticalHex d).w :=
  positiveCriticalFamily_pos d.property

lemma continuous_positiveCritical_vertex (i : Fin 3) :
    Continuous (fun d : positiveCriticalFamily => d.val.vertex i) := by
  unfold HexParameters.vertex point
  fun_prop

lemma continuous_positiveCritical_form (i : Fin 3) :
    Continuous (fun d : positiveCriticalFamily => (d.val.form i).toContinuousLinearMap) := by
  have he : (fun d : positiveCriticalFamily => (d.val.form i).toContinuousLinearMap) =
      (fun d => d.val.1 i 0 • (coord 0).toContinuousLinearMap +
        d.val.1 i 1 • (coord 1).toContinuousLinearMap) := by
    funext d
    apply ContinuousLinearMap.coe_injective
    simp [HexParameters.form]
  rw [he]
  fun_prop

lemma continuous_positiveCritical_slideA :
    Continuous (fun d : positiveCriticalFamily => (positiveCriticalHex d).slideA) := by
  have hc := (continuous_positiveCritical_form 0).clm_apply (continuous_positiveCritical_vertex 2)
  have hn (d : positiveCriticalFamily) : 1 + d.val.form 0 (d.val.vertex 2) ≠ 0 := by
    have h := (abs_lt.1 (positiveCriticalHex_strict d).2.2).1
    change -1 < d.val.form 0 (d.val.vertex 2) at h
    linarith
  change Continuous (fun d : positiveCriticalFamily =>
    (1 / (1 + d.val.form 0 (d.val.vertex 2))) • (d.val.vertex 0 + d.val.vertex 2))
  have hc' : Continuous (fun d : positiveCriticalFamily => d.val.form 0 (d.val.vertex 2)) := by
    simpa only [LinearMap.coe_toContinuousLinearMap'] using hc
  exact (continuous_const.div (continuous_const.add hc') hn).smul
    ((continuous_positiveCritical_vertex 0).add (continuous_positiveCritical_vertex 2))

lemma continuous_positiveCritical_slideB :
    Continuous (fun d : positiveCriticalFamily => (positiveCriticalHex d).slideB) := by
  have hc := (continuous_positiveCritical_form 0).clm_apply (continuous_positiveCritical_vertex 2)
  have hn (d : positiveCriticalFamily) : 1 - d.val.form 0 (d.val.vertex 2) ≠ 0 := by
    have h := (abs_lt.1 (positiveCriticalHex_strict d).2.2).2
    change d.val.form 0 (d.val.vertex 2) < 1 at h
    linarith
  change Continuous (fun d : positiveCriticalFamily =>
    (1 / (1 - d.val.form 0 (d.val.vertex 2))) • (d.val.vertex 1 - d.val.vertex 2))
  have hc' : Continuous (fun d : positiveCriticalFamily => d.val.form 0 (d.val.vertex 2)) := by
    simpa only [LinearMap.coe_toContinuousLinearMap'] using hc
  exact (continuous_const.div (continuous_const.sub hc') hn).smul
    ((continuous_positiveCritical_vertex 1).sub (continuous_positiveCritical_vertex 2))

noncomputable def criticalSupportCoefficient (d : positiveCriticalFamily) : ℝ :=
  8 * det2 (positiveCriticalHex d).a (positiveCriticalHex d).b /
    (-det2 (positiveCriticalHex d).slideA (positiveCriticalHex d).slideB)

lemma criticalSupportCoefficient_pos (d : positiveCriticalFamily) :
    0 < criticalSupportCoefficient d :=
  div_pos (mul_pos (by norm_num)
    ((positiveCriticalHex d).strict_first_det_pos (positiveCriticalHex_strict d)
      (positiveCriticalHex_det_pos d)))
    (neg_pos.2 ((positiveCriticalHex d).slide_pair_det_neg (positiveCriticalHex_strict d)
      (positiveCriticalHex_det_pos d)))

lemma continuous_criticalSupportCoefficient : Continuous criticalSupportCoefficient := by
  have ha := continuous_positiveCritical_vertex 0
  have hb := continuous_positiveCritical_vertex 1
  have hA := continuous_positiveCritical_slideA
  have hB := continuous_positiveCritical_slideB
  have hn (d : positiveCriticalFamily) :
      -det2 (positiveCriticalHex d).slideA (positiveCriticalHex d).slideB ≠ 0 :=
    (neg_pos.2 ((positiveCriticalHex d).slide_pair_det_neg (positiveCriticalHex_strict d)
      (positiveCriticalHex_det_pos d))).ne'
  unfold criticalSupportCoefficient
  apply Continuous.div _ _ hn
  · change Continuous (fun d : positiveCriticalFamily => 8 * det2 (d.val.vertex 0) (d.val.vertex 1))
    unfold det2
    fun_prop
  · exact (continuous_det2_comp hA hB).neg

theorem criticalSupportCoefficient_uniform_bound :
    ∃ A : ℝ, 0 < A ∧ ∀ d : positiveCriticalFamily, criticalSupportCoefficient d ≤ A := by
  letI : CompactSpace positiveCriticalFamily := isCompact_iff_compactSpace.1 isCompact_positiveCriticalFamily
  obtain ⟨A, hA⟩ := isCompact_univ.bddAbove_image continuous_criticalSupportCoefficient.continuousOn
  refine ⟨max 1 A, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro d
  exact (hA (mem_image_of_mem _ (mem_univ d))).trans (le_max_right _ _)

/-- Uniform conditioning of endpoint evaluation on all critical hexagons. -/
theorem critical_normal_evaluation_uniform_bound :
    ∃ B : ℝ, 0 < B ∧ ∀ (d : positiveCriticalFamily) (ζ : E →L[ℝ] ℝ),
      ‖ζ‖^2 ≤ B * ((ζ (positiveCriticalHex d).a)^2 + (ζ (positiveCriticalHex d).b)^2) := by
  letI : CompactSpace positiveCriticalFamily := isCompact_iff_compactSpace.1 isCompact_positiveCriticalFamily
  let S : Set (positiveCriticalFamily × (E →L[ℝ] ℝ)) := Set.univ ×ˢ Metric.sphere 0 1
  have hS : IsCompact S := isCompact_univ.prod (isCompact_sphere 0 1)
  let f : positiveCriticalFamily × (E →L[ℝ] ℝ) → ℝ := fun z =>
    (z.2 (positiveCriticalHex z.1).a)^2 + (z.2 (positiveCriticalHex z.1).b)^2
  have hf : Continuous f := by
    have ha := (continuous_positiveCritical_vertex 0).comp
      (continuous_fst : Continuous (fun z : positiveCriticalFamily × (E →L[ℝ] ℝ) => z.1))
    have hb := (continuous_positiveCritical_vertex 1).comp
      (continuous_fst : Continuous (fun z : positiveCriticalFamily × (E →L[ℝ] ℝ) => z.1))
    change Continuous (fun z : positiveCriticalFamily × (E →L[ℝ] ℝ) =>
      (z.2 (z.1.val.vertex 0))^2 + (z.2 (z.1.val.vertex 1))^2)
    fun_prop
  have hpos (z : positiveCriticalFamily × (E →L[ℝ] ℝ)) (hz : z ∈ S) : 0 < f z := by
    have hn : ‖z.2‖ = 1 := by simpa [S, Metric.mem_sphere, dist_zero_right] using hz.2
    have hne : z.2 ≠ 0 := by intro he; simp [he] at hn
    have hnon : 0 ≤ f z := add_nonneg (sq_nonneg _) (sq_nonneg _)
    apply lt_of_le_of_ne hnon
    intro he
    have ha : z.2 (positiveCriticalHex z.1).a = 0 := by
      dsimp [f] at he
      nlinarith [sq_nonneg (z.2 (positiveCriticalHex z.1).b)]
    have hb : z.2 (positiveCriticalHex z.1).b = 0 := by
      dsimp [f] at he
      nlinarith [sq_nonneg (z.2 (positiveCriticalHex z.1).a)]
    apply hne
    apply ContinuousLinearMap.coe_injective
    exact linear_forms_eq_of_pair _ _ _ _
      ((positiveCriticalHex z.1).strict_first_det_pos (positiveCriticalHex_strict z.1)
        (positiveCriticalHex_det_pos z.1)).ne' ha hb
  obtain ⟨B, hB⟩ := hS.bddAbove_image (hf.continuousOn.inv₀ (fun z hz => (hpos z hz).ne'))
  let M := max 1 B
  have hM : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨M, hM, ?_⟩
  intro d ζ
  by_cases hz : ζ = 0
  · simp [hz]
  have hn : 0 < ‖ζ‖ := norm_pos_iff.2 hz
  let ξ : E →L[ℝ] ℝ := ‖ζ‖⁻¹ • ζ
  have hξ : (d, ξ) ∈ S := by
    refine ⟨mem_univ _, ?_⟩
    simp [ξ, Metric.mem_sphere, dist_zero_right, norm_smul, abs_of_pos hn, hn.ne']
  have hbound : (f (d,ξ))⁻¹ ≤ M :=
    (hB (mem_image_of_mem _ hξ)).trans (le_max_right _ _)
  have hprod : 1 ≤ M * f (d,ξ) := by
    have hh := mul_le_mul_of_nonneg_right hbound (hpos _ hξ).le
    simpa only [inv_mul_cancel₀ (hpos _ hξ).ne'] using hh
  have he : f (d,ξ) =
      ((ζ (positiveCriticalHex d).a)^2 + (ζ (positiveCriticalHex d).b)^2) / ‖ζ‖^2 := by
    simp [f, ξ]
    ring
  rw [he, ← mul_div_assoc] at hprod
  simpa only [one_mul] using (le_div_iff₀ (sq_pos_of_pos hn)).1 hprod

end Certificate.Packing
