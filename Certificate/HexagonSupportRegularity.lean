import Certificate.HexagonSupportCoercivity

/-! Local quantitative stability of a minimum hexagon's supporting form.
All admissibility conditions are established in a neighborhood of the old
normal; the final estimate is linear in displacement of the contact point. -/
namespace Certificate.Packing
open Set MeasureTheory Filter Topology
set_option maxHeartbeats 0
namespace Hex

theorem eventually_small_normal_variation (H : Hex) (hs : H.Strict)
    (hD : 0 < det2 H.v H.w) :
    ∀ᶠ ζ : E →L[ℝ] ℝ in 𝓝 0,
      H.SideVariationValid ζ.toLinearMap 1 ∧ ζ H.slideA + ζ H.slideB ≤ 2 := by
  have hAc : ContinuousAt (fun ζ : E →L[ℝ] ℝ => H.movedA ζ.toLinearMap 1) 0 := by
    change ContinuousAt (fun ζ : E →L[ℝ] ℝ => H.a -
      (1 * ζ H.a / (1 + 1 * ζ H.slideA)) • H.slideA) 0
    fun_prop (disch := norm_num)
  have hBc : ContinuousAt (fun ζ : E →L[ℝ] ℝ => H.movedB ζ.toLinearMap 1) 0 := by
    change ContinuousAt (fun ζ : E →L[ℝ] ℝ => H.b -
      (1 * ζ H.b / (1 + 1 * ζ H.slideB)) • H.slideB) 0
    fun_prop (disch := norm_num)
  have hDc : ContinuousAt (fun ζ : E →L[ℝ] ℝ => H.variationDet ζ.toLinearMap 1) 0 := by
    unfold variationDet det2
    fun_prop
  have eD : ∀ᶠ ζ : E →L[ℝ] ℝ in 𝓝 0, 0 < H.variationDet ζ.toLinearMap 1 :=
    continuousAt_const.eventually_lt hDc (by simpa [variationDet, movedA, movedB, v, w] using hD)
  have eA : ∀ᶠ ζ : E →L[ℝ] ℝ in 𝓝 0, 0 < 1 + 1 * ζ H.slideA :=
    continuousAt_const.eventually_lt (by fun_prop) (by norm_num)
  have eB : ∀ᶠ ζ : E →L[ℝ] ℝ in 𝓝 0, 0 < 1 + 1 * ζ H.slideB :=
    continuousAt_const.eventually_lt (by fun_prop) (by norm_num)
  have ea : ∀ᶠ ζ : E →L[ℝ] ℝ in 𝓝 0, |H.φ₂ (H.movedA ζ.toLinearMap 1)| < 1 :=
    ((H.φ₂.continuous_of_finiteDimensional.continuousAt.comp hAc).abs).eventually_lt
      continuousAt_const (by simpa [movedA] using hs.1)
  have eb : ∀ᶠ ζ : E →L[ℝ] ℝ in 𝓝 0, |H.φ₃ (H.movedB ζ.toLinearMap 1)| < 1 :=
    ((H.φ₃.continuous_of_finiteDimensional.continuousAt.comp hBc).abs).eventually_lt
      continuousAt_const (by simpa [movedB] using hs.2.1)
  have ec : ∀ᶠ ζ : E →L[ℝ] ℝ in 𝓝 0, |(H.φ₁ + (1:ℝ) • ζ.toLinearMap) H.c| < 1 := by
    have hc : ContinuousAt (fun ζ : E →L[ℝ] ℝ => |(H.φ₁ + (1:ℝ) • ζ.toLinearMap) H.c|) 0 := by
      change ContinuousAt (fun ζ : E →L[ℝ] ℝ => |H.φ₁ H.c + 1 * ζ H.c|) 0
      fun_prop
    exact hc.eventually_lt continuousAt_const (by simpa using hs.2.2)
  have eS : ∀ᶠ ζ : E →L[ℝ] ℝ in 𝓝 0, ζ H.slideA + ζ H.slideB < 2 :=
    (show ContinuousAt (fun ζ : E →L[ℝ] ℝ => ζ H.slideA + ζ H.slideB) 0 by fun_prop).eventually_lt
      continuousAt_const (by norm_num)
  filter_upwards [eA, eB, ea, eb, ec, eD, eS] with ζ hA hB ha hb hc hd hS
  exact ⟨⟨hA, hB, ha, hb, hc, hd⟩, hS.le⟩

/-- Evaluations on the endpoints control the entire normal, since the
endpoints of a strict positively oriented side form a basis. -/
theorem exists_normal_evaluation_bound (H : Hex) (hs : H.Strict)
    (hD : 0 < det2 H.v H.w) :
    ∃ B : ℝ, 0 < B ∧ ∀ ζ : E →L[ℝ] ℝ,
      ‖ζ‖^2 ≤ B * ((ζ H.a)^2 + (ζ H.b)^2) := by
  let F : (E →L[ℝ] ℝ) →ₗ[ℝ] (ℝ × ℝ) :=
    { toFun := fun ζ => (ζ H.a, ζ H.b)
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have hi : Function.Injective F := by
    intro ζ ξ he
    apply ContinuousLinearMap.coe_injective
    have hh := linear_forms_eq_of_pair ζ.toLinearMap ξ.toLinearMap H.a H.b
      (H.strict_first_det_pos hs hD).ne' (congrArg Prod.fst he) (congrArg Prod.snd he)
    exact hh
  obtain ⟨B, hB, hBF⟩ := F.injective_iff_antilipschitz.1 hi
  refine ⟨(B:ℝ)^2, sq_pos_of_pos (by exact_mod_cast hB), ?_⟩
  intro ζ
  have hh := hBF.le_mul_dist ζ 0
  simp only [dist_zero_right, map_zero] at hh
  have hnorm : ‖F ζ‖^2 ≤ (ζ H.a)^2 + (ζ H.b)^2 := by
    change (max |ζ H.a| |ζ H.b|)^2 ≤ _
    rcases le_total |ζ H.a| |ζ H.b| with hab | hba
    · rw [max_eq_right hab, sq_abs]; nlinarith [sq_nonneg (ζ H.a)]
    · rw [max_eq_left hba, sq_abs]; nlinarith [sq_nonneg (ζ H.b)]
  have hsq := sq_le_sq₀ (norm_nonneg ζ) (mul_nonneg B.coe_nonneg (norm_nonneg (F ζ))) |>.2 hh
  calc
    ‖ζ‖^2 ≤ ((B:ℝ) * ‖F ζ‖)^2 := hsq
    _ = (B:ℝ)^2 * ‖F ζ‖^2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hnorm (sq_nonneg _)

/-- A neighborhood of the original normal has a quadratic support-deficit
bound in operator norm. All constants depend only on the fixed hexagon. -/
theorem eventually_support_norm_square_bound (H : Hex) (hs : H.Strict)
    (hD : 0 < det2 H.v H.w) {K : Set E} (hKH : K ⊆ H.set)
    (hmin : ∀ G : Hex, K ⊆ G.set → volume H.set ≤ volume G.set)
    (hm : (1/2:ℝ) • (H.a+H.b) ∈ K) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ ψ : E →L[ℝ] ℝ in 𝓝 H.φ₁.toContinuousLinearMap,
      (∀ x ∈ K, |ψ x| ≤ 1) →
      ‖ψ - H.φ₁.toContinuousLinearMap‖^2 ≤ C * (1 - ψ ((1/2:ℝ) • (H.a+H.b))) := by
  obtain ⟨B, hB, hb⟩ := H.exists_normal_evaluation_bound hs hD
  let A := 8 * det2 H.a H.b / (-det2 H.slideA H.slideB)
  have hA : 0 < A := div_pos (mul_pos (by norm_num) (H.strict_first_det_pos hs hD))
    (neg_pos.2 (H.slide_pair_det_neg hs hD))
  refine ⟨B*A, mul_pos hB hA, ?_⟩
  have ht : Tendsto (fun ψ : E →L[ℝ] ℝ => ψ-H.φ₁.toContinuousLinearMap)
      (𝓝 H.φ₁.toContinuousLinearMap) (𝓝 0) := by
    convert! (continuous_id.sub (continuous_const (y := H.φ₁.toContinuousLinearMap))).tendsto H.φ₁.toContinuousLinearMap using 1 <;> simp
  filter_upwards [ht.eventually (H.eventually_small_normal_variation hs hD)] with ψ hψ
  intro hsupport
  have hh := H.support_deficit_square_bound hs hD hKH hmin hm ψ.toLinearMap hsupport hψ.1 hψ.2
  have hn := hb (ψ-H.φ₁.toContinuousLinearMap)
  have hmul := mul_le_mul_of_nonneg_left hh hB.le
  change ‖ψ-H.φ₁.toContinuousLinearMap‖^2 ≤ B*A * _
  exact hn.trans (by simpa [A, mul_assoc] using hmul)

/-- Comparing a new contact point with the old midpoint improves the square
bound to a linear displacement bound. No differentiability is assumed. -/
theorem eventually_support_contact_lipschitz (H : Hex) (hs : H.Strict)
    (hD : 0 < det2 H.v H.w) {K : Set E} (hKH : K ⊆ H.set)
    (hmin : ∀ G : Hex, K ⊆ G.set → volume H.set ≤ volume G.set)
    (hm : (1/2:ℝ) • (H.a+H.b) ∈ K) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ ψ : E →L[ℝ] ℝ in 𝓝 H.φ₁.toContinuousLinearMap,
      ∀ q ∈ K, (∀ x ∈ K, |ψ x| ≤ 1) → ψ q = 1 →
      ‖ψ-H.φ₁.toContinuousLinearMap‖ ≤ C * ‖q-(1/2:ℝ) • (H.a+H.b)‖ := by
  obtain ⟨C, hC, he⟩ := H.eventually_support_norm_square_bound hs hD hKH hmin hm
  refine ⟨C, hC, ?_⟩
  filter_upwards [he] with ψ hψ
  intro q hq hsupport heq
  let ζ := ψ-H.φ₁.toContinuousLinearMap
  let m := (1/2:ℝ) • (H.a+H.b)
  have hmφ : H.φ₁ m = 1 := by simp [m, map_smul, map_add, H.ha₁, H.hb₁]; norm_num
  have hqφ : H.φ₁ q ≤ 1 := (le_abs_self _).trans (hKH hq).1
  have hδ : 1 - ψ m ≤ ζ (q-m) := by
    simp only [ζ, ContinuousLinearMap.sub_apply, map_sub, LinearMap.coe_toContinuousLinearMap']
    rw [heq, hmφ]; linarith
  have hn : 1 - ψ m ≤ ‖ζ‖ * ‖q-m‖ :=
    hδ.trans ((le_abs_self _).trans (ζ.le_opNorm (q-m)))
  have hsquare := hψ hsupport
  change ‖ζ‖^2 ≤ C * (1-ψ m) at hsquare
  have hh := mul_le_mul_of_nonneg_left hn hC.le
  change ‖ζ‖ ≤ C * ‖q-m‖
  by_cases hz : ‖ζ‖ = 0
  · rw [hz]; positivity
  · have hp := lt_of_le_of_ne (norm_nonneg ζ) (Ne.symm hz)
    nlinarith only [hsquare, hh, hp]

end Hex
end Certificate.Packing
