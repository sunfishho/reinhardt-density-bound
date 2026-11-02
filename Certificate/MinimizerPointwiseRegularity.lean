import Certificate.HexagonSupportRegularity
import Certificate.MinimizerBoundarySuccessor

/-! Quantitative regularity at each boundary point. The constant may depend
on the base point. A uniform bound over the compact critical family is a
separate obligation; these statements alone do not assert global Lipschitz
regularity or absolute continuity. -/
namespace Certificate.Packing
open Set MeasureTheory Filter Topology
set_option maxHeartbeats 0

theorem criticalMidpoint_gradient_pointwise_lipschitz (p : criticalMidpointSet) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ q : criticalMidpointSet in 𝓝 p,
      ‖minimizerGaugeGradient q.val - minimizerGaugeGradient p.val‖ ≤ C * ‖q.val-p.val‖ := by
  obtain ⟨H, hH, he, hp, hm⟩ := exists_positive_criticalHexagonMidpoint p
  have hmp : H.midpoint 0 = p.val := congrArg Subtype.val hm
  have hs := criticalHexagon_of_minimizer_strict H hH he
  have hmin : ∀ G : Hex, ratioMinimizingBody ⊆ G.set → volume H.set ≤ volume G.set := by
    intro G hG
    rw [he]
    exact criticalHexArea_le G hG
  have hmK : (1/2:ℝ) • (H.a+H.b) ∈ ratioMinimizingBody := by
    change H.midpoint 0 ∈ ratioMinimizingBody
    rw [hmp]
    exact criticalMidpoint_mem_body p
  obtain ⟨C, hC, hlocal⟩ := H.eventually_support_contact_lipschitz hs hp hH hmin hmK
  have hφ : H.φ₁.toContinuousLinearMap = minimizerGaugeGradient p.val := by
    apply ContinuousLinearMap.coe_injective
    have hh := minimizerGaugeGradient_eq_sideNormal H hH he 0
    rw [hmp] at hh
    simpa [Hex.sideNormal] using hh.symm
  have hcont : Continuous (fun q : criticalMidpointSet => minimizerGaugeGradient q.val) :=
    continuousOn_minimizerGaugeGradient.comp_continuous continuous_subtype_val
      (fun q => criticalMidpoint_ne_zero q)
  rw [hφ] at hlocal
  refine ⟨C, hC, ?_⟩
  filter_upwards [(hcont.tendsto p).eventually hlocal] with q hq
  have hsupport := criticalMidpoint_gradient_support q
  have hbound := hq q.val (criticalMidpoint_mem_body q)
    (normalizedSupportAt_abs ratioMinimizingBody_properties.1.2.2.2 hsupport) hsupport.1
  change ‖minimizerGaugeGradient q.val - minimizerGaugeGradient p.val‖ ≤
    C * ‖q.val - H.midpoint 0‖ at hbound
  rwa [hmp] at hbound

/-- The gauge gradient has a finite local slope at every point of the full
boundary, now that critical-midpoint coverage has been proved. -/
theorem minimizerBoundary_gradient_pointwise_lipschitz (p : frontier ratioMinimizingBody) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ q : frontier ratioMinimizingBody in 𝓝 p,
      ‖minimizerGaugeGradient q.val-minimizerGaugeGradient p.val‖ ≤ C * ‖q.val-p.val‖ := by
  obtain ⟨C, hC, he⟩ := criticalMidpoint_gradient_pointwise_lipschitz
    (criticalMidpointBoundaryHomeomorph.symm p)
  refine ⟨C, hC, ?_⟩
  exact (criticalMidpointBoundaryHomeomorph.symm.continuous.tendsto p).eventually he

noncomputable def supportTangentLinear : (E →L[ℝ] ℝ) →ₗ[ℝ] E where
  toFun φ := point (-φ (point 0 1)) (φ (point 1 0))
  map_add' φ ψ := by ext i; fin_cases i <;> simp [point]; ring
  map_smul' c φ := by ext i; fin_cases i <;> simp [point]

lemma criticalMidpointTangent_eq_supportTangent (p : criticalMidpointSet) :
    criticalMidpointTangent p = supportTangentLinear (minimizerGaugeGradient p.val) := by
  have h0 := det_criticalMidpointTangent p (point 0 1)
  have h1 := det_criticalMidpointTangent p (point 1 0)
  ext i
  fin_cases i
  · change _ = -minimizerGaugeGradient p.val (point 0 1)
    simp [det2, point] at h0
    simpa [point] using congrArg Neg.neg h0
  · change _ = minimizerGaugeGradient p.val (point 1 0)
    simpa [det2, point] using h1

theorem criticalMidpoint_tangent_pointwise_lipschitz (p : criticalMidpointSet) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ q : criticalMidpointSet in 𝓝 p,
      ‖criticalMidpointTangent q-criticalMidpointTangent p‖ ≤ C * ‖q.val-p.val‖ := by
  obtain ⟨C, hC, he⟩ := criticalMidpoint_gradient_pointwise_lipschitz p
  let R := supportTangentLinear.toContinuousLinearMap
  refine ⟨(‖R‖+1)*C, mul_pos (by positivity) hC, ?_⟩
  filter_upwards [he] with q hq
  rw [criticalMidpointTangent_eq_supportTangent, criticalMidpointTangent_eq_supportTangent]
  change ‖R (minimizerGaugeGradient q.val) - R (minimizerGaugeGradient p.val)‖ ≤ _
  rw [← map_sub]
  calc
    _ ≤ ‖R‖ * ‖minimizerGaugeGradient q.val-minimizerGaugeGradient p.val‖ := R.le_opNorm _
    _ ≤ ‖R‖ * (C * ‖q.val-p.val‖) := mul_le_mul_of_nonneg_left hq (norm_nonneg R)
    _ ≤ _ := by nlinarith [mul_nonneg hC.le (norm_nonneg (q.val-p.val))]

theorem minimizerBoundary_tangent_pointwise_lipschitz (p : frontier ratioMinimizingBody) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ q : frontier ratioMinimizingBody in 𝓝 p,
      ‖minimizerBoundaryTangent q-minimizerBoundaryTangent p‖ ≤ C * ‖q.val-p.val‖ := by
  obtain ⟨C, hC, he⟩ := criticalMidpoint_tangent_pointwise_lipschitz
    (criticalMidpointBoundaryHomeomorph.symm p)
  refine ⟨C, hC, ?_⟩
  exact (criticalMidpointBoundaryHomeomorph.symm.continuous.tendsto p).eventually he

end Certificate.Packing
