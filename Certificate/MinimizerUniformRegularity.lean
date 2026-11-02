import Certificate.CriticalFamilyUniformVariation
import Mathlib.Topology.Algebra.MetricSpace.Lipschitz

/-! Uniform Lipschitz supporting normals and tangents on the entire boundary
of the constructed minimizer. Compactness is used for the family estimates
and for passing from two-point local estimates to the global bound. -/
namespace Certificate.Packing
open Set Filter Topology MeasureTheory
open scoped NNReal
set_option maxHeartbeats 0

theorem uniform_critical_gradient_small_difference :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ ζ : E →L[ℝ] ℝ in 𝓝 0,
      ∀ p q : criticalMidpointSet,
      ζ = minimizerGaugeGradient q.val-minimizerGaugeGradient p.val →
      ‖ζ‖ ≤ C * ‖q.val-p.val‖ := by
  obtain ⟨C,hC,he⟩ := uniform_critical_support_contact_bound
  refine ⟨C,hC,?_⟩
  filter_upwards [he] with ζ hζ
  intro p q hdiff
  obtain ⟨d,hd⟩ := positiveCriticalProjection_surjective p
  let H := positiveCriticalHex d
  have hm : H.midpoint 0 = p.val := congrArg Subtype.val hd
  have hφ : H.φ₁.toContinuousLinearMap = minimizerGaugeGradient p.val := by
    apply ContinuousLinearMap.coe_injective
    have hh := minimizerGaugeGradient_eq_sideNormal H d.property.1.2.1
      (critical_parameter_area d.property.1) 0
    rw [hm] at hh
    simpa [Hex.sideNormal] using hh.symm
  have hs := criticalMidpoint_gradient_support q
  have hh := hζ d (minimizerGaugeGradient q.val) q.val
    (by change ζ = minimizerGaugeGradient q.val - H.φ₁.toContinuousLinearMap; rwa [hφ]) (criticalMidpoint_mem_body q)
    (normalizedSupportAt_abs ratioMinimizingBody_properties.1.2.2.2 hs) hs.1
  change ‖ζ‖ ≤ C * ‖q.val-H.midpoint 0‖ at hh
  rwa [hm] at hh

theorem locallyLipschitz_criticalMidpoint_gradient :
    LocallyLipschitz (fun p : criticalMidpointSet => minimizerGaugeGradient p.val) := by
  obtain ⟨C,hC,he⟩ := uniform_critical_gradient_small_difference
  have hg : Continuous (fun p : criticalMidpointSet => minimizerGaugeGradient p.val) :=
    continuousOn_minimizerGaugeGradient.comp_continuous continuous_subtype_val
      (fun p => criticalMidpoint_ne_zero p)
  intro p
  have ht : Tendsto (fun z : criticalMidpointSet × criticalMidpointSet =>
      minimizerGaugeGradient z.2.val-minimizerGaugeGradient z.1.val) (𝓝 (p,p)) (𝓝 0) := by
    convert! ((hg.comp continuous_snd).sub (hg.comp continuous_fst)).tendsto (p,p) using 1 <;> simp
  have hh : ∀ᶠ z : criticalMidpointSet × criticalMidpointSet in 𝓝 (p,p),
      ‖minimizerGaugeGradient z.2.val-minimizerGaugeGradient z.1.val‖ ≤ C * ‖z.2.val-z.1.val‖ := by
    filter_upwards [ht.eventually he] with z hz
    exact hz z.1 z.2 rfl
  obtain ⟨u,hu,v,hv,huv⟩ := mem_nhds_prod_iff.1 hh
  refine ⟨⟨C,hC.le⟩, u ∩ v, inter_mem hu hv, ?_⟩
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  have hxy := huv (show (x,y) ∈ u ×ˢ v from ⟨hx.1,hy.2⟩)
  change ‖minimizerGaugeGradient y.val-minimizerGaugeGradient x.val‖ ≤ C * ‖y.val-x.val‖ at hxy
  convert! hxy using 1 <;> simp [dist_eq_norm, norm_sub_rev]
  change C * dist x.val y.val = C * ‖x.val-y.val‖
  rw [dist_eq_norm]

theorem criticalMidpoint_gradient_lipschitz :
    ∃ L : ℝ≥0, LipschitzWith L (fun p : criticalMidpointSet => minimizerGaugeGradient p.val) := by
  letI : CompactSpace criticalMidpointSet := isCompact_iff_compactSpace.1 isCompact_criticalMidpointSet
  obtain ⟨L,hL⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact isCompact_univ
    (locallyLipschitzOn_univ.2 locallyLipschitz_criticalMidpoint_gradient)
  exact ⟨L,lipschitzOnWith_univ.1 hL⟩

theorem minimizerBoundary_gradient_lipschitz :
    ∃ L : ℝ≥0, LipschitzWith L
      (fun p : frontier ratioMinimizingBody => minimizerGaugeGradient p.val) := by
  obtain ⟨L,hL⟩ := criticalMidpoint_gradient_lipschitz
  refine ⟨L,LipschitzWith.of_dist_le_mul (fun p q => ?_)⟩
  exact hL.dist_le_mul (criticalMidpointBoundaryHomeomorph.symm p)
    (criticalMidpointBoundaryHomeomorph.symm q)

theorem criticalMidpoint_tangent_lipschitz :
    ∃ L : ℝ≥0, LipschitzWith L criticalMidpointTangent := by
  obtain ⟨L,hL⟩ := criticalMidpoint_gradient_lipschitz
  have hh := supportTangentLinear.toContinuousLinearMap.lipschitz.comp hL
  refine ⟨‖supportTangentLinear.toContinuousLinearMap‖₊ * L,?_⟩
  convert! hh using 1
  funext p
  exact criticalMidpointTangent_eq_supportTangent p

theorem minimizerBoundary_tangent_lipschitz :
    ∃ L : ℝ≥0, LipschitzWith L minimizerBoundaryTangent := by
  obtain ⟨L,hL⟩ := criticalMidpoint_tangent_lipschitz
  refine ⟨L,LipschitzWith.of_dist_le_mul (fun p q => ?_)⟩
  exact hL.dist_le_mul (criticalMidpointBoundaryHomeomorph.symm p)
    (criticalMidpointBoundaryHomeomorph.symm q)

/-- Every Lipschitz parametrization of the boundary now has an absolutely
continuous supporting-tangent field. The curve is supplied here. -/
theorem minimizerBoundary_tangent_ac_of_lipschitz
    {γ : ℝ → frontier ratioMinimizingBody} {K : ℝ≥0} {a b : ℝ}
    (hγ : LipschitzOnWith K γ (uIcc a b)) :
    AbsolutelyContinuousOnInterval (fun t => minimizerBoundaryTangent (γ t)) a b := by
  obtain ⟨L,hL⟩ := minimizerBoundary_tangent_lipschitz
  exact (hL.comp_lipschitzOnWith hγ).absolutelyContinuousOnInterval

theorem minimizerBoundary_gradient_ac_of_lipschitz
    {γ : ℝ → frontier ratioMinimizingBody} {K : ℝ≥0} {a b : ℝ}
    (hγ : LipschitzOnWith K γ (uIcc a b)) :
    AbsolutelyContinuousOnInterval (fun t => minimizerGaugeGradient (γ t).val) a b := by
  obtain ⟨L,hL⟩ := minimizerBoundary_gradient_lipschitz
  exact (hL.comp_lipschitzOnWith hγ).absolutelyContinuousOnInterval

end Certificate.Packing
