import Certificate.MinimizerFrameBoundary
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-! The fundamental endpoint is the actual successor of the angular starting
point. Its angle is constructed in (0,pi); no regular-hexagon angular spacing
is assumed for the unnormalized minimizing body. -/
namespace Certificate.Packing
open Set Filter Topology MeasureTheory
set_option maxHeartbeats 300000

theorem unitCirclePoint_det (s t : ℝ) :
    det2 (unitCirclePoint s) (unitCirclePoint t)=Real.sin (t-s) := by
  simp [unitCirclePoint,point,det2,Real.sin_sub]
  ring

theorem upper_point_polar {x : E} (hy : 0 < x 1) :
    ∃ θ : ℝ, θ ∈ Ioo 0 Real.pi ∧ unitCirclePoint θ=‖x‖⁻¹ • x := by
  have hn : 0 < ‖x‖ := norm_pos_iff.2 (by
    intro h; have := congrArg (fun z : E => z 1) h; simp at this; linarith)
  have hn2 : ‖x‖^2=(x 0)^2+(x 1)^2 := by
    rw [EuclideanSpace.real_norm_sq_eq]; simp [Fin.sum_univ_two]
  have hx : -1 < x 0/‖x‖ ∧ x 0/‖x‖ < 1 := by
    constructor
    · apply (lt_div_iff₀ hn).2; nlinarith [sq_nonneg (x 0+‖x‖)]
    · apply (div_lt_iff₀ hn).2; nlinarith [sq_nonneg (x 0-‖x‖)]
  refine ⟨Real.arccos (x 0/‖x‖),⟨Real.arccos_pos.2 hx.2,Real.arccos_lt_pi.2 hx.1⟩,?_⟩
  have he : 1-(x 0/‖x‖)^2=(x 1/‖x‖)^2 := by
    field_simp
    nlinarith only [hn2]
  have hs : Real.sin (Real.arccos (x 0/‖x‖))=x 1/‖x‖ := by
    rw [Real.sin_arccos,he,Real.sqrt_sq (div_nonneg hy.le hn.le)]
  ext i
  fin_cases i
  · simpa [unitCirclePoint,point] using (Real.cos_arccos hx.1.le hx.2.le).trans
      (show x 0/‖x‖=‖x‖⁻¹*x 0 by ring)
  · simpa [unitCirclePoint,point] using hs.trans
      (show x 1/‖x‖=‖x‖⁻¹*x 1 by ring)

theorem minimizerRadialFoot_normalized_boundary {x : E}
    (hx : x ∈ frontier ratioMinimizingBody) : minimizerRadialFoot (‖x‖⁻¹ • x)=x := by
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.2
    (criticalMidpoint_ne_zero ⟨x,criticalMidpointSet_eq_frontier_minimizer.symm ▸ hx⟩)
  have hg : gauge ratioMinimizingBody x=1 :=
    (gauge_eq_one_iff_mem_frontier ratioMinimizingBody_properties.1.1
      (disc_mem_nhds_zero ratioMinimizingBody_properties.1)).2 hx
  simp only [minimizerRadialFoot,gauge_smul_of_nonneg (inv_nonneg.2 (norm_nonneg x)),
    hg,smul_eq_mul,mul_one,inv_inv,smul_smul,mul_inv_cancel₀ hn,one_smul]

theorem minimizerAngularBoundary_upper_surjective {x : E}
    (hx : x ∈ frontier ratioMinimizingBody) (hy : 0 < x 1) :
    ∃ θ ∈ Ioo 0 Real.pi, (minimizerAngularBoundary θ).val=x := by
  obtain ⟨θ,hθ,he⟩ := upper_point_polar hy
  refine ⟨θ,hθ,?_⟩
  change minimizerRadialFoot (unitCirclePoint θ)=x
  rw [he,minimizerRadialFoot_normalized_boundary hx]

theorem minimizerAngularBoundary_injOn_half :
    InjOn minimizerAngularBoundary (Icc 0 Real.pi) := by
  intro s hs t ht he
  have hv := congrArg Subtype.val he
  change minimizerRadialFoot (unitCirclePoint s)=minimizerRadialFoot (unitCirclePoint t) at hv
  rw [minimizerRadialFoot_eq_boundary (unitCirclePoint_mem_sphere s),
    minimizerRadialFoot_eq_boundary (unitCirclePoint_mem_sphere t)] at hv
  have hu := (discRadialHomeomorph ratioMinimizingBody ratioMinimizingBody_properties.1).injective hv
  apply Real.strictAntiOn_cos.injOn hs ht
  simpa [unitCirclePoint,point] using congrArg (fun z : E => z 0) hu

theorem minimizerAngularBoundary_det_sign (s t : ℝ) :
    0 < det2 (minimizerAngularBoundary s).val (minimizerAngularBoundary t).val ↔
      0 < Real.sin (t-s) := by
  have hs : 0 < (gauge ratioMinimizingBody (unitCirclePoint s))⁻¹ :=
    inv_pos.2 (disc_gauge_pos ratioMinimizingBody_properties.1 (unitCirclePoint_ne_zero s))
  have ht : 0 < (gauge ratioMinimizingBody (unitCirclePoint t))⁻¹ :=
    inv_pos.2 (disc_gauge_pos ratioMinimizingBody_properties.1 (unitCirclePoint_ne_zero t))
  have he : det2 (minimizerAngularBoundary s).val (minimizerAngularBoundary t).val =
      ((gauge ratioMinimizingBody (unitCirclePoint s))⁻¹ *
        (gauge ratioMinimizingBody (unitCirclePoint t))⁻¹) * Real.sin (t-s) := by
    rw [← unitCirclePoint_det]
    simp [minimizerAngularBoundary,minimizerRadialFoot,det2]; ring
  rw [he]
  exact mul_pos_iff_of_pos_left (mul_pos hs ht)

theorem minimizerAngularSuccessor_zero_upper :
    0 < (criticalMidpointNext (minimizerAngularMidpoint 0)).val 1 := by
  have hp := criticalMidpointNext_det_pos (minimizerAngularMidpoint 0)
  have hg : 0 < (gauge ratioMinimizingBody (point 1 0))⁻¹ :=
    inv_pos.2 (disc_gauge_pos ratioMinimizingBody_properties.1 (by
      intro h; have := congrArg (fun z : E => z 0) h; norm_num [point] at this))
  change 0 < det2 (minimizerRadialFoot (unitCirclePoint 0)) _ at hp
  simp [unitCirclePoint,minimizerRadialFoot,det2,point] at hp
  exact pos_of_mul_pos_right hp hg.le

theorem exists_minimizerFundamentalAngle :
    ∃ θ ∈ Ioo 0 Real.pi,
      minimizerAngularMidpoint θ=criticalMidpointNext (minimizerAngularMidpoint 0) := by
  obtain ⟨θ,hθ,he⟩ := minimizerAngularBoundary_upper_surjective
    (criticalMidpointSet_subset_frontier (criticalMidpointNext (minimizerAngularMidpoint 0)).property)
    minimizerAngularSuccessor_zero_upper
  exact ⟨θ,hθ,Subtype.ext he⟩

noncomputable def minimizerFundamentalAngle : ℝ := exists_minimizerFundamentalAngle.choose

theorem minimizerFundamentalAngle_mem : minimizerFundamentalAngle ∈ Ioo 0 Real.pi :=
  exists_minimizerFundamentalAngle.choose_spec.1

theorem minimizerFundamentalAngle_endpoint :
    minimizerAngularMidpoint minimizerFundamentalAngle=criticalMidpointNext (minimizerAngularMidpoint 0) :=
  exists_minimizerFundamentalAngle.choose_spec.2

noncomputable def minimizerFundamentalDuration : ℝ := minimizerDeterminantClock minimizerFundamentalAngle

theorem minimizerFundamentalDuration_pos : 0 < minimizerFundamentalDuration :=
  minimizerDeterminantClock_pos minimizerFundamentalAngle_mem.1

theorem minimizerFundamentalDuration_endpoint :
    minimizerBalancedBoundary 0 minimizerFundamentalDuration=minimizerBalancedBoundary 1 0 := by
  change (minimizerAngularMidpoint (minimizerAngularTime (minimizerDeterminantClock minimizerFundamentalAngle))).val =
    (criticalMidpointNext (minimizerAngularMidpoint (minimizerAngularTime 0))).val
  rw [minimizerAngularTime_clock,minimizerAngularTime_zero,minimizerFundamentalAngle_endpoint]

end Certificate.Packing
