import Certificate.MinimizerUniformRegularity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! An explicit regular angular boundary curve, with absolutely continuous
supporting tangents. Determinant-normalizing its time variable and choosing
the single fundamental arc remain separate constructions. -/
namespace Certificate.Packing
open Set Filter Topology MeasureTheory
open scoped NNReal
set_option maxHeartbeats 0

noncomputable def unitCirclePoint (t : ℝ) : E :=
  Real.cos t • point 1 0 + Real.sin t • point 0 1

noncomputable def unitCircleVelocity (t : ℝ) : E :=
  (-Real.sin t) • point 1 0 + Real.cos t • point 0 1

lemma unitCirclePoint_norm (t : ℝ) : ‖unitCirclePoint t‖ = 1 := by
  have he : ‖unitCirclePoint t‖^2 = 1 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simpa [unitCirclePoint, Fin.sum_univ_two, point] using Real.cos_sq_add_sin_sq t
  nlinarith [norm_nonneg (unitCirclePoint t)]

lemma unitCirclePoint_mem_sphere (t : ℝ) : unitCirclePoint t ∈ Metric.sphere 0 1 := by
  simpa only [Metric.mem_sphere, dist_zero_right] using unitCirclePoint_norm t

lemma unitCirclePoint_ne_zero (t : ℝ) : unitCirclePoint t ≠ 0 := by
  intro he
  have hh := unitCirclePoint_norm t
  simp [he] at hh

lemma unitCirclePoint_velocity_det (t : ℝ) : det2 (unitCirclePoint t) (unitCircleVelocity t) = 1 := by
  simpa [unitCirclePoint, unitCircleVelocity, det2, point, pow_two] using Real.cos_sq_add_sin_sq t

lemma hasDerivAt_unitCirclePoint (t : ℝ) : HasDerivAt unitCirclePoint (unitCircleVelocity t) t :=
  ((Real.hasDerivAt_cos t).smul_const (point 1 0)).add
    ((Real.hasDerivAt_sin t).smul_const (point 0 1))

lemma contDiff_unitCirclePoint : ContDiff ℝ 1 unitCirclePoint := by
  unfold unitCirclePoint
  fun_prop

lemma unitCirclePoint_lipschitz : ∃ L : ℝ≥0, LipschitzWith L unitCirclePoint := by
  let A := (ContinuousLinearMap.id ℝ ℝ).smulRight (point 1 0)
  let B := (ContinuousLinearMap.id ℝ ℝ).smulRight (point 0 1)
  have hA := A.lipschitz.comp Real.lipschitzWith_cos
  have hB := B.lipschitz.comp Real.lipschitzWith_sin
  refine ⟨‖A‖₊+‖B‖₊,?_⟩
  convert! hA.add hB using 1 <;> simp [unitCirclePoint, A, B, Function.comp_def]

noncomputable def minimizerAngularBoundary (t : ℝ) : frontier ratioMinimizingBody :=
  ⟨minimizerRadialFoot (unitCirclePoint t), minimizerRadialFoot_frontier (unitCirclePoint_ne_zero t)⟩

noncomputable def minimizerAngularVelocity (t : ℝ) : E :=
  minimizerRadialVelocity (unitCirclePoint t) (unitCircleVelocity t)

theorem hasDerivAt_minimizerAngularBoundary (t : ℝ) :
    HasDerivAt (fun s => (minimizerAngularBoundary s).val) (minimizerAngularVelocity t) t :=
  hasDerivAt_minimizerRadialFoot_comp (hasDerivAt_unitCirclePoint t) (unitCirclePoint_ne_zero t)

theorem minimizerAngularVelocity_det_pos (t : ℝ) :
    0 < det2 (minimizerAngularBoundary t).val (minimizerAngularVelocity t) := by
  change 0 < det2 (minimizerRadialFoot (unitCirclePoint t))
    (minimizerRadialVelocity (unitCirclePoint t) (unitCircleVelocity t))
  rw [minimizerRadialVelocity_det, unitCirclePoint_velocity_det, mul_one]
  exact sq_pos_of_pos (inv_pos.2 (disc_gauge_pos ratioMinimizingBody_properties.1
    (unitCirclePoint_ne_zero t)))

theorem minimizerAngularVelocity_ne_zero (t : ℝ) : minimizerAngularVelocity t ≠ 0 :=
  minimizerRadialVelocity_ne_zero (unitCirclePoint_ne_zero t)
    (by rw [unitCirclePoint_velocity_det]; norm_num)

theorem contDiff_minimizerAngularBoundary :
    ContDiff ℝ 1 (fun t => (minimizerAngularBoundary t).val) := by
  apply contDiff_iff_contDiffAt.2
  intro t
  exact (contDiffOn_minimizerRadialFoot.contDiffAt
    (isOpen_ne.mem_nhds (unitCirclePoint_ne_zero t))).comp t
      contDiff_unitCirclePoint.contDiffAt

theorem minimizerAngularBoundary_lipschitz :
    ∃ L : ℝ≥0, LipschitzWith L minimizerAngularBoundary := by
  obtain ⟨A,hA⟩ := discRadialHomeomorph_lipschitz_sphere ratioMinimizingBody_properties.1
  obtain ⟨B,hB⟩ := unitCirclePoint_lipschitz
  refine ⟨A*B,LipschitzWith.of_dist_le_mul (fun s t => ?_)⟩
  have hh := hA.dist_le_mul (unitCirclePoint s) (unitCirclePoint_mem_sphere s)
    (unitCirclePoint t) (unitCirclePoint_mem_sphere t)
  rw [discRadialHomeomorph_on_sphere ratioMinimizingBody_properties.1 (unitCirclePoint_mem_sphere s),
    discRadialHomeomorph_on_sphere ratioMinimizingBody_properties.1 (unitCirclePoint_mem_sphere t)] at hh
  have hmul := mul_le_mul_of_nonneg_left (hB.dist_le_mul s t) A.coe_nonneg
  calc
    dist (minimizerAngularBoundary s) (minimizerAngularBoundary t) ≤
        A * dist (unitCirclePoint s) (unitCirclePoint t) := hh
    _ ≤ A * (B * dist s t) := hmul
    _ = (A*B:ℝ≥0) * dist s t := by push_cast; ring

theorem minimizerAngularBoundary_tangent_ac (a b : ℝ) :
    AbsolutelyContinuousOnInterval
      (fun t => minimizerBoundaryTangent (minimizerAngularBoundary t)) a b := by
  obtain ⟨L,hL⟩ := minimizerAngularBoundary_lipschitz
  exact minimizerBoundary_tangent_ac_of_lipschitz hL.lipschitzOnWith

theorem minimizerAngularBoundary_gradient_ac (a b : ℝ) :
    AbsolutelyContinuousOnInterval
      (fun t => minimizerGaugeGradient (minimizerAngularBoundary t).val) a b := by
  obtain ⟨L,hL⟩ := minimizerAngularBoundary_lipschitz
  exact minimizerBoundary_gradient_ac_of_lipschitz hL.lipschitzOnWith

noncomputable def minimizerAngularSpeed (t : ℝ) : ℝ :=
  (gauge ratioMinimizingBody (unitCirclePoint t))⁻¹^2

lemma contDiff_minimizerAngularSpeed : ContDiff ℝ 1 minimizerAngularSpeed := by
  apply contDiff_iff_contDiffAt.2
  intro t
  have hg := (contDiffOn_minimizerGauge.contDiffAt
    (isOpen_ne.mem_nhds (unitCirclePoint_ne_zero t))).comp t
      contDiff_unitCirclePoint.contDiffAt
  exact (hg.inv (disc_gauge_pos ratioMinimizingBody_properties.1 (unitCirclePoint_ne_zero t)).ne').pow 2

lemma minimizerAngularVelocity_eq_speed_tangent (t : ℝ) :
    minimizerAngularVelocity t = minimizerAngularSpeed t •
      minimizerBoundaryTangent (minimizerAngularBoundary t) := by
  let p := criticalMidpointBoundaryHomeomorph.symm (minimizerAngularBoundary t)
  have he := criticalMidpoint_vector_decomposition p (minimizerAngularVelocity t)
  have ht := criticalMidpointCurve_velocity_tangent
    (γ := fun s => criticalMidpointBoundaryHomeomorph.symm (minimizerAngularBoundary s))
    (hasDerivAt_minimizerAngularBoundary t)
  change minimizerGaugeGradient p.val (minimizerAngularVelocity t) = 0 at ht
  rw [ht,zero_smul,zero_add] at he
  change minimizerAngularVelocity t =
    det2 (minimizerRadialFoot (unitCirclePoint t)) (minimizerAngularVelocity t) •
      minimizerBoundaryTangent (minimizerAngularBoundary t) at he
  simpa only [minimizerAngularSpeed,minimizerAngularVelocity,minimizerRadialVelocity_det,
    unitCirclePoint_velocity_det,mul_one] using he

/-- The actual velocity, not just its direction, is absolutely continuous
on every bounded parameter interval. -/
theorem minimizerAngularVelocity_ac (a b : ℝ) :
    AbsolutelyContinuousOnInterval minimizerAngularVelocity a b := by
  have hs := contDiff_minimizerAngularSpeed.contDiffOn.absolutelyContinuousOnInterval (a := a) (b := b)
  have hh := hs.smul (minimizerAngularBoundary_tangent_ac a b)
  have he : minimizerAngularVelocity = fun t => minimizerAngularSpeed t •
      minimizerBoundaryTangent (minimizerAngularBoundary t) :=
    funext minimizerAngularVelocity_eq_speed_tangent
  rwa [he]

/-- The successor produces a regular C1 neighboring curve for the explicit
angular parametrization; its fixed determinant and balance are already proved. -/
theorem contDiff_minimizerAngularSuccessor :
    ContDiff ℝ 1 (fun t => (minimizerBoundarySuccessor (minimizerAngularBoundary t)).val) := by
  apply contDiff_iff_contDiffAt.2
  intro t
  exact contDiffAt_minimizerBoundarySuccessor_comp contDiff_minimizerAngularBoundary.contDiffAt

theorem minimizerAngularSuccessor_regular (t : ℝ) :
    ∃ v : E, HasDerivAt (fun s => (minimizerBoundarySuccessor (minimizerAngularBoundary s)).val) v t ∧ v ≠ 0 :=
  minimizerBoundarySuccessor_regular_curve (hasDerivAt_minimizerAngularBoundary t)
    (minimizerAngularVelocity_ne_zero t)

end Certificate.Packing
