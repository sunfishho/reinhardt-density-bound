import Certificate.SuccessorVelocityRegularity
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! The strictly increasing clock for determinant-normalizing the balanced
boundary curves. This constructs the forward clock and the normalized tangent
vectors; an inverse parametrization and frame endpoint assembly are separate. -/
namespace Certificate.Packing
open Set Filter Topology MeasureTheory
open scoped NNReal
set_option maxHeartbeats 0

theorem ac_sqrt_pos {f : ℝ → ℝ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) (hp : ∀ t ∈ uIcc a b, 0 < f t) :
    AbsolutelyContinuousOnInterval (fun t => Real.sqrt (f t)) a b := by
  obtain ⟨t,ht,hmin⟩ := isCompact_uIcc.exists_isMinOn nonempty_uIcc hf.continuousOn
  obtain ⟨C,hC⟩ := hf.exists_bound
  have hft : 0 < f t := hp t ht
  have hc : ContDiffOn ℝ 1 Real.sqrt (Icc (f t) C) :=
    contDiffOn_id.sqrt (fun x hx => (hft.trans_le hx.1).ne')
  obtain ⟨L,hL⟩ := hc.exists_lipschitzOnWith (by norm_num) (convex_Icc _ _) isCompact_Icc
  exact ac_comp_lipschitzOn hf hL (fun x hx =>
    ⟨hmin hx,(le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hC x hx)⟩)

theorem minimizerAngular_adjacent_velocity_det_pos (t : ℝ) :
    0 < det2 (minimizerAngularVelocity t) (minimizerAngularSuccessorVelocity t) := by
  let p := minimizerAngularMidpoint t
  let v := minimizerAngularVelocity t
  let d := det2 p.val v
  have hd : 0 < d := minimizerAngularVelocity_det_pos t
  have he := criticalMidpoint_vector_decomposition p v
  rw [criticalMidpointCurve_velocity_tangent (γ := minimizerAngularMidpoint)
    (hasDerivAt_minimizerAngularBoundary t), zero_smul, zero_add] at he
  change v = d • criticalMidpointTangent p at he
  change 0 < det2 v (criticalMidpointNextDerivative p v)
  have hdeq : det2 v (criticalMidpointNextDerivative p v) =
      d^2 * det2 (criticalMidpointTangent p)
        (criticalMidpointNextDerivative p (criticalMidpointTangent p)) := by
    conv_lhs => rw [he, map_smul]
    simp only [det2, PiLp.smul_apply, smul_eq_mul]
    ring
  rw [hdeq]
  exact mul_pos (sq_pos_of_pos hd) (criticalMidpoint_adjacent_velocities_det_pos p)

theorem continuous_minimizerAngularVelocity : Continuous minimizerAngularVelocity := by
  have he : deriv (fun t => (minimizerAngularBoundary t).val) = minimizerAngularVelocity :=
    funext (fun t => (hasDerivAt_minimizerAngularBoundary t).deriv)
  rw [← he]
  exact (contDiff_one_iff_deriv.1 contDiff_minimizerAngularBoundary).2

theorem continuous_minimizerAngularSuccessorVelocity : Continuous minimizerAngularSuccessorVelocity := by
  have he : deriv (fun t => (minimizerBoundarySuccessor (minimizerAngularBoundary t)).val) =
      minimizerAngularSuccessorVelocity :=
    funext (fun t => (hasDerivAt_minimizerAngularSuccessor t).deriv)
  rw [← he]
  exact (contDiff_one_iff_deriv.1 contDiff_minimizerAngularSuccessor).2

noncomputable def minimizerDeterminantSpeed (t : ℝ) : ℝ :=
  Real.sqrt ((2 / Real.sqrt 3) *
    det2 (minimizerAngularVelocity t) (minimizerAngularSuccessorVelocity t))

theorem minimizerDeterminantSpeed_pos (t : ℝ) : 0 < minimizerDeterminantSpeed t :=
  Real.sqrt_pos.2 (mul_pos (by positivity) (minimizerAngular_adjacent_velocity_det_pos t))

theorem continuous_minimizerDeterminantSpeed : Continuous minimizerDeterminantSpeed :=
  ((continuous_const.mul (continuous_det2_comp continuous_minimizerAngularVelocity
    continuous_minimizerAngularSuccessorVelocity)).sqrt)

theorem minimizerDeterminantSpeed_ac (a b : ℝ) :
    AbsolutelyContinuousOnInterval minimizerDeterminantSpeed a b :=
  ac_sqrt_pos ((ac_plane_det (minimizerAngularVelocity_ac a b)
    (minimizerAngularSuccessorVelocity_ac a b)).const_mul (2 / Real.sqrt 3))
    (fun t _ => mul_pos (by positivity) (minimizerAngular_adjacent_velocity_det_pos t))

noncomputable def minimizerNormalizedAngularVelocity (i : Fin 6) (t : ℝ) : E :=
  (minimizerDeterminantSpeed t)⁻¹ • minimizerAngularBalancedVelocity i t

theorem minimizerNormalizedAngularVelocity_ac (i : Fin 6) (a b : ℝ) :
    AbsolutelyContinuousOnInterval (minimizerNormalizedAngularVelocity i) a b :=
  (ac_reciprocal_pos (minimizerDeterminantSpeed_ac a b)
    (fun t _ => minimizerDeterminantSpeed_pos t)).smul
    (minimizerAngularBalancedVelocity_ac i a b)

theorem minimizerNormalizedAngularVelocity_det (t : ℝ) :
    det2 (minimizerNormalizedAngularVelocity 0 t) (minimizerNormalizedAngularVelocity 1 t) =
      Real.sqrt 3 / 2 := by
  have hs := Real.sq_sqrt (show 0 ≤ (2 / Real.sqrt 3) *
      det2 (minimizerAngularVelocity t) (minimizerAngularSuccessorVelocity t) from
    (mul_pos (by positivity) (minimizerAngular_adjacent_velocity_det_pos t)).le)
  change minimizerDeterminantSpeed t ^ 2 = _ at hs
  have hp := (minimizerDeterminantSpeed_pos t).ne'
  have hr : Real.sqrt (3 : ℝ) ≠ 0 := by positivity
  have he : det2 (minimizerNormalizedAngularVelocity 0 t) (minimizerNormalizedAngularVelocity 1 t) =
      det2 (minimizerAngularVelocity t) (minimizerAngularSuccessorVelocity t) /
        minimizerDeterminantSpeed t ^ 2 := by
    simp [minimizerNormalizedAngularVelocity, minimizerAngularBalancedVelocity, det2, div_eq_mul_inv]
    ring
  rw [he]
  apply (div_eq_iff (pow_ne_zero 2 hp)).2
  rw [hs]
  field_simp

noncomputable def minimizerDeterminantClock (t : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..t, minimizerDeterminantSpeed s

theorem hasDerivAt_minimizerDeterminantClock (t : ℝ) :
    HasDerivAt minimizerDeterminantClock (minimizerDeterminantSpeed t) t :=
  intervalIntegral.integral_hasDerivAt_right
    (continuous_minimizerDeterminantSpeed.intervalIntegrable _ _)
    continuous_minimizerDeterminantSpeed.aestronglyMeasurable.stronglyMeasurableAtFilter
    continuous_minimizerDeterminantSpeed.continuousAt

theorem contDiff_minimizerDeterminantClock : ContDiff ℝ 1 minimizerDeterminantClock := by
  apply contDiff_one_iff_deriv.2
  refine ⟨fun t => (hasDerivAt_minimizerDeterminantClock t).differentiableAt,?_⟩
  have he : deriv minimizerDeterminantClock = minimizerDeterminantSpeed :=
    funext (fun t => (hasDerivAt_minimizerDeterminantClock t).deriv)
  rw [he]
  exact continuous_minimizerDeterminantSpeed

theorem strictMono_minimizerDeterminantClock : StrictMono minimizerDeterminantClock :=
  strictMono_of_deriv_pos (fun t => by
    rw [(hasDerivAt_minimizerDeterminantClock t).deriv]
    exact minimizerDeterminantSpeed_pos t)

theorem minimizerDeterminantClock_zero : minimizerDeterminantClock 0 = 0 := by
  simp [minimizerDeterminantClock]

theorem minimizerDeterminantClock_pos {t : ℝ} (ht : 0 < t) : 0 < minimizerDeterminantClock t := by
  simpa only [minimizerDeterminantClock_zero] using strictMono_minimizerDeterminantClock ht

end Certificate.Packing
