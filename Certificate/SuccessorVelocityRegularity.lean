import Certificate.BoundaryAbsoluteContinuity
import Certificate.MinimizerAngularBoundary

/-! The critical successor transports absolute continuity of actual velocities.
This supplies velocity regularity for all six balanced companion curves. -/
namespace Certificate.Packing
open Set Filter Topology MeasureTheory
open scoped NNReal
set_option maxHeartbeats 0

theorem criticalMidpointCurve_lipschitzOn {γ : ℝ → criticalMidpointSet}
    (hγ : ContDiff ℝ 1 (fun t => (γ t).val)) (a b : ℝ) :
    ∃ L : ℝ≥0, LipschitzOnWith L γ (uIcc a b) := by
  obtain ⟨L,hL⟩ := hγ.contDiffOn.exists_lipschitzOnWith (by norm_num)
    (convex_Icc _ _) isCompact_Icc
  exact ⟨L,LipschitzOnWith.of_dist_le_mul (fun x hx y hy => hL.dist_le_mul x hx y hy)⟩

theorem criticalMidpointCurve_gradient_ac {γ : ℝ → criticalMidpointSet}
    (hγ : ContDiff ℝ 1 (fun t => (γ t).val)) (a b : ℝ) :
    AbsolutelyContinuousOnInterval (fun t => minimizerGaugeGradient (γ t).val) a b := by
  obtain ⟨L,hL⟩ := criticalMidpointCurve_lipschitzOn hγ a b
  obtain ⟨K,hK⟩ := criticalMidpoint_gradient_lipschitz
  exact (hK.comp_lipschitzOnWith hL).absolutelyContinuousOnInterval

theorem criticalMidpointCurve_tangent_ac {γ : ℝ → criticalMidpointSet}
    (hγ : ContDiff ℝ 1 (fun t => (γ t).val)) (a b : ℝ) :
    AbsolutelyContinuousOnInterval (fun t => criticalMidpointTangent (γ t)) a b := by
  obtain ⟨L,hL⟩ := criticalMidpointCurve_lipschitzOn hγ a b
  obtain ⟨K,hK⟩ := criticalMidpoint_tangent_lipschitz
  exact (hK.comp_lipschitzOnWith hL).absolutelyContinuousOnInterval

theorem criticalMidpointCurve_tangentScale_ac {γ : ℝ → criticalMidpointSet}
    (hγ : ContDiff ℝ 1 (fun t => (γ t).val)) (a b : ℝ) :
    AbsolutelyContinuousOnInterval (fun t => criticalMidpointTangentScale (γ t)) a b := by
  have hq : ContDiff ℝ 1 (fun t => (criticalMidpointNext (γ t)).val) :=
    contDiff_iff_contDiffAt.2 (fun t => contDiffAt_criticalMidpointNext_comp hγ.contDiffAt)
  have hpac := hγ.contDiffOn.absolutelyContinuousOnInterval (a := a) (b := b)
  have hqac := hq.contDiffOn.absolutelyContinuousOnInterval (a := a) (b := b)
  have hnum := ac_linear_form_eval (criticalMidpointCurve_gradient_ac hγ a b) hqac
  have hden := ac_linear_form_eval (criticalMidpointCurve_gradient_ac hq a b) hpac
  have hinv := ac_reciprocal_pos hden (fun t _ => criticalMidpointNext_transverse (γ t))
  convert! hnum.mul hinv using 1

theorem criticalMidpointCurve_successor_velocity_formula {γ : ℝ → criticalMidpointSet}
    {v : E} {t : ℝ} (hγ : HasDerivAt (fun s => (γ s).val) v t) :
    criticalMidpointNextDerivative (γ t) v =
      (det2 (γ t).val v * criticalMidpointTangentScale (γ t)) •
        criticalMidpointTangent (criticalMidpointNext (γ t)) := by
  have he := criticalMidpoint_vector_decomposition (γ t) v
  rw [criticalMidpointCurve_velocity_tangent hγ, zero_smul, zero_add] at he
  calc
    _ = det2 (γ t).val v •
        criticalMidpointNextDerivative (γ t) (criticalMidpointTangent (γ t)) := by
      conv_lhs => rw [he, map_smul]
    _ = _ := by rw [criticalMidpointNextDerivative_tangent, mul_smul]

theorem criticalMidpointCurve_successor_velocity_ac {γ : ℝ → criticalMidpointSet}
    {v : ℝ → E} {a b : ℝ}
    (hγ : ContDiff ℝ 1 (fun t => (γ t).val))
    (hv : ∀ t, HasDerivAt (fun s => (γ s).val) (v t) t)
    (hac : AbsolutelyContinuousOnInterval v a b) :
    AbsolutelyContinuousOnInterval
      (fun t => criticalMidpointNextDerivative (γ t) (v t)) a b := by
  have hq : ContDiff ℝ 1 (fun t => (criticalMidpointNext (γ t)).val) :=
    contDiff_iff_contDiffAt.2 (fun t => contDiffAt_criticalMidpointNext_comp hγ.contDiffAt)
  have hd := ac_plane_det hγ.contDiffOn.absolutelyContinuousOnInterval hac
  have hh := (hd.mul (criticalMidpointCurve_tangentScale_ac hγ a b)).smul
    (criticalMidpointCurve_tangent_ac hq a b)
  convert! hh using 1
  funext t
  exact criticalMidpointCurve_successor_velocity_formula (hv t)

noncomputable def minimizerAngularMidpoint (t : ℝ) : criticalMidpointSet :=
  criticalMidpointBoundaryHomeomorph.symm (minimizerAngularBoundary t)

noncomputable def minimizerAngularSuccessorVelocity (t : ℝ) : E :=
  criticalMidpointNextDerivative (minimizerAngularMidpoint t) (minimizerAngularVelocity t)

theorem hasDerivAt_minimizerAngularSuccessor (t : ℝ) :
    HasDerivAt (fun s => (minimizerBoundarySuccessor (minimizerAngularBoundary s)).val)
      (minimizerAngularSuccessorVelocity t) t :=
  hasDerivAt_criticalMidpointNext_comp (γ := minimizerAngularMidpoint)
    (hasDerivAt_minimizerAngularBoundary t)

theorem minimizerAngularSuccessorVelocity_ac (a b : ℝ) :
    AbsolutelyContinuousOnInterval minimizerAngularSuccessorVelocity a b :=
  criticalMidpointCurve_successor_velocity_ac (γ := minimizerAngularMidpoint)
    contDiff_minimizerAngularBoundary hasDerivAt_minimizerAngularBoundary
    (minimizerAngularVelocity_ac a b)

theorem minimizerAngularSuccessorVelocity_ne_zero (t : ℝ) :
    minimizerAngularSuccessorVelocity t ≠ 0 :=
  (criticalMidpointNext_regular_curve (γ := minimizerAngularMidpoint)
    (hasDerivAt_minimizerAngularBoundary t) (minimizerAngularVelocity_ne_zero t)).2

noncomputable def minimizerAngularBalancedCurve (i : Fin 6) (t : ℝ) : E :=
  criticalMidpointConfiguration (minimizerAngularMidpoint t) i

noncomputable def minimizerAngularBalancedVelocity (i : Fin 6) (t : ℝ) : E :=
  ![minimizerAngularVelocity t, minimizerAngularSuccessorVelocity t,
    minimizerAngularSuccessorVelocity t-minimizerAngularVelocity t,
    -minimizerAngularVelocity t, -minimizerAngularSuccessorVelocity t,
    minimizerAngularVelocity t-minimizerAngularSuccessorVelocity t] i

theorem hasDerivAt_minimizerAngularBalancedCurve (i : Fin 6) (t : ℝ) :
    HasDerivAt (minimizerAngularBalancedCurve i) (minimizerAngularBalancedVelocity i t) t := by
  have hp := hasDerivAt_minimizerAngularBoundary t
  have hq := hasDerivAt_minimizerAngularSuccessor t
  fin_cases i
  · exact hp
  · exact hq
  · exact hq.sub hp
  · exact hp.neg
  · exact hq.neg
  · exact hp.sub hq

theorem minimizerAngularBalancedVelocity_ac (i : Fin 6) (a b : ℝ) :
    AbsolutelyContinuousOnInterval (minimizerAngularBalancedVelocity i) a b := by
  have hp := minimizerAngularVelocity_ac a b
  have hq := minimizerAngularSuccessorVelocity_ac a b
  fin_cases i
  · exact hp
  · exact hq
  · exact hq.sub hp
  · exact hp.neg
  · exact hq.neg
  · exact hp.sub hq

theorem contDiff_minimizerAngularBalancedCurve (i : Fin 6) :
    ContDiff ℝ 1 (minimizerAngularBalancedCurve i) :=
  contDiff_iff_contDiffAt.2 (fun t =>
    contDiffAt_criticalMidpointConfiguration_comp (γ := minimizerAngularMidpoint)
      contDiff_minimizerAngularBoundary.contDiffAt i)

theorem minimizerAngularBalancedCurve_frontier (i : Fin 6) (t : ℝ) :
    minimizerAngularBalancedCurve i t ∈ frontier ratioMinimizingBody :=
  criticalMidpointSet_subset_frontier (criticalMidpointConfiguration_mem (minimizerAngularMidpoint t) i)

end Certificate.Packing
