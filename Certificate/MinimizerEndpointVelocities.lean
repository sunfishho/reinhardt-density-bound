import Certificate.MinimizerStateStars
import Certificate.MinimizerFundamentalAngle

/-! The determinant normalization fixes the positive tangent speed uniquely.
It forces actual velocity matching at the fundamental endpoint, rather than
leaving a free positive scale in the terminal frame. -/
namespace Certificate.Packing
open Set Filter Topology MeasureTheory Confinement HVGeometry
set_option maxHeartbeats 300000

theorem minimizerBalanced_orientation (i : Fin 6) (t : ℝ) :
    0 < det2 (minimizerBalancedBoundary i t) (minimizerBalancedVelocity i t) := by
  rw [← minimizerBalancedState_root, ← minimizerBalancedState_root_velocity,
    det2_stateAction,(minimizerBalancedState_determinants t).1,one_mul]
  obtain ⟨h0,h1,h2⟩ := minimizerBalancedState_star_pos t
  exact root_area_integrands_pos _ h0 h1 h2 i

theorem criticalMidpoint_normalized_tangent_unique (p : criticalMidpointSet) (v w : E)
    (hv : minimizerGaugeGradient p.val v=0) (hw : minimizerGaugeGradient p.val w=0)
    (hpv : 0 < det2 p.val v) (hpw : 0 < det2 p.val w)
    (he : det2 v (criticalMidpointNextDerivative p v)=det2 w (criticalMidpointNextDerivative p w)) :
    v=w := by
  have hvd := criticalMidpoint_vector_decomposition p v
  have hwd := criticalMidpoint_vector_decomposition p w
  rw [hv,zero_smul,zero_add] at hvd
  rw [hw,zero_smul,zero_add] at hwd
  have hf (c : ℝ) : det2 (c • criticalMidpointTangent p)
      (criticalMidpointNextDerivative p (c • criticalMidpointTangent p)) =
      c^2 * det2 (criticalMidpointTangent p)
        (criticalMidpointNextDerivative p (criticalMidpointTangent p)) := by
    rw [map_smul]
    simp only [det2, PiLp.smul_apply, smul_eq_mul]
    ring
  have hve := congrArg (fun z => det2 z (criticalMidpointNextDerivative p z)) hvd
  have hwe := congrArg (fun z => det2 z (criticalMidpointNextDerivative p z)) hwd
  rw [hf] at hve hwe
  have hsq : (det2 p.val v)^2=(det2 p.val w)^2 := by
    apply mul_right_cancel₀ (criticalMidpoint_adjacent_velocities_det_pos p).ne'
    rw [← hve,← hwe,he]
  have hd : det2 p.val v=det2 p.val w := by nlinarith
  rw [hvd,hwd,hd]

noncomputable def minimizerTimedMidpoint (t : ℝ) : criticalMidpointSet :=
  minimizerAngularMidpoint (minimizerAngularTime t)

theorem hasDerivAt_minimizerTimedMidpoint (t : ℝ) :
    HasDerivAt (fun s => (minimizerTimedMidpoint s).val) (minimizerBalancedVelocity 0 t) t :=
  hasDerivAt_minimizerBalancedBoundary 0 t

theorem hasDerivAt_minimizerTimedNext (t : ℝ) :
    HasDerivAt (fun s => (criticalMidpointNext (minimizerTimedMidpoint s)).val)
      (minimizerBalancedVelocity 1 t) t := hasDerivAt_minimizerBalancedBoundary 1 t

theorem minimizerTimedNext_velocity (t : ℝ) :
    criticalMidpointNextDerivative (minimizerTimedMidpoint t) (minimizerBalancedVelocity 0 t)=
      minimizerBalancedVelocity 1 t :=
  (hasDerivAt_criticalMidpointNext_comp (hasDerivAt_minimizerTimedMidpoint t)).unique
    (hasDerivAt_minimizerTimedNext t)

theorem hasDerivAt_minimizerTimedSecond (t : ℝ) :
    HasDerivAt (fun s => (criticalMidpointNext (criticalMidpointNext (minimizerTimedMidpoint s))).val)
      (minimizerBalancedVelocity 2 t) t := by
  have he : (fun s => (criticalMidpointNext (criticalMidpointNext (minimizerTimedMidpoint s))).val)=
      minimizerBalancedBoundary 2 := funext (fun s => criticalMidpointNext_balance _)
  rw [he]
  exact hasDerivAt_minimizerBalancedBoundary 2 t

theorem minimizerTimedSecond_velocity (t : ℝ) :
    criticalMidpointNextDerivative (criticalMidpointNext (minimizerTimedMidpoint t))
      (minimizerBalancedVelocity 1 t)=minimizerBalancedVelocity 2 t :=
  (hasDerivAt_criticalMidpointNext_comp (hasDerivAt_minimizerTimedNext t)).unique
    (hasDerivAt_minimizerTimedSecond t)

theorem minimizerBalancedVelocity_balance (t : ℝ) :
    minimizerBalancedVelocity 2 t=minimizerBalancedVelocity 1 t-minimizerBalancedVelocity 0 t := by
  simp [minimizerBalancedVelocity,minimizerNormalizedAngularVelocity,minimizerAngularBalancedVelocity,smul_sub]

theorem minimizerBalancedVelocity_second_det (t : ℝ) :
    det2 (minimizerBalancedVelocity 1 t) (minimizerBalancedVelocity 2 t)=Real.sqrt 3/2 := by
  rw [minimizerBalancedVelocity_balance]
  have he : det2 (minimizerBalancedVelocity 1 t)
      (minimizerBalancedVelocity 1 t-minimizerBalancedVelocity 0 t)=
      det2 (minimizerBalancedVelocity 0 t) (minimizerBalancedVelocity 1 t) := by simp [det2]; ring
  rw [he,minimizerBalancedVelocity_det]

theorem minimizerTimedMidpoint_endpoint :
    minimizerTimedMidpoint minimizerFundamentalDuration=criticalMidpointNext (minimizerTimedMidpoint 0) := by
  apply Subtype.ext
  exact minimizerFundamentalDuration_endpoint

theorem minimizerFundamentalVelocity_endpoint :
    minimizerBalancedVelocity 0 minimizerFundamentalDuration=minimizerBalancedVelocity 1 0 := by
  let T := minimizerFundamentalDuration
  let p := criticalMidpointNext (minimizerTimedMidpoint 0)
  have hp : minimizerTimedMidpoint T=p := minimizerTimedMidpoint_endpoint
  apply criticalMidpoint_normalized_tangent_unique p
  · rw [← hp]; exact criticalMidpointCurve_velocity_tangent (hasDerivAt_minimizerTimedMidpoint T)
  · exact criticalMidpointCurve_velocity_tangent (hasDerivAt_minimizerTimedNext 0)
  · rw [← hp]; exact minimizerBalanced_orientation 0 T
  · exact minimizerBalanced_orientation 1 0
  · change det2 _ (criticalMidpointNextDerivative p _) = _
    rw [← hp,minimizerTimedNext_velocity,hp]
    change det2 _ _=det2 _ (criticalMidpointNextDerivative (criticalMidpointNext (minimizerTimedMidpoint 0)) _)
    rw [minimizerTimedSecond_velocity,minimizerBalancedVelocity_det,minimizerBalancedVelocity_second_det]

theorem minimizerFundamentalNextVelocity_endpoint :
    minimizerBalancedVelocity 1 minimizerFundamentalDuration=minimizerBalancedVelocity 2 0 := by
  rw [← minimizerTimedNext_velocity,minimizerTimedMidpoint_endpoint,
    minimizerFundamentalVelocity_endpoint,minimizerTimedSecond_velocity]

theorem minimizerFundamentalNextPosition_endpoint :
    minimizerBalancedBoundary 1 minimizerFundamentalDuration=minimizerBalancedBoundary 2 0 := by
  change (criticalMidpointNext (minimizerTimedMidpoint minimizerFundamentalDuration)).val=_
  rw [minimizerTimedMidpoint_endpoint,criticalMidpointNext_balance]
  rfl

end Certificate.Packing
