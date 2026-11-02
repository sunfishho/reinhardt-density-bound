import Certificate.MinimizerFrameBoundary
import Certificate.TangentHexagonSides
import Certificate.StateLinearFrame

/-! The constructed state has strictly positive star coordinates. This is
derived from positive tangent transport and the strict neighboring support
inequality, without assuming a FrameTrajectory or its star conditions. -/
namespace Certificate.Packing
open Set Filter Topology MeasureTheory Confinement HVGeometry
set_option maxHeartbeats 300000

theorem criticalMidpointCurve_next_orientation {γ : ℝ → criticalMidpointSet}
    {v : E} {t : ℝ} (hd : HasDerivAt (fun s => (γ s).val) v t)
    (hp : 0 < det2 (γ t).val v) :
    0 < det2 (criticalMidpointNext (γ t)).val (criticalMidpointNextDerivative (γ t) v) := by
  rw [criticalMidpointCurve_successor_velocity_formula hd, det2_smul_right,
    criticalMidpointTangent_det, mul_one]
  exact mul_pos hp (criticalMidpointTangentScale_pos _)

theorem criticalMidpointCurve_next_contact {γ : ℝ → criticalMidpointSet}
    {v : E} {t : ℝ} (hd : HasDerivAt (fun s => (γ s).val) v t)
    (hp : 0 < det2 (γ t).val v) :
    0 < det2 v ((criticalMidpointNext (γ t)).val-(γ t).val) := by
  have he := criticalMidpoint_vector_decomposition (γ t) v
  rw [criticalMidpointCurve_velocity_tangent hd, zero_smul, zero_add] at he
  have hid : det2 v ((criticalMidpointNext (γ t)).val-(γ t).val) =
      det2 (γ t).val v * (1-minimizerGaugeGradient (γ t).val (criticalMidpointNext (γ t)).val) := by
    rw [← det_criticalMidpointTangent, ← criticalMidpointTangent_det (γ t)]
    conv_lhs => rw [he]
    simp only [det2, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  rw [hid]
  exact mul_pos hp (sub_pos.2 (criticalMidpointNext_forward_transverse_lt_one _))

theorem minimizerAngular_first_three_contacts (t : ℝ) :
    0 < det2 (minimizerAngularBalancedVelocity 0 t)
      (minimizerAngularBalancedCurve 1 t-minimizerAngularBalancedCurve 0 t) ∧
    0 < det2 (minimizerAngularBalancedVelocity 1 t)
      (minimizerAngularBalancedCurve 2 t-minimizerAngularBalancedCurve 1 t) ∧
    0 < det2 (minimizerAngularBalancedVelocity 2 t)
      (minimizerAngularBalancedCurve 3 t-minimizerAngularBalancedCurve 2 t) := by
  let γ := minimizerAngularMidpoint
  let η := fun s => criticalMidpointNext (γ s)
  let ζ := fun s => criticalMidpointNext (η s)
  have hd0 : HasDerivAt (fun s => (γ s).val) (minimizerAngularVelocity t) t :=
    hasDerivAt_minimizerAngularBoundary t
  have hd1 : HasDerivAt (fun s => (η s).val) (minimizerAngularSuccessorVelocity t) t :=
    hasDerivAt_criticalMidpointNext_comp hd0
  have hp0 : 0 < det2 (γ t).val (minimizerAngularVelocity t) := minimizerAngularVelocity_det_pos t
  have hp1 : 0 < det2 (η t).val (minimizerAngularSuccessorVelocity t) :=
    criticalMidpointCurve_next_orientation hd0 hp0
  have hζ : (fun s => (ζ s).val) = fun s => (η s).val-(γ s).val :=
    funext (fun s => criticalMidpointNext_balance (γ s))
  have hd2 : HasDerivAt (fun s => (ζ s).val)
      (minimizerAngularSuccessorVelocity t-minimizerAngularVelocity t) t := by
    rw [hζ]; exact hd1.sub hd0
  have he2 : criticalMidpointNextDerivative (η t) (minimizerAngularSuccessorVelocity t) =
      minimizerAngularSuccessorVelocity t-minimizerAngularVelocity t :=
    (hasDerivAt_criticalMidpointNext_comp hd1).unique hd2
  have hp2 : 0 < det2 (ζ t).val
      (minimizerAngularSuccessorVelocity t-minimizerAngularVelocity t) := by
    rw [← he2]
    exact criticalMidpointCurve_next_orientation hd1 hp1
  refine ⟨criticalMidpointCurve_next_contact hd0 hp0, ?_, ?_⟩
  · have hh := criticalMidpointCurve_next_contact hd1 hp1
    change 0 < det2 (minimizerAngularSuccessorVelocity t)
      ((criticalMidpointNext (criticalMidpointNext (γ t))).val-(η t).val) at hh
    rw [criticalMidpointNext_balance] at hh
    exact hh
  · have hh := criticalMidpointCurve_next_contact hd2 hp2
    change 0 < det2 (minimizerAngularSuccessorVelocity t-minimizerAngularVelocity t)
      ((criticalMidpointNext (criticalMidpointNext (criticalMidpointNext (γ t)))).val-
        (criticalMidpointNext (criticalMidpointNext (γ t))).val) at hh
    rw [criticalMidpointNext_third, criticalMidpointNext_balance] at hh
    exact hh

theorem minimizerBalanced_first_three_contacts (t : ℝ) :
    0 < det2 (minimizerBalancedVelocity 0 t)
      (minimizerBalancedBoundary 1 t-minimizerBalancedBoundary 0 t) ∧
    0 < det2 (minimizerBalancedVelocity 1 t)
      (minimizerBalancedBoundary 2 t-minimizerBalancedBoundary 1 t) ∧
    0 < det2 (minimizerBalancedVelocity 2 t)
      (minimizerBalancedBoundary 3 t-minimizerBalancedBoundary 2 t) := by
  have hh := minimizerAngular_first_three_contacts (minimizerAngularTime t)
  have hs : 0 < (minimizerDeterminantSpeed (minimizerAngularTime t))⁻¹ :=
    inv_pos.2 (minimizerDeterminantSpeed_pos _)
  have he (i j : Fin 6) : det2 (minimizerBalancedVelocity i t)
      (minimizerBalancedBoundary j t-minimizerBalancedBoundary i t) =
      (minimizerDeterminantSpeed (minimizerAngularTime t))⁻¹ *
      det2 (minimizerAngularBalancedVelocity i (minimizerAngularTime t))
        (minimizerAngularBalancedCurve j (minimizerAngularTime t)-
          minimizerAngularBalancedCurve i (minimizerAngularTime t)) := by
    simp [minimizerBalancedVelocity, minimizerNormalizedAngularVelocity,
      minimizerBalancedBoundary, det2]; ring
  rw [he,he,he]
  exact ⟨mul_pos hs hh.1,mul_pos hs hh.2.1,mul_pos hs hh.2.2⟩

theorem minimizerBalancedState_star_pos (t : ℝ) :
    0 < rho0 (minimizerBalancedState t) ∧ 0 < rho1 (minimizerBalancedState t) ∧
      0 < rho2 (minimizerBalancedState t) := by
  have he (i j : Fin 6) : det2 (minimizerBalancedVelocity i t)
      (minimizerBalancedBoundary j t-minimizerBalancedBoundary i t) =
      det2 (stateTangent (minimizerBalancedState t) (root i)) (root j-root i) := by
    rw [← minimizerBalancedState_root_velocity, ← minimizerBalancedState_root,
      ← minimizerBalancedState_root, ← stateAction_sub, det2_stateAction,
      (minimizerBalancedState_determinants t).1, one_mul]
  obtain ⟨h0,h1,h2⟩ := minimizerBalanced_first_three_contacts t
  rw [he] at h0 h1 h2
  obtain ⟨e0,e1,e2⟩ := adjacent_tangent_contacts (minimizerBalancedState t)
  change 0 < det2 (stateTangent (minimizerBalancedState t) s0) (s1-s0) at h0
  change 0 < det2 (stateTangent (minimizerBalancedState t) s1) (s2-s1) at h1
  change 0 < det2 (stateTangent (minimizerBalancedState t) s2) (-s0-s2) at h2
  rw [e0] at h0; rw [e1] at h1; rw [e2] at h2
  exact ⟨pos_of_mul_pos_right h0 (by positivity),pos_of_mul_pos_right h1 (by positivity),
    pos_of_mul_pos_right h2 (by positivity)⟩

theorem minimizerBalancedState_star_nonneg (t : ℝ) :
    0 ≤ rho0 (minimizerBalancedState t) ∧ 0 ≤ rho1 (minimizerBalancedState t) ∧
      0 ≤ rho2 (minimizerBalancedState t) :=
  ⟨(minimizerBalancedState_star_pos t).1.le,(minimizerBalancedState_star_pos t).2.1.le,
    (minimizerBalancedState_star_pos t).2.2.le⟩

end Certificate.Packing
