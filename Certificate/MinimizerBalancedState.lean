import Certificate.MinimizerBalancedRegularity
import Certificate.FrameTrajectory

/-! The actual determinant-normalized matrix state, assembled from the two
neighboring boundary curves and their velocities. The fundamental-arc endpoint
and trace conditions are not included in this construction. -/
namespace Certificate.Packing
open Set Filter Topology MeasureTheory Confinement
open scoped NNReal
set_option maxHeartbeats 300000

theorem hasDerivAt_plane_coordinate {f : ℝ → E} {v : E} {t : ℝ}
    (hf : HasDerivAt f v t) (i : Fin 2) : HasDerivAt (fun s => f s i) (v i) t :=
  (coord i).toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t hf

theorem hasDerivAt_plane_det {f g : ℝ → E} {v w : E} {t : ℝ}
    (hf : HasDerivAt f v t) (hg : HasDerivAt g w t) :
    HasDerivAt (fun s => det2 (f s) (g s)) (det2 v (g t)+det2 (f t) w) t := by
  convert! (((hasDerivAt_plane_coordinate hf 0).mul (hasDerivAt_plane_coordinate hg 1)).sub
    ((hasDerivAt_plane_coordinate hf 1).mul (hasDerivAt_plane_coordinate hg 0))) using 1
  simp only [det2]
  ring

noncomputable def minimizerFrameColumn (t : ℝ) : E :=
  (Real.sqrt 3)⁻¹ • ((2 : ℝ) • minimizerBalancedBoundary 1 t-minimizerBalancedBoundary 0 t)

noncomputable def minimizerFrameColumnVelocity (t : ℝ) : E :=
  (Real.sqrt 3)⁻¹ • ((2 : ℝ) • minimizerBalancedVelocity 1 t-minimizerBalancedVelocity 0 t)

theorem hasDerivAt_minimizerFrameColumn (t : ℝ) :
    HasDerivAt minimizerFrameColumn (minimizerFrameColumnVelocity t) t := by
  convert! (((hasDerivAt_minimizerBalancedBoundary 1 t).const_smul (2 : ℝ)).sub
    (hasDerivAt_minimizerBalancedBoundary 0 t)).const_smul ((Real.sqrt 3)⁻¹) using 1

theorem minimizerFrameColumn_ac (a b : ℝ) :
    AbsolutelyContinuousOnInterval minimizerFrameColumn a b :=
  (((minimizerBalancedBoundary_ac 1 a b).const_smul (2 : ℝ)).sub
    (minimizerBalancedBoundary_ac 0 a b)).const_smul _

theorem minimizerFrameColumnVelocity_ac (a b : ℝ) :
    AbsolutelyContinuousOnInterval minimizerFrameColumnVelocity a b :=
  (((minimizerBalancedVelocity_ac 1 a b).const_smul (2 : ℝ)).sub
    (minimizerBalancedVelocity_ac 0 a b)).const_smul _

theorem det2_normalized_second_column (p q : E) (h : det2 p q=Real.sqrt 3/2) :
    det2 p ((Real.sqrt 3)⁻¹ • ((2 : ℝ) • q-p))=1 := by
  have hs : Real.sqrt (3 : ℝ) ≠ 0 := by positivity
  calc
    _ = (2/Real.sqrt 3)*det2 p q := by simp [det2, div_eq_mul_inv]; ring
    _ = 1 := by rw [h]; field_simp

theorem minimizerFrame_position_det (t : ℝ) :
    det2 (minimizerBalancedBoundary 0 t) (minimizerFrameColumn t)=1 :=
  det2_normalized_second_column _ _ (minimizerBalancedBoundary_fixed_det t)

theorem minimizerFrame_velocity_det (t : ℝ) :
    det2 (minimizerBalancedVelocity 0 t) (minimizerFrameColumnVelocity t)=1 :=
  det2_normalized_second_column _ _ (minimizerBalancedVelocity_det t)

theorem minimizerFrame_mixed_det (t : ℝ) :
    det2 (minimizerBalancedVelocity 0 t) (minimizerFrameColumn t)+
      det2 (minimizerBalancedBoundary 0 t) (minimizerFrameColumnVelocity t)=0 := by
  have hd := hasDerivAt_plane_det (hasDerivAt_minimizerBalancedBoundary 0 t)
    (hasDerivAt_minimizerFrameColumn t)
  have he : (fun s => det2 (minimizerBalancedBoundary 0 s) (minimizerFrameColumn s)) =
      fun _ : ℝ => (1 : ℝ) := funext minimizerFrame_position_det
  rw [he] at hd
  exact hd.unique (hasDerivAt_const t 1)

noncomputable def minimizerBalancedState (t : ℝ) : State where
  g11 := minimizerBalancedBoundary 0 t 0
  g12 := minimizerFrameColumn t 0
  g21 := minimizerBalancedBoundary 0 t 1
  g22 := minimizerFrameColumn t 1
  a := det2 (minimizerBalancedVelocity 0 t) (minimizerFrameColumn t)
  p := (det2 (minimizerFrameColumnVelocity t) (minimizerFrameColumn t)+
    det2 (minimizerBalancedBoundary 0 t) (minimizerBalancedVelocity 0 t))/2
  h := (det2 (minimizerBalancedBoundary 0 t) (minimizerBalancedVelocity 0 t)-
    det2 (minimizerFrameColumnVelocity t) (minimizerFrameColumn t))/2

theorem minimizerBalancedState_determinants (t : ℝ) :
    (minimizerBalancedState t).determinantConstraints := by
  constructor
  · simpa only [det2, minimizerBalancedState, mul_comm] using minimizerFrame_position_det t
  · have hi := det2_pair_identity (minimizerBalancedBoundary 0 t) (minimizerFrameColumn t)
      (minimizerBalancedVelocity 0 t) (minimizerFrameColumnVelocity t)
    rw [minimizerFrame_position_det, minimizerFrame_velocity_det] at hi
    have hm := minimizerFrame_mixed_det t
    have hswap (x y : E) : det2 x y = -det2 y x := by simp [det2]; ring
    rw [hswap (minimizerFrameColumn t) (minimizerFrameColumnVelocity t),
      hswap (minimizerFrameColumn t) (minimizerBalancedVelocity 0 t)] at hi
    have he : det2 (minimizerBalancedBoundary 0 t) (minimizerFrameColumnVelocity t) =
        -det2 (minimizerBalancedVelocity 0 t) (minimizerFrameColumn t) := by linarith only [hm]
    rw [he] at hi
    dsimp [minimizerBalancedState]
    nlinarith only [hi]

theorem minimizerBalancedState_coordinates_ac (i : Fin 8) (a b : ℝ) :
    AbsolutelyContinuousOnInterval (fun t => (minimizerBalancedState t).coordinates i) a b := by
  have hp := minimizerBalancedBoundary_ac 0 a b
  have hb := minimizerFrameColumn_ac a b
  have hv := minimizerBalancedVelocity_ac 0 a b
  have hd := minimizerFrameColumnVelocity_ac a b
  have hA := ac_plane_det hv hb
  have hB := ac_plane_det hd hb
  have hC := ac_plane_det hp hv
  fin_cases i
  · exact ac_plane_coordinate hp 0
  · exact ac_plane_coordinate hb 0
  · exact ac_plane_coordinate hp 1
  · exact ac_plane_coordinate hb 1
  · exact hA
  · convert! (hB.add hC).const_mul (1/2 : ℝ) using 1
    funext t
    simp [State.coordinates, minimizerBalancedState]
    ring
  · convert! (hC.sub hB).const_mul (1/2 : ℝ) using 1
    funext t
    simp [State.coordinates, minimizerBalancedState]
    ring
  · exact contDiffOn_const.absolutelyContinuousOnInterval

lemma det_one_basis_decomposition (p b v : E) (hd : det2 p b=1) :
    v=det2 v b • p+det2 p v • b := by
  have he : det2 p b • v=det2 v b • p+det2 p v • b := by
    ext i; fin_cases i <;> simp [det2] <;> ring
  simpa only [hd, one_smul] using he

theorem minimizerBalancedState_group_derivative (t : ℝ) :
    GroupDerivative minimizerBalancedState t := by
  have hv := det_one_basis_decomposition (minimizerBalancedBoundary 0 t) (minimizerFrameColumn t)
    (minimizerBalancedVelocity 0 t) (minimizerFrame_position_det t)
  have hd := det_one_basis_decomposition (minimizerBalancedBoundary 0 t) (minimizerFrameColumn t)
    (minimizerFrameColumnVelocity t) (minimizerFrame_position_det t)
  have hm := minimizerFrame_mixed_det t
  have he : det2 (minimizerBalancedBoundary 0 t) (minimizerFrameColumnVelocity t) =
      -det2 (minimizerBalancedVelocity 0 t) (minimizerFrameColumn t) := by linarith
  rw [he] at hd
  have hv0 := congrArg (fun x : E => x 0) hv
  have hv1 := congrArg (fun x : E => x 1) hv
  have hd0 := congrArg (fun x : E => x 0) hd
  have hd1 := congrArg (fun x : E => x 1) hd
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at hv0 hv1 hd0 hd1
  constructor
  · convert! hasDerivAt_plane_coordinate (hasDerivAt_minimizerBalancedBoundary 0 t) 0 using 1
    dsimp [minimizerBalancedState]; linear_combination -hv0
  · convert! hasDerivAt_plane_coordinate (hasDerivAt_minimizerFrameColumn t) 0 using 1
    dsimp [minimizerBalancedState]; linear_combination -hd0
  · convert! hasDerivAt_plane_coordinate (hasDerivAt_minimizerBalancedBoundary 0 t) 1 using 1
    dsimp [minimizerBalancedState]; linear_combination -hv1
  · convert! hasDerivAt_plane_coordinate (hasDerivAt_minimizerFrameColumn t) 1 using 1
    dsimp [minimizerBalancedState]; linear_combination -hd1

end Certificate.Packing
