import Certificate.MinimizerStateStars

/-! Constant left normalization of a state path by its initial determinant-one
matrix. The velocity coordinates and star signs are unchanged. -/
namespace Certificate.Packing
open Set Filter Topology MeasureTheory Confinement HVGeometry
set_option maxHeartbeats 300000

noncomputable def normalizeStateAt (base x : State) : State where
  g11 := base.g22*x.g11-base.g12*x.g21
  g12 := base.g22*x.g12-base.g12*x.g22
  g21 := -base.g21*x.g11+base.g11*x.g21
  g22 := -base.g21*x.g12+base.g11*x.g22
  a := x.a
  p := x.p
  h := x.h

theorem normalizeStateAt_initial (x : State) (hd : x.g11*x.g22-x.g12*x.g21=1) :
    normalizeStateAt x x=initialState (normalizeStateAt x x) := by
  apply state_ext <;> dsimp [normalizeStateAt,initialState] <;> nlinarith only [hd]

theorem normalizeStateAt_determinants (base x : State)
    (hb : base.g11*base.g22-base.g12*base.g21=1) (hx : x.determinantConstraints) :
    (normalizeStateAt base x).determinantConstraints := by
  refine ⟨?_,hx.2⟩
  change (base.g22*x.g11-base.g12*x.g21)*(-base.g21*x.g12+base.g11*x.g22)-
    (base.g22*x.g12-base.g12*x.g22)*(-base.g21*x.g11+base.g11*x.g21)=1
  calc
    _ = (base.g11*base.g22-base.g12*base.g21)*(x.g11*x.g22-x.g12*x.g21) := by ring
    _ = 1 := by rw [hb,hx.1,mul_one]

theorem normalizeStateAt_group_derivative (base : State) {x : ℝ → State} {t : ℝ}
    (hd : GroupDerivative x t) : GroupDerivative (fun s => normalizeStateAt base (x s)) t := by
  constructor
  · convert! (hd.g11.const_mul base.g22).sub (hd.g21.const_mul base.g12) using 1
    dsimp [normalizeStateAt]; ring
  · convert! (hd.g12.const_mul base.g22).sub (hd.g22.const_mul base.g12) using 1
    dsimp [normalizeStateAt]; ring
  · convert! (hd.g11.const_mul (-base.g21)).add (hd.g21.const_mul base.g11) using 1
    dsimp [normalizeStateAt]; ring
  · convert! (hd.g12.const_mul (-base.g21)).add (hd.g22.const_mul base.g11) using 1
    dsimp [normalizeStateAt]; ring

theorem normalizeStateAt_coordinates_ac (base : State) {x : ℝ → State} {a b : ℝ}
    (hac : ∀ i, AbsolutelyContinuousOnInterval (fun t => (x t).coordinates i) a b)
    (i : Fin 8) :
    AbsolutelyContinuousOnInterval (fun t => (normalizeStateAt base (x t)).coordinates i) a b := by
  fin_cases i
  · exact ((hac 0).const_mul base.g22).sub ((hac 2).const_mul base.g12)
  · exact ((hac 1).const_mul base.g22).sub ((hac 3).const_mul base.g12)
  · exact ((hac 0).const_mul (-base.g21)).add ((hac 2).const_mul base.g11)
  · exact ((hac 1).const_mul (-base.g21)).add ((hac 3).const_mul base.g11)
  · exact hac 4
  · exact hac 5
  · exact hac 6
  · exact hac 7

theorem normalizeStateAt_action (base x : State) (hb : base.g11*base.g22-base.g12*base.g21=1) (v : E) :
    stateAction (normalizeStateAt base x) v=(stateFrame base hb).symm (stateAction x v) := by
  apply (stateFrame base hb).injective
  rw [LinearEquiv.apply_symm_apply]
  change stateAction base (stateAction (normalizeStateAt base x) v)=stateAction x v
  have he : stateAction base (stateAction (normalizeStateAt base x) v)=
      (base.g11*base.g22-base.g12*base.g21) • stateAction x v := by
    ext i; fin_cases i <;> simp [stateAction,normalizeStateAt] <;> ring
  rw [he,hb,one_smul]

noncomputable def minimizerInitialNormalizedState (t : ℝ) : State :=
  normalizeStateAt (minimizerBalancedState 0) (minimizerBalancedState t)

noncomputable def minimizerInitialInverseFrame : E ≃ₗ[ℝ] E :=
  (stateFrame (minimizerBalancedState 0) (minimizerBalancedState_determinants 0).1).symm

noncomputable def minimizerFrameBody : Set E := minimizerInitialInverseFrame '' ratioMinimizingBody

theorem minimizerFrameBody_disc : IsSymmetricConvexDisc minimizerFrameBody :=
  symmetricConvexDisc_linear_image ratioMinimizingBody_properties.1 minimizerInitialInverseFrame

theorem minimizerInitialInverseFrame_det : LinearMap.det (minimizerInitialInverseFrame : E →ₗ[ℝ] E)=1 := by
  rw [minimizerInitialInverseFrame,LinearEquiv.det_coe_symm,stateFrame_det,inv_one]

theorem minimizerInitialNormalizedState_initial :
    minimizerInitialNormalizedState 0=initialState (minimizerInitialNormalizedState 0) :=
  normalizeStateAt_initial _ (minimizerBalancedState_determinants 0).1

theorem minimizerInitialNormalizedState_determinants (t : ℝ) :
    (minimizerInitialNormalizedState t).determinantConstraints :=
  normalizeStateAt_determinants _ _ (minimizerBalancedState_determinants 0).1
    (minimizerBalancedState_determinants t)

theorem minimizerInitialNormalizedState_coordinates_ac (i : Fin 8) (a b : ℝ) :
    AbsolutelyContinuousOnInterval (fun t => (minimizerInitialNormalizedState t).coordinates i) a b :=
  normalizeStateAt_coordinates_ac _ (fun j => minimizerBalancedState_coordinates_ac j a b) i

theorem minimizerInitialNormalizedState_group_derivative (t : ℝ) :
    GroupDerivative minimizerInitialNormalizedState t :=
  normalizeStateAt_group_derivative _ (minimizerBalancedState_group_derivative t)

theorem minimizerInitialNormalizedState_star_pos (t : ℝ) :
    0 < rho0 (minimizerInitialNormalizedState t) ∧ 0 < rho1 (minimizerInitialNormalizedState t) ∧
      0 < rho2 (minimizerInitialNormalizedState t) := minimizerBalancedState_star_pos t

theorem minimizerInitialNormalizedState_root (i : Fin 6) (t : ℝ) :
    stateAction (minimizerInitialNormalizedState t) (root i)=
      minimizerInitialInverseFrame (minimizerBalancedBoundary i t) := by
  rw [minimizerInitialNormalizedState,normalizeStateAt_action _ _ (minimizerBalancedState_determinants 0).1,
    minimizerBalancedState_root]
  rfl

theorem minimizerInitialNormalizedState_roots_frontier (i : Fin 6) (t : ℝ) :
    stateAction (minimizerInitialNormalizedState t) (root i) ∈ frontier minimizerFrameBody := by
  rw [minimizerInitialNormalizedState_root]
  have he := minimizerInitialInverseFrame.toContinuousLinearEquiv.toHomeomorph.image_frontier ratioMinimizingBody
  change minimizerInitialInverseFrame '' frontier ratioMinimizingBody=frontier minimizerFrameBody at he
  rw [← he]
  exact mem_image_of_mem _ (minimizerBalancedBoundary_frontier i t)

end Certificate.Packing
