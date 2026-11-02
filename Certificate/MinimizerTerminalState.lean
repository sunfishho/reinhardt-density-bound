import Certificate.InitialFrameNormalization
import Certificate.MinimizerEndpointVelocities

/-! The initial normalization and exact endpoint velocity matching give the
rotated terminal state. This closes the endpoint obligations for the actual
FrameTrajectory; the once-around FrameTrace is a separate construction. -/
namespace Certificate.Packing
open Set Filter Topology MeasureTheory Confinement HVGeometry
set_option maxHeartbeats 300000

theorem stateAction_initialState (x : State) (v : E) : stateAction (initialState x) v=v := by
  ext i; fin_cases i <;> simp [stateAction,initialState]

theorem minimizerInitialInverseFrame_start (i : Fin 6) :
    minimizerInitialInverseFrame (minimizerBalancedBoundary i 0)=root i := by
  rw [← minimizerInitialNormalizedState_root,minimizerInitialNormalizedState_initial,stateAction_initialState]

theorem minimizerInitialNormalizedState_root_velocity (i : Fin 6) (t : ℝ) :
    stateAction (minimizerInitialNormalizedState t)
      (stateTangent (minimizerInitialNormalizedState t) (root i))=
      minimizerInitialInverseFrame (minimizerBalancedVelocity i t) := by
  have hd := stateAction_hasDerivAt (minimizerInitialNormalizedState_group_derivative t) (root i)
  have he : (fun s => stateAction (minimizerInitialNormalizedState s) (root i))=
      fun s => minimizerInitialInverseFrame (minimizerBalancedBoundary i s) :=
    funext (minimizerInitialNormalizedState_root i)
  rw [he] at hd
  exact hd.unique (minimizerInitialInverseFrame.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_minimizerBalancedBoundary i t))

theorem minimizerInitialNormalizedState_terminal_roots :
    stateAction (minimizerInitialNormalizedState minimizerFundamentalDuration) (root 0)=root 1 ∧
    stateAction (minimizerInitialNormalizedState minimizerFundamentalDuration) (root 1)=root 2 := by
  constructor
  · rw [minimizerInitialNormalizedState_root,minimizerFundamentalDuration_endpoint,minimizerInitialInverseFrame_start]
  · rw [minimizerInitialNormalizedState_root,minimizerFundamentalNextPosition_endpoint,minimizerInitialInverseFrame_start]

theorem minimizerInitialNormalizedState_terminal_frame :
    let x := minimizerInitialNormalizedState minimizerFundamentalDuration
    x.g11=1/2 ∧ x.g12= -Real.sqrt 3/2 ∧ x.g21=Real.sqrt 3/2 ∧ x.g22=1/2 := by
  let x := minimizerInitialNormalizedState minimizerFundamentalDuration
  obtain ⟨h0,h1⟩ := minimizerInitialNormalizedState_terminal_roots
  have h00 := congrArg (fun z : E => z 0) h0
  have h01 := congrArg (fun z : E => z 1) h0
  have h10 := congrArg (fun z : E => z 0) h1
  have h11 := congrArg (fun z : E => z 1) h1
  change stateAction x (root 0) 0=root 1 0 at h00
  change stateAction x (root 0) 1=root 1 1 at h01
  change stateAction x (root 1) 0=root 2 0 at h10
  change stateAction x (root 1) 1=root 2 1 at h11
  norm_num [stateAction,root,s0,s1,s2,pt] at h00 h01 h10 h11
  change x.g11*(1/2)+x.g12*(Real.sqrt 3/2)= -(1/2) at h10
  change x.g21*(1/2)+x.g22*(Real.sqrt 3/2)=Real.sqrt 3/2 at h11
  have hs : Real.sqrt (3 : ℝ) ≠ 0 := by positivity
  have hs2 := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have hx12 : (x.g12+Real.sqrt 3/2)*Real.sqrt 3=0 := by nlinarith only [h00,h10,hs2]
  have hx22 : (x.g22-1/2)*Real.sqrt 3=0 := by nlinarith only [h01,h11]
  have he12 := (mul_eq_zero.1 hx12).resolve_right hs
  have he22 := (mul_eq_zero.1 hx22).resolve_right hs
  exact ⟨h00,by linarith only [he12],h01,by linarith only [he22]⟩

theorem rotateState_tangent_roots (x : State) :
    stateAction (rotateState x) (stateTangent (rotateState x) (root 0))=stateTangent x (root 1) ∧
    stateAction (rotateState x) (stateTangent (rotateState x) (root 1))=stateTangent x (root 2) := by
  have hs2 := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have hs3 : Real.sqrt (3 : ℝ)^3=3*Real.sqrt 3 := by
    calc
      _ = Real.sqrt 3 ^ 2 * Real.sqrt 3 := by ring
      _ = _ := by rw [hs2]
  constructor <;> ext i <;> fin_cases i <;>
    simp [stateAction,stateTangent,rotateState,root,s0,s1,s2,pt,point] <;>
    ring_nf <;> simp only [hs2,hs3] <;> ring

theorem state_eq_of_frame_and_root_tangents (x y : State)
    (hg11 : x.g11=y.g11) (hg12 : x.g12=y.g12) (hg21 : x.g21=y.g21) (hg22 : x.g22=y.g22)
    (h0 : stateTangent x (root 0)=stateTangent y (root 0))
    (h1 : stateTangent x (root 1)=stateTangent y (root 1)) : x=y := by
  have h00 := congrArg (fun z : E => z 0) h0
  have h01 := congrArg (fun z : E => z 1) h0
  have h10 := congrArg (fun z : E => z 0) h1
  norm_num [stateTangent,root,s0,s1,pt,point] at h00 h01 h10
  have hdiff : x.p-x.h=y.p-y.h := by
    apply mul_right_cancel₀ (show Real.sqrt (3 : ℝ) ≠ 0 by positivity)
    nlinarith only [h00,h10]
  exact state_ext hg11 hg12 hg21 hg22 h00 (by linarith only [h01,hdiff]) (by linarith only [h01,hdiff])

theorem minimizerInitialNormalizedState_terminal :
    minimizerInitialNormalizedState minimizerFundamentalDuration=
      rotateState (minimizerInitialNormalizedState 0) := by
  let x := minimizerInitialNormalizedState minimizerFundamentalDuration
  let y := rotateState (minimizerInitialNormalizedState 0)
  obtain ⟨h11,h12,h21,h22⟩ := minimizerInitialNormalizedState_terminal_frame
  have hframe (v : E) : stateAction x v=stateAction y v := by
    ext i; fin_cases i <;> simp [stateAction,x,y,rotateState,h11,h12,h21,h22]
  have hv0 : stateAction x (stateTangent x (root 0))=stateAction y (stateTangent y (root 0)) := by
    rw [(rotateState_tangent_roots (minimizerInitialNormalizedState 0)).1]
    change stateAction (minimizerInitialNormalizedState minimizerFundamentalDuration) _=_
    rw [minimizerInitialNormalizedState_root_velocity,minimizerFundamentalVelocity_endpoint,
      ← minimizerInitialNormalizedState_root_velocity]
    conv_lhs => rw [minimizerInitialNormalizedState_initial]
    rw [stateAction_initialState]
    rfl
  have hv1 : stateAction x (stateTangent x (root 1))=stateAction y (stateTangent y (root 1)) := by
    rw [(rotateState_tangent_roots (minimizerInitialNormalizedState 0)).2]
    change stateAction (minimizerInitialNormalizedState minimizerFundamentalDuration) _=_
    rw [minimizerInitialNormalizedState_root_velocity,minimizerFundamentalNextVelocity_endpoint,
      ← minimizerInitialNormalizedState_root_velocity]
    conv_lhs => rw [minimizerInitialNormalizedState_initial]
    rw [stateAction_initialState]
    rfl
  have ht0 : stateTangent x (root 0)=stateTangent y (root 0) := by
    apply (stateFrame x (minimizerInitialNormalizedState_determinants _).1).injective
    change stateAction x _=stateAction x _
    rw [hframe (stateTangent y (root 0))]
    exact hv0
  have ht1 : stateTangent x (root 1)=stateTangent y (root 1) := by
    apply (stateFrame x (minimizerInitialNormalizedState_determinants _).1).injective
    change stateAction x _=stateAction x _
    rw [hframe (stateTangent y (root 1))]
    exact hv1
  exact state_eq_of_frame_and_root_tangents x y h11 h12 h21 h22 ht0 ht1

noncomputable def minimizerFrameTrajectory : FrameTrajectory where
  state := minimizerInitialNormalizedState
  duration := minimizerFundamentalDuration
  duration_nonneg := minimizerFundamentalDuration_pos.le
  coordinates_ac i := minimizerInitialNormalizedState_coordinates_ac i _ _
  determinant t _ := minimizerInitialNormalizedState_determinants t
  star_nonneg t _ := ⟨(minimizerInitialNormalizedState_star_pos t).1.le,
    (minimizerInitialNormalizedState_star_pos t).2.1.le,(minimizerInitialNormalizedState_star_pos t).2.2.le⟩
  group_ode := Filter.Eventually.of_forall minimizerInitialNormalizedState_group_derivative
  initial := minimizerInitialNormalizedState_initial
  terminal := minimizerInitialNormalizedState_terminal

theorem minimizerFrameTrajectory_boundary (i : Fin 6) (t : ℝ) :
    stateAction (minimizerFrameTrajectory.state t) (root i) ∈ frontier minimizerFrameBody :=
  minimizerInitialNormalizedState_roots_frontier i t

end Certificate.Packing
