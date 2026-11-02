import Certificate.MinimizerBalancedState

/-! The constructed state acts on the six roots as the actual normalized
boundary curves. This identifies its geometric meaning independently of the
still-unassembled fundamental arc and its endpoint conditions. -/
namespace Certificate.Packing
open Set Filter Topology MeasureTheory Confinement HVGeometry
set_option maxHeartbeats 0

theorem minimizerBalancedState_root (i : Fin 6) (t : ℝ) :
    stateAction (minimizerBalancedState t) (root i) = minimizerBalancedBoundary i t := by
  have hs : Real.sqrt (3 : ℝ) ≠ 0 := by positivity
  ext k
  fin_cases i <;> fin_cases k <;>
    simp [stateAction, minimizerBalancedState, minimizerFrameColumn, root, s0, s1, s2, pt,
      minimizerBalancedBoundary, minimizerAngularBalancedCurve, criticalMidpointConfiguration] <;>
    field_simp <;> ring

theorem minimizerBalancedState_roots_frontier (i : Fin 6) (t : ℝ) :
    stateAction (minimizerBalancedState t) (root i) ∈ frontier ratioMinimizingBody := by
  rw [minimizerBalancedState_root]
  exact minimizerBalancedBoundary_frontier i t

theorem minimizerBalancedState_root_velocity (i : Fin 6) (t : ℝ) :
    stateAction (minimizerBalancedState t) (stateTangent (minimizerBalancedState t) (root i)) =
      minimizerBalancedVelocity i t := by
  have hd := stateAction_hasDerivAt (minimizerBalancedState_group_derivative t) (root i)
  have he : (fun s => stateAction (minimizerBalancedState s) (root i)) = minimizerBalancedBoundary i :=
    funext (fun s => minimizerBalancedState_root i s)
  rw [he] at hd
  exact hd.unique (hasDerivAt_minimizerBalancedBoundary i t)

end Certificate.Packing
