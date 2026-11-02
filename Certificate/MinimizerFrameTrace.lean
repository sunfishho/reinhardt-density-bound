import Certificate.MinimizerTerminalState
import Certificate.MinimizerFundamentalArc
import Certificate.CriticalMidpointSectorSeparation

/-! The six constructed fundamental arcs cover the minimizing body's boundary
once. Coverage and absence of interior overlaps are proved from the explicit
sector partition and the successor's order-preserving bijection. -/
namespace Certificate.Packing
open Set Filter Topology MeasureTheory Confinement HVGeometry
set_option maxHeartbeats 300000

theorem minimizerBalancedBoundary_eq_step (i : Fin 6) (t : ℝ) :
    minimizerBalancedBoundary i t=(criticalMidpointStep (minimizerTimedMidpoint t) i).val :=
  (criticalMidpointStep_val _ _).symm

theorem minimizerBalancedBoundary_covers {x : E} (hx : x ∈ frontier ratioMinimizingBody) :
    ∃ i : Fin 6, ∃ t ∈ Icc 0 minimizerFundamentalDuration, minimizerBalancedBoundary i t=x := by
  let p := minimizerTimedMidpoint 0
  let r : criticalMidpointSet := ⟨x,criticalMidpointSet_eq_frontier_minimizer.symm ▸ hx⟩
  obtain ⟨i,hi | hi⟩ := criticalMidpoint_partition p r
  · refine ⟨i,0,⟨le_rfl,minimizerFundamentalDuration_pos.le⟩,?_⟩
    rw [minimizerBalancedBoundary_eq_step]
    exact congrArg Subtype.val hi.symm
  · obtain ⟨q,hq⟩ := criticalMidpointStep_surjective i r
    rw [← hq] at hi
    have hsector := (criticalMidpointStep_sector_iff p q i).1 hi
    obtain ⟨t,ht,he⟩ := minimizerFundamentalSector_timed_range hsector
    refine ⟨i,t,⟨ht.1.le,ht.2.le⟩,?_⟩
    rw [minimizerBalancedBoundary_eq_step,he]
    exact congrArg (fun z : criticalMidpointSet => z.val) hq

theorem minimizerBalancedBoundary_in_sector (i : Fin 6) {t : ℝ}
    (ht : t ∈ Ioo 0 minimizerFundamentalDuration) :
    InCriticalMidpointSector (criticalMidpointStep (minimizerTimedMidpoint 0) i)
      (minimizerBalancedBoundary i t) := by
  rw [minimizerBalancedBoundary_eq_step]
  exact (criticalMidpointStep_sector_iff _ _ i).2 (minimizerTimedMidpoint_in_fundamental_sector ht)

theorem minimizerBalancedBoundary_simple (i j : Fin 6) {s t : ℝ}
    (hs : s ∈ Ioo 0 minimizerFundamentalDuration) (ht : t ∈ Ioo 0 minimizerFundamentalDuration)
    (he : minimizerBalancedBoundary i s=minimizerBalancedBoundary j t) : i=j ∧ s=t := by
  have hi := minimizerBalancedBoundary_in_sector i hs
  have hj := minimizerBalancedBoundary_in_sector j ht
  rw [← he] at hj
  have hij := criticalMidpoint_sectors_disjoint _ hi hj
  subst j
  refine ⟨rfl,?_⟩
  apply minimizerTimedMidpoint_injOn_fundamental ⟨hs.1.le,hs.2.le⟩ ⟨ht.1.le,ht.2.le⟩
  apply criticalMidpointStep_injective i
  apply Subtype.ext
  simpa only [← minimizerBalancedBoundary_eq_step] using he

theorem minimizerFrameTrace : FrameTrace minimizerFrameTrajectory minimizerFrameBody where
  boundary i t _ := minimizerFrameTrajectory_boundary i t
  covers x hx := by
    have he := minimizerInitialInverseFrame.toContinuousLinearEquiv.toHomeomorph.image_frontier ratioMinimizingBody
    change minimizerInitialInverseFrame '' frontier ratioMinimizingBody=frontier minimizerFrameBody at he
    rw [← he] at hx
    obtain ⟨q,hq,rfl⟩ := hx
    obtain ⟨i,t,ht,hit⟩ := minimizerBalancedBoundary_covers hq
    refine ⟨i,t,ht,?_⟩
    change stateAction (minimizerInitialNormalizedState t) (root i)=_
    rw [minimizerInitialNormalizedState_root,hit]
  simple i j s t hs ht he := by
    change stateAction (minimizerInitialNormalizedState s) (root i)=
      stateAction (minimizerInitialNormalizedState t) (root j) at he
    rw [minimizerInitialNormalizedState_root,minimizerInitialNormalizedState_root] at he
    exact minimizerBalancedBoundary_simple i j hs ht (minimizerInitialInverseFrame.injective he)

end Certificate.Packing
