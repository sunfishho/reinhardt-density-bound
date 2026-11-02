import Certificate.CriticalMidpointCoverage

/-! The globally ordered critical successor now acts on the entire boundary.
Local regularity results therefore apply to arbitrary boundary curves. -/
namespace Certificate.Packing
open Set Filter Topology
set_option maxHeartbeats 0

noncomputable def criticalMidpointBoundaryHomeomorph :
    criticalMidpointSet ≃ₜ frontier ratioMinimizingBody :=
  Homeomorph.setCongr criticalMidpointSet_eq_frontier_minimizer

noncomputable def minimizerBoundarySuccessor :
    frontier ratioMinimizingBody ≃ₜ frontier ratioMinimizingBody :=
  criticalMidpointBoundaryHomeomorph.symm.trans
    (criticalMidpointHomeomorph.trans criticalMidpointBoundaryHomeomorph)

theorem minimizerBoundarySuccessor_balance (p : frontier ratioMinimizingBody) :
    (minimizerBoundarySuccessor (minimizerBoundarySuccessor p)).val =
      (minimizerBoundarySuccessor p).val-p.val :=
  criticalMidpointNext_balance (criticalMidpointBoundaryHomeomorph.symm p)

set_option maxRecDepth 2048 in
theorem minimizerBoundarySuccessor_sixth (p : frontier ratioMinimizingBody) :
    minimizerBoundarySuccessor (minimizerBoundarySuccessor (minimizerBoundarySuccessor
      (minimizerBoundarySuccessor (minimizerBoundarySuccessor (minimizerBoundarySuccessor p))))) = p := by
  apply Subtype.ext
  change (criticalMidpointNext (criticalMidpointNext (criticalMidpointNext
    (criticalMidpointNext (criticalMidpointNext (criticalMidpointNext
      (criticalMidpointBoundaryHomeomorph.symm p))))))).val = p.val
  rw [criticalMidpointNext_sixth]
  rfl

theorem minimizerBoundarySuccessor_fixed_det (p : frontier ratioMinimizingBody) :
    det2 p.val (minimizerBoundarySuccessor p).val = Real.sqrt 3/2 :=
  criticalMidpointNext_fixed_det (criticalMidpointBoundaryHomeomorph.symm p)

theorem minimizerBoundarySuccessor_det_pos_iff (p q : frontier ratioMinimizingBody) :
    0 < det2 (minimizerBoundarySuccessor p).val (minimizerBoundarySuccessor q).val ↔
      0 < det2 p.val q.val :=
  criticalMidpointNext_det_pos_iff (criticalMidpointBoundaryHomeomorph.symm p)
    (criticalMidpointBoundaryHomeomorph.symm q)

theorem contDiffAt_minimizerBoundarySuccessor_comp {γ : ℝ → frontier ratioMinimizingBody} {t : ℝ}
    (hγ : ContDiffAt ℝ 1 (fun s => (γ s).val) t) :
    ContDiffAt ℝ 1 (fun s => (minimizerBoundarySuccessor (γ s)).val) t :=
  contDiffAt_criticalMidpointNext_comp (γ := fun s => criticalMidpointBoundaryHomeomorph.symm (γ s)) hγ

theorem minimizerBoundarySuccessor_regular_curve {γ : ℝ → frontier ratioMinimizingBody}
    {t : ℝ} {v : E} (hγ : HasDerivAt (fun s => (γ s).val) v t) (hv : v ≠ 0) :
    ∃ w : E, HasDerivAt (fun s => (minimizerBoundarySuccessor (γ s)).val) w t ∧ w ≠ 0 :=
  ⟨_,criticalMidpointNext_regular_curve
    (γ := fun s => criticalMidpointBoundaryHomeomorph.symm (γ s)) hγ hv⟩

theorem minimizerRadialFoot_mem_criticalMidpointSet {x : E} (hx : x ≠ 0) :
    minimizerRadialFoot x ∈ criticalMidpointSet := by
  rw [criticalMidpointSet_eq_frontier_minimizer]
  exact minimizerRadialFoot_frontier hx

#print axioms minimizerBoundarySuccessor
#print axioms minimizerBoundarySuccessor_balance
#print axioms minimizerBoundarySuccessor_sixth
#print axioms minimizerBoundarySuccessor_fixed_det
#print axioms minimizerBoundarySuccessor_det_pos_iff
#print axioms contDiffAt_minimizerBoundarySuccessor_comp
#print axioms minimizerBoundarySuccessor_regular_curve
#print axioms minimizerRadialFoot_mem_criticalMidpointSet
end Certificate.Packing
