import Certificate.MinimizerClockInverse
import Mathlib.Order.Interval.Set.OrderEmbedding

/-! Absolute continuity survives the increasing C1 clock change. Consequently
all six determinant-normalized boundary curves have absolutely continuous
actual velocities, not merely continuous tangent directions. -/
namespace Certificate.Packing
open Set Filter Topology MeasureTheory
open scoped NNReal
set_option maxHeartbeats 0

theorem ac_comp_orderIso {X : Type*} [PseudoMetricSpace X] {f : ℝ → X}
    (e : ℝ ≃o ℝ) {a b : ℝ} {L : ℝ≥0}
    (hf : AbsolutelyContinuousOnInterval f (e a) (e b))
    (he : LipschitzOnWith L e (uIcc a b)) :
    AbsolutelyContinuousOnInterval (fun t => f (e t)) a b := by
  rw [absolutelyContinuousOnInterval_iff] at hf ⊢
  intro ε hε
  obtain ⟨δ,hδ,hfδ⟩ := hf ε hε
  refine ⟨δ / ((L : ℝ)+1), by positivity, ?_⟩
  intro E hE hlen
  let F : ℕ × (ℕ → ℝ × ℝ) := (E.1, fun i => (e (E.2 i).1, e (E.2 i).2))
  have hmap : ∀ {x : ℝ}, x ∈ uIcc a b → e x ∈ uIcc (e a) (e b) := by
    intro x hx
    rw [mem_uIcc] at hx ⊢
    rcases hx with hx | hx
    · exact Or.inl ⟨e.monotone hx.1, e.monotone hx.2⟩
    · exact Or.inr ⟨e.monotone hx.1, e.monotone hx.2⟩
  have hpre (x y z : ℝ) : e z ∈ uIoc (e x) (e y) ↔ z ∈ uIoc x y := by
    change z ∈ e.toOrderEmbedding ⁻¹' uIoc (e.toOrderEmbedding x) (e.toOrderEmbedding y) ↔ _
    rw [e.toOrderEmbedding.preimage_uIoc]
  have hF : F ∈ AbsolutelyContinuousOnInterval.disjWithin (e a) (e b) := by
    refine ⟨fun i hi => ⟨hmap (hE.1 i hi).1, hmap (hE.1 i hi).2⟩, ?_⟩
    intro i hi j hj hij
    apply Set.disjoint_left.2
    intro z hz hz'
    apply Set.disjoint_left.1 (hE.2 hi hj hij)
    · exact (hpre _ _ (e.symm z)).1 (by simpa only [e.apply_symm_apply] using hz)
    · exact (hpre _ _ (e.symm z)).1 (by simpa only [e.apply_symm_apply] using hz')
  have htotal : ∑ i ∈ Finset.range F.1, dist (F.2 i).1 (F.2 i).2 < δ := by
    calc
      _ ≤ (L : ℝ) * ∑ i ∈ Finset.range E.1, dist (E.2 i).1 (E.2 i).2 := by
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum (fun i hi => he.dist_le_mul _ (hE.1 i hi).1 _ (hE.1 i hi).2)
      _ ≤ ((L : ℝ)+1) * ∑ i ∈ Finset.range E.1, dist (E.2 i).1 (E.2 i).2 :=
        mul_le_mul_of_nonneg_right (by linarith) (Finset.sum_nonneg (fun _ _ => dist_nonneg))
      _ < ((L : ℝ)+1) * (δ/((L : ℝ)+1)) := mul_lt_mul_of_pos_left hlen (by positivity)
      _ = δ := by field_simp
  exact hfδ F hF htotal

theorem minimizerBalancedVelocity_ac (i : Fin 6) (a b : ℝ) :
    AbsolutelyContinuousOnInterval (minimizerBalancedVelocity i) a b := by
  obtain ⟨L,hL⟩ := contDiff_minimizerAngularTime.contDiffOn.exists_lipschitzOnWith
    (by norm_num) (convex_Icc _ _) isCompact_Icc
  exact ac_comp_orderIso minimizerClockOrderIso.symm
    (minimizerNormalizedAngularVelocity_ac i (minimizerAngularTime a) (minimizerAngularTime b)) hL

theorem minimizerBalancedBoundary_ac (i : Fin 6) (a b : ℝ) :
    AbsolutelyContinuousOnInterval (minimizerBalancedBoundary i) a b :=
  (contDiff_minimizerBalancedBoundary i).contDiffOn.absolutelyContinuousOnInterval

theorem minimizerBalancedVelocity_continuous (i : Fin 6) :
    Continuous (minimizerBalancedVelocity i) := by
  have he : deriv (minimizerBalancedBoundary i) = minimizerBalancedVelocity i :=
    funext (fun t => (hasDerivAt_minimizerBalancedBoundary i t).deriv)
  rw [← he]
  exact (contDiff_one_iff_deriv.1 (contDiff_minimizerBalancedBoundary i)).2

theorem minimizerBalancedBoundary_fixed_det (t : ℝ) :
    det2 (minimizerBalancedBoundary 0 t) (minimizerBalancedBoundary 1 t) = Real.sqrt 3 / 2 :=
  criticalMidpointNext_fixed_det (minimizerAngularMidpoint (minimizerAngularTime t))

theorem minimizerBalancedBoundary_balance (t : ℝ) :
    minimizerBalancedBoundary 2 t = minimizerBalancedBoundary 1 t - minimizerBalancedBoundary 0 t := rfl

theorem minimizerBalancedBoundary_opposite (i : Fin 3) (t : ℝ) :
    minimizerBalancedBoundary (⟨i.val + 3, by omega⟩ : Fin 6) t = -minimizerBalancedBoundary (i.castLE (by decide)) t := by
  fin_cases i <;> simp [minimizerBalancedBoundary, minimizerAngularBalancedCurve,
    criticalMidpointConfiguration] <;> module

end Certificate.Packing
