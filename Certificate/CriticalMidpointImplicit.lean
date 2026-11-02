import Certificate.CriticalMidpointTransversality
import Mathlib.Analysis.Calculus.ImplicitContDiff

/-! Local C1 continuation of the critical-midpoint successor. The continuation
is defined on an ambient neighborhood and agrees with the successor on its
actual locus. No full-boundary coverage or Lipschitz tangent bound is assumed. -/
namespace Certificate.Packing
open Set Filter Topology
set_option maxHeartbeats 0

lemma criticalMidpoint_gauge (p : criticalMidpointSet) :
    gauge ratioMinimizingBody p.val = 1 :=
  (gauge_eq_one_iff_mem_frontier ratioMinimizingBody_properties.1.1
    (disc_mem_nhds_zero ratioMinimizingBody_properties.1)).2
    (criticalMidpointSet_subset_frontier p.property)

lemma criticalMidpoint_ne_zero (p : criticalMidpointSet) : p.val ≠ 0 := by
  intro he
  have h := criticalMidpoint_gauge p
  simp [he] at h

theorem criticalMidpointConstraints_next (p : criticalMidpointSet) :
    criticalMidpointConstraints p.val (criticalMidpointNext p).val =
      point 1 (Real.sqrt 3 / 2) := by
  simp only [criticalMidpointConstraints, criticalMidpoint_gauge,
    criticalMidpointNext_fixed_det, one_smul]
  ext i
  fin_cases i <;> simp [point]

lemma contDiffAt_criticalMidpointConstraints {p q : E} (hq : q ≠ 0) :
    ContDiffAt ℝ 1 (fun z : E × E => criticalMidpointConstraints z.1 z.2) (p,q) := by
  have hg : ContDiffAt ℝ 1 (gauge ratioMinimizingBody) q :=
    (contDiffOn_minimizerGauge q hq).contDiffAt
      ((isClosed_singleton.isOpen_compl : IsOpen {x : E | x ≠ 0}).mem_nhds hq)
  unfold criticalMidpointConstraints
  apply ContDiffAt.add
  · have hg' : ContDiffAt ℝ 1 (fun z : E × E => gauge ratioMinimizingBody z.2) (p,q) :=
      ContDiffAt.comp (f := Prod.snd) (g := gauge ratioMinimizingBody) (p,q) hg contDiffAt_snd
    exact hg'.smul contDiffAt_const
  · have hd : ContDiffAt ℝ 1 (fun z : E × E => det2 z.1 z.2) (p,q) := by
      unfold det2
      fun_prop
    exact hd.smul contDiffAt_const

lemma criticalMidpointConstraints_partial (p : criticalMidpointSet) :
    fderiv ℝ (fun z : E × E => criticalMidpointConstraints z.1 z.2)
      (p.val, (criticalMidpointNext p).val) ∘L ContinuousLinearMap.inr ℝ E E =
      (criticalMidpointPartial p).toContinuousLinearMap := by
  have hf := (contDiffAt_criticalMidpointConstraints
    (p := p.val) (criticalMidpoint_ne_zero (criticalMidpointNext p))).differentiableAt
    (by norm_num)
  have hp : HasFDerivAt (fun q : E => (p.val,q)) (ContinuousLinearMap.inr ℝ E E)
      (criticalMidpointNext p).val := by
    convert! (hasFDerivAt_const p.val (criticalMidpointNext p).val).prodMk
      (hasFDerivAt_id (criticalMidpointNext p).val) using 1
  exact (hf.hasFDerivAt.comp (criticalMidpointNext p).val hp).unique
    (hasFDerivAt_criticalMidpointConstraints p)

lemma criticalMidpointConstraints_partial_invertible (p : criticalMidpointSet) :
    (fderiv ℝ (fun z : E × E => criticalMidpointConstraints z.1 z.2)
      (p.val, (criticalMidpointNext p).val) ∘L ContinuousLinearMap.inr ℝ E E).IsInvertible := by
  rw [criticalMidpointConstraints_partial]
  exact criticalMidpointPartial_isInvertible p

noncomputable def criticalMidpointLocalNext (p : criticalMidpointSet) : E → E :=
  (contDiffAt_criticalMidpointConstraints (p := p.val)
    (criticalMidpoint_ne_zero (criticalMidpointNext p))).implicitFunction (by norm_num)
      (criticalMidpointConstraints_partial_invertible p)

theorem criticalMidpointLocalNext_self (p : criticalMidpointSet) :
    criticalMidpointLocalNext p p.val = (criticalMidpointNext p).val :=
  ContDiffAt.implicitFunction_apply_self _ _ _

theorem contDiffAt_criticalMidpointLocalNext (p : criticalMidpointSet) :
    ContDiffAt ℝ 1 (criticalMidpointLocalNext p) p.val :=
  ContDiffAt.contDiffAt_implicitFunction _ _ _

theorem criticalMidpointLocalNext_constraints (p : criticalMidpointSet) :
    ∀ᶠ x in 𝓝 p.val, criticalMidpointConstraints x (criticalMidpointLocalNext p x) =
      point 1 (Real.sqrt 3 / 2) := by
  have h := (contDiffAt_criticalMidpointConstraints (p := p.val)
    (criticalMidpoint_ne_zero (criticalMidpointNext p))).eventually_apply_implicitFunction
      (by norm_num) (criticalMidpointConstraints_partial_invertible p)
  simpa only [criticalMidpointLocalNext, criticalMidpointConstraints_next] using h

theorem criticalMidpointLocalNext_unique (p : criticalMidpointSet) :
    ∀ᶠ z : E × E in 𝓝 (p.val, (criticalMidpointNext p).val),
      criticalMidpointConstraints z.1 z.2 = point 1 (Real.sqrt 3 / 2) ↔
        criticalMidpointLocalNext p z.1 = z.2 := by
  have h := (contDiffAt_criticalMidpointConstraints (p := p.val)
    (criticalMidpoint_ne_zero (criticalMidpointNext p))).eventually_apply_eq_iff_implicitFunction
      (by norm_num) (criticalMidpointConstraints_partial_invertible p)
  simpa only [criticalMidpointLocalNext, criticalMidpointConstraints_next] using h

/-- Continuity selects the correct implicit branch on the existing midpoint
locus, without any assumption that this locus contains a boundary arc. -/
theorem criticalMidpointLocalNext_agrees (p : criticalMidpointSet) :
    ∀ᶠ r : criticalMidpointSet in 𝓝 p,
      criticalMidpointLocalNext p r.val = (criticalMidpointNext r).val := by
  have hc : Continuous (fun r : criticalMidpointSet => (r.val, (criticalMidpointNext r).val)) :=
    continuous_subtype_val.prodMk (continuous_subtype_val.comp continuous_criticalMidpointNext)
  have h := hc.continuousAt.tendsto.eventually (criticalMidpointLocalNext_unique p)
  filter_upwards [h] with r hr
  exact hr.mp (criticalMidpointConstraints_next r)

/-- Any C1 curve in the midpoint locus carries its successor along a C1
curve. This is conditional on the curve lying in the locus, not an existence
claim for a full boundary arc. -/
theorem contDiffAt_criticalMidpointNext_comp {γ : ℝ → criticalMidpointSet} {t : ℝ}
    (hγ : ContDiffAt ℝ 1 (fun s => (γ s).val) t) :
    ContDiffAt ℝ 1 (fun s => (criticalMidpointNext (γ s)).val) t := by
  have hc : Tendsto γ (𝓝 t) (𝓝 (γ t)) := tendsto_subtype_rng.2 hγ.continuousAt.tendsto
  have he := hc.eventually (criticalMidpointLocalNext_agrees (γ t))
  have hs := ContDiffAt.comp (f := fun s => (γ s).val)
    (g := criticalMidpointLocalNext (γ t)) t
    (contDiffAt_criticalMidpointLocalNext (γ t)) hγ
  exact hs.congr_of_eventuallyEq (he.mono (fun s h => h.symm))

theorem contDiffAt_criticalMidpointConfiguration_comp {γ : ℝ → criticalMidpointSet} {t : ℝ}
    (hγ : ContDiffAt ℝ 1 (fun s => (γ s).val) t) (i : Fin 6) :
    ContDiffAt ℝ 1 (fun s => criticalMidpointConfiguration (γ s) i) t := by
  have hn := contDiffAt_criticalMidpointNext_comp hγ
  fin_cases i
  · exact hγ
  · exact hn
  · exact hn.sub hγ
  · exact hγ.neg
  · exact hn.neg
  · exact hγ.sub hn

#print axioms criticalMidpointConstraints_next
#print axioms contDiffAt_criticalMidpointConstraints
#print axioms criticalMidpointConstraints_partial
#print axioms criticalMidpointLocalNext_self
#print axioms contDiffAt_criticalMidpointLocalNext
#print axioms criticalMidpointLocalNext_constraints
#print axioms criticalMidpointLocalNext_unique
#print axioms criticalMidpointLocalNext_agrees
#print axioms contDiffAt_criticalMidpointNext_comp
#print axioms contDiffAt_criticalMidpointConfiguration_comp
end Certificate.Packing
