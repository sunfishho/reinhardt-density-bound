import Certificate.CriticalMidpointImplicit

/-! The implicit successor sends a positive boundary tangent to a positive
multiple of the next tangent. This is a local differential orientation result,
not yet a global order or coverage theorem for the midpoint locus. -/
namespace Certificate.Packing
open Set Filter Topology
set_option maxHeartbeats 0

noncomputable def criticalMidpointTangent (p : criticalMidpointSet) : E :=
  minimizerBoundaryTangent ⟨p.val, criticalMidpointSet_subset_frontier p.property⟩

lemma criticalMidpointTangent_det (p : criticalMidpointSet) :
    det2 p.val (criticalMidpointTangent p) = 1 :=
  minimizerBoundaryTangent_det ⟨p.val, criticalMidpointSet_subset_frontier p.property⟩

lemma criticalMidpointTangent_ne_zero (p : criticalMidpointSet) :
    criticalMidpointTangent p ≠ 0 :=
  minimizerBoundaryTangent_ne_zero ⟨p.val, criticalMidpointSet_subset_frontier p.property⟩

lemma det_criticalMidpointTangent (p : criticalMidpointSet) (v : E) :
    det2 v (criticalMidpointTangent p) = minimizerGaugeGradient p.val v := by
  have hs := minimizerGaugeGradient_support (criticalMidpoint_ne_zero p)
  simp only [minimizerRadialFoot, criticalMidpoint_gauge, inv_one, one_smul] at hs
  have hp := criticalMidpointSet_subset_frontier p.property
  have he := minimizer_normalized_support_unique
    (frontier_subset_iff_isClosed.2 ratioMinimizingBody_properties.1.2.1.isClosed hp)
    hs (minimizerBoundaryNormal_support ⟨p.val,hp⟩)
  have hv := LinearMap.congr_fun he v
  change minimizerGaugeGradient p.val v = _ at hv
  rw [hv]
  simp [criticalMidpointTangent, minimizerBoundaryTangent, det2, point]
  ring

lemma criticalMidpointNext_forward_transverse (p : criticalMidpointSet) :
    0 < minimizerGaugeGradient p.val (criticalMidpointNext p).val := by
  obtain ⟨H,hH,he,hp,rfl⟩ := exists_positive_criticalHexagonMidpoint p
  rw [criticalMidpointNext_side H hH he hp]
  change 0 < minimizerGaugeGradient (H.midpoint 0) (H.midpoint 1)
  have hh := LinearMap.congr_fun (minimizerGaugeGradient_eq_sideNormal H hH he 0)
    (H.midpoint 1)
  rw [show minimizerGaugeGradient (H.midpoint 0) (H.midpoint 1) =
      H.φ₁ (H.midpoint 1) from hh]
  have hc := (abs_lt.1 (criticalHexagon_of_minimizer_strict H hH he).2.2).1
  simp [Hex.midpoint, H.hb₁]
  linarith

noncomputable def criticalMidpointFirstPartial (p : criticalMidpointSet) : E →L[ℝ] E :=
  (-(detForm (criticalMidpointNext p).val).toContinuousLinearMap).smulRight (point 0 1)

lemma criticalMidpointFirstPartial_apply (p : criticalMidpointSet) (v : E) :
    criticalMidpointFirstPartial p v = det2 v (criticalMidpointNext p).val • point 0 1 := by
  simp [criticalMidpointFirstPartial, detForm_apply, det2]
  congr 1
  ring

lemma criticalMidpointConstraints_first_partial (p : criticalMidpointSet) :
    fderiv ℝ (fun z : E × E => criticalMidpointConstraints z.1 z.2)
      (p.val, (criticalMidpointNext p).val) ∘L ContinuousLinearMap.inl ℝ E E =
      criticalMidpointFirstPartial p := by
  have hf := (contDiffAt_criticalMidpointConstraints
    (p := p.val) (criticalMidpoint_ne_zero (criticalMidpointNext p))).differentiableAt
    (by norm_num)
  have hp : HasFDerivAt (fun x : E => (x,(criticalMidpointNext p).val))
      (ContinuousLinearMap.inl ℝ E E) p.val := by
    convert! (hasFDerivAt_id p.val).prodMk
      (hasFDerivAt_const (criticalMidpointNext p).val p.val) using 1
  have hc : HasFDerivAt (fun _ : E =>
      gauge ratioMinimizingBody (criticalMidpointNext p).val • point 1 0)
      (0 : E →L[ℝ] E) p.val := hasFDerivAt_const _ _
  have hd := (((detForm (criticalMidpointNext p).val).toContinuousLinearMap.hasFDerivAt
    (x := p.val)).neg).smul_const (point 0 1)
  have hh : HasFDerivAt (fun x => criticalMidpointConstraints x (criticalMidpointNext p).val)
      (criticalMidpointFirstPartial p) p.val := by
    convert! hc.add hd using 1
    · ext x i
      simp [criticalMidpointConstraints, detForm_apply, det2]
      ring_nf
      simp
    · simp [criticalMidpointFirstPartial]
  have hcomp := hf.hasFDerivAt.comp
    (g := fun z : E × E => criticalMidpointConstraints z.1 z.2) p.val hp
  exact hcomp.unique hh

noncomputable def criticalMidpointNextDerivative (p : criticalMidpointSet) : E →L[ℝ] E :=
  -(criticalMidpointPartial p).toContinuousLinearMap.inverse ∘L criticalMidpointFirstPartial p

theorem hasStrictFDerivAt_criticalMidpointLocalNext (p : criticalMidpointSet) :
    HasStrictFDerivAt (criticalMidpointLocalNext p) (criticalMidpointNextDerivative p) p.val := by
  have h := (contDiffAt_criticalMidpointConstraints (p := p.val)
    (criticalMidpoint_ne_zero (criticalMidpointNext p))).hasStrictFDerivAt_implicitFunction
      (by norm_num) (criticalMidpointConstraints_partial_invertible p)
  simpa only [criticalMidpointLocalNext, criticalMidpointConstraints_partial,
    criticalMidpointConstraints_first_partial, criticalMidpointNextDerivative] using h

lemma criticalMidpointNextDerivative_equation (p : criticalMidpointSet) (v : E) :
    criticalMidpointPartial p (criticalMidpointNextDerivative p v) =
      -(criticalMidpointFirstPartial p v) := by
  change (criticalMidpointPartial p).toContinuousLinearMap _ = _
  simp only [criticalMidpointNextDerivative, ContinuousLinearMap.comp_apply,
    neg_apply, map_neg]
  rw [(criticalMidpointPartial_isInvertible p).self_apply_inverse]

noncomputable def criticalMidpointTangentScale (p : criticalMidpointSet) : ℝ :=
  minimizerGaugeGradient p.val (criticalMidpointNext p).val /
    minimizerGaugeGradient (criticalMidpointNext p).val p.val

theorem criticalMidpointTangentScale_pos (p : criticalMidpointSet) :
    0 < criticalMidpointTangentScale p :=
  div_pos (criticalMidpointNext_forward_transverse p) (criticalMidpointNext_transverse p)

/-- Counterclockwise boundary tangents are carried to counterclockwise tangents,
with a strictly positive scale. -/
theorem criticalMidpointNextDerivative_tangent (p : criticalMidpointSet) :
    criticalMidpointNextDerivative p (criticalMidpointTangent p) =
      criticalMidpointTangentScale p • criticalMidpointTangent (criticalMidpointNext p) := by
  apply (criticalMidpointPartialEquiv p).injective
  change criticalMidpointPartial p _ = criticalMidpointPartial p _
  rw [criticalMidpointNextDerivative_equation, criticalMidpointFirstPartial_apply]
  have hzero : minimizerGaugeGradient (criticalMidpointNext p).val
      (criticalMidpointTangent (criticalMidpointNext p)) = 0 := by
    rw [← det_criticalMidpointTangent, det2_self]
  have hb := criticalMidpointNext_transverse p
  have hleft : det2 (criticalMidpointTangent p) (criticalMidpointNext p).val =
      -minimizerGaugeGradient p.val (criticalMidpointNext p).val := by
    rw [← det_criticalMidpointTangent]
    simp [det2]
    ring
  have hright := det_criticalMidpointTangent (criticalMidpointNext p) p.val
  simp only [criticalMidpointPartial, HVGeometry.pairLinear, map_smul, detForm_apply, hleft]
  ext i
  fin_cases i
  · simp [point, hzero]
  · simp [point, criticalMidpointTangentScale, hright, hb.ne']

theorem criticalMidpointNextDerivative_tangent_ne_zero (p : criticalMidpointSet) :
    criticalMidpointNextDerivative p (criticalMidpointTangent p) ≠ 0 := by
  rw [criticalMidpointNextDerivative_tangent]
  exact smul_ne_zero (criticalMidpointTangentScale_pos p).ne'
    (criticalMidpointTangent_ne_zero (criticalMidpointNext p))


theorem hasDerivAt_criticalMidpointNext_comp {γ : ℝ → criticalMidpointSet} {t : ℝ} {v : E}
    (hγ : HasDerivAt (fun s => (γ s).val) v t) :
    HasDerivAt (fun s => (criticalMidpointNext (γ s)).val)
      (criticalMidpointNextDerivative (γ t) v) t := by
  have hc : Tendsto γ (𝓝 t) (𝓝 (γ t)) := tendsto_subtype_rng.2 hγ.continuousAt.tendsto
  have he := hc.eventually (criticalMidpointLocalNext_agrees (γ t))
  have hs := (hasStrictFDerivAt_criticalMidpointLocalNext (γ t)).hasFDerivAt.comp_hasDerivAt t hγ
  exact hs.congr_of_eventuallyEq (he.mono (fun s h => h.symm))

theorem continuous_criticalMidpointTangentScale : Continuous criticalMidpointTangentScale := by
  have hg : Continuous (fun p : criticalMidpointSet => minimizerGaugeGradient p.val) :=
    continuousOn_minimizerGaugeGradient.comp_continuous continuous_subtype_val
      (fun p => criticalMidpoint_ne_zero p)
  have ha := hg.clm_apply (continuous_subtype_val.comp continuous_criticalMidpointNext)
  have hb := (hg.comp continuous_criticalMidpointNext).clm_apply continuous_subtype_val
  exact ha.div hb (fun p => (criticalMidpointNext_transverse p).ne')

/-- The positive tangent scale stays bounded above and away from zero on the
compact midpoint locus. This bounds first-order transport, not variation of
the boundary tangent itself. -/
theorem criticalMidpointTangentScale_bounds :
    ∃ m M : ℝ, 0 < m ∧ ∀ p : criticalMidpointSet,
      m ≤ criticalMidpointTangentScale p ∧ criticalMidpointTangentScale p ≤ M := by
  let : CompactSpace criticalMidpointSet := isCompact_iff_compactSpace.1 isCompact_criticalMidpointSet
  by_cases hn : Nonempty criticalMidpointSet
  · let := hn
    obtain ⟨p,_,hp⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty
      continuous_criticalMidpointTangentScale.continuousOn
    obtain ⟨q,_,hq⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty
      continuous_criticalMidpointTangentScale.continuousOn
    exact ⟨_,_,criticalMidpointTangentScale_pos p,fun r => ⟨hp (mem_univ r),hq (mem_univ r)⟩⟩
  · refine ⟨1,1,by norm_num,?_⟩
    intro p
    exact (hn ⟨p⟩).elim


lemma criticalMidpointNext_transverse_lt_one (p : criticalMidpointSet) :
    minimizerGaugeGradient (criticalMidpointNext p).val p.val < 1 := by
  obtain ⟨H,hH,he,hp,rfl⟩ := exists_positive_criticalHexagonMidpoint p
  rw [criticalMidpointNext_side H hH he hp]
  change minimizerGaugeGradient (H.midpoint 1) (H.midpoint 0) < 1
  have hh := LinearMap.congr_fun (minimizerGaugeGradient_eq_sideNormal H hH he 1)
    (H.midpoint 0)
  rw [show minimizerGaugeGradient (H.midpoint 1) (H.midpoint 0) =
      H.φ₂ (H.midpoint 0) from hh]
  have hc := (abs_lt.1 (criticalHexagon_of_minimizer_strict H hH he).1).2
  simp [Hex.midpoint, H.hb₂]
  linarith

lemma criticalMidpointNext_forward_transverse_lt_one (p : criticalMidpointSet) :
    minimizerGaugeGradient p.val (criticalMidpointNext p).val < 1 := by
  obtain ⟨H,hH,he,hp,rfl⟩ := exists_positive_criticalHexagonMidpoint p
  rw [criticalMidpointNext_side H hH he hp]
  change minimizerGaugeGradient (H.midpoint 0) (H.midpoint 1) < 1
  have hh := LinearMap.congr_fun (minimizerGaugeGradient_eq_sideNormal H hH he 0)
    (H.midpoint 1)
  rw [show minimizerGaugeGradient (H.midpoint 0) (H.midpoint 1) =
      H.φ₁ (H.midpoint 1) from hh]
  have hc := (abs_lt.1 (criticalHexagon_of_minimizer_strict H hH he).2.2).2
  simp [Hex.midpoint, H.hb₁]
  linarith

lemma det2_pair_identity (p q v w : E) :
    det2 p q * det2 v w = det2 p v * det2 q w - det2 p w * det2 q v := by
  simp only [det2]
  ring

theorem criticalMidpoint_adjacent_tangents_det_pos (p : criticalMidpointSet) :
    0 < det2 (criticalMidpointTangent p) (criticalMidpointTangent (criticalMidpointNext p)) := by
  have hi := det2_pair_identity p.val (criticalMidpointNext p).val
    (criticalMidpointTangent p) (criticalMidpointTangent (criticalMidpointNext p))
  rw [criticalMidpointTangent_det p, criticalMidpointTangent_det (criticalMidpointNext p),
    det_criticalMidpointTangent (criticalMidpointNext p) p.val,
    det_criticalMidpointTangent p (criticalMidpointNext p).val, one_mul] at hi
  have hab : minimizerGaugeGradient (criticalMidpointNext p).val p.val *
      minimizerGaugeGradient p.val (criticalMidpointNext p).val < 1 := by
    calc
      _ < minimizerGaugeGradient (criticalMidpointNext p).val p.val * 1 :=
        mul_lt_mul_of_pos_left (criticalMidpointNext_forward_transverse_lt_one p)
          (criticalMidpointNext_transverse p)
      _ < 1 := by simpa using criticalMidpointNext_transverse_lt_one p
  have hprod : 0 < det2 p.val (criticalMidpointNext p).val *
      det2 (criticalMidpointTangent p) (criticalMidpointTangent (criticalMidpointNext p)) := by
    rw [hi]
    linarith
  have hc : 0 < det2 p.val (criticalMidpointNext p).val := by
    rw [criticalMidpointNext_fixed_det]
    positivity
  exact pos_of_mul_pos_right hprod hc.le

/-- The adjacent position velocities form an oriented, nondegenerate frame.
This is the positivity needed before a determinant-normalizing time change. -/
theorem criticalMidpoint_adjacent_velocities_det_pos (p : criticalMidpointSet) :
    0 < det2 (criticalMidpointTangent p)
      (criticalMidpointNextDerivative p (criticalMidpointTangent p)) := by
  rw [criticalMidpointNextDerivative_tangent]
  have he : det2 (criticalMidpointTangent p)
      (criticalMidpointTangentScale p • criticalMidpointTangent (criticalMidpointNext p)) =
      criticalMidpointTangentScale p *
        det2 (criticalMidpointTangent p) (criticalMidpointTangent (criticalMidpointNext p)) := by
    simp [det2]
    ring
  rw [he]
  exact mul_pos (criticalMidpointTangentScale_pos p) (criticalMidpoint_adjacent_tangents_det_pos p)

#print axioms det_criticalMidpointTangent
#print axioms criticalMidpointNext_forward_transverse
#print axioms hasStrictFDerivAt_criticalMidpointLocalNext
#print axioms criticalMidpointNextDerivative_equation
#print axioms criticalMidpointTangentScale_pos
#print axioms criticalMidpointNextDerivative_tangent
#print axioms criticalMidpointNextDerivative_tangent_ne_zero
#print axioms hasDerivAt_criticalMidpointNext_comp
#print axioms continuous_criticalMidpointTangentScale
#print axioms criticalMidpointTangentScale_bounds
#print axioms criticalMidpointNext_transverse_lt_one
#print axioms criticalMidpointNext_forward_transverse_lt_one
#print axioms criticalMidpoint_adjacent_tangents_det_pos
#print axioms criticalMidpoint_adjacent_velocities_det_pos
end Certificate.Packing
