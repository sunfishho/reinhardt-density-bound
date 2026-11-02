import Certificate.MinimizerGaugeDifferentiability
import Certificate.CriticalMidpointCycle

/-! The gauge/determinant equations for a neighboring critical midpoint have
an invertible linearization in that midpoint. This supplies the transversality
condition for an implicit-function construction; it does not assert coverage
of the whole boundary or Lipschitz regularity. -/
namespace Certificate.Packing
open Set MeasureTheory
set_option maxHeartbeats 0

lemma minimizerGaugeGradient_eq_sideNormal (H : Hex)
    (hH : ratioMinimizingBody ⊆ H.set)
    (he : volume H.set = criticalHexArea ratioMinimizingBody) (i : Fin 6) :
    (minimizerGaugeGradient (H.midpoint i)).toLinearMap = H.sideNormal i := by
  have hf := criticalHexagon_of_minimizer_midpoint_frontier H hH he i
  have hg : gauge ratioMinimizingBody (H.midpoint i) = 1 :=
    (gauge_eq_one_iff_mem_frontier ratioMinimizingBody_properties.1.1
      (disc_mem_nhds_zero ratioMinimizingBody_properties.1)).2 hf
  have hn : H.midpoint i ≠ 0 := by
    intro hz
    simp [hz] at hg
  have hs := minimizerGaugeGradient_support hn
  simp only [minimizerRadialFoot, hg, inv_one, one_smul] at hs
  apply minimizer_normalized_support_unique
    (frontier_subset_iff_isClosed.2 ratioMinimizingBody_properties.1.2.1.isClosed hf) hs
  exact ⟨H.sideNormal_midpoint i, fun x hx =>
    (le_abs_self _).trans (H.sideNormal_abs_le i (hH hx))⟩

/-- The neighboring midpoint's support normal is strictly positive on the
starting midpoint; hence the determinant constraint meets the boundary
transversely. -/
theorem criticalMidpointNext_transverse (p : criticalMidpointSet) :
    0 < minimizerGaugeGradient (criticalMidpointNext p).val p.val := by
  obtain ⟨H,hH,he,hp,rfl⟩ := exists_positive_criticalHexagonMidpoint p
  rw [criticalMidpointNext_side H hH he hp]
  change 0 < minimizerGaugeGradient (H.midpoint 1) (H.midpoint 0)
  have hh := LinearMap.congr_fun (minimizerGaugeGradient_eq_sideNormal H hH he 1)
    (H.midpoint 0)
  rw [show minimizerGaugeGradient (H.midpoint 1) (H.midpoint 0) =
      H.φ₂ (H.midpoint 0) from hh]
  exact H.second_normal_first_midpoint_pos (criticalHexagon_of_minimizer_strict H hH he)

noncomputable def criticalMidpointPartial (p : criticalMidpointSet) : E →ₗ[ℝ] E :=
  HVGeometry.pairLinear (minimizerGaugeGradient (criticalMidpointNext p).val).toLinearMap
    (detForm p.val)

/-- The two constraint derivatives are linearly independent. This avoids
constructing and simplifying a coordinate-by-coordinate inverse. -/
theorem criticalMidpointPartial_det_ne_zero (p : criticalMidpointSet) :
    LinearMap.det (criticalMidpointPartial p) ≠ 0 := by
  have hd : det2 p.val (criticalMidpointNext p).val ≠ 0 := by
    rw [criticalMidpointNext_fixed_det]
    positivity
  have ht := criticalMidpointNext_transverse p
  have hi : det2 (criticalMidpointPartial p p.val)
      (criticalMidpointPartial p (criticalMidpointNext p).val) =
      minimizerGaugeGradient (criticalMidpointNext p).val p.val *
        det2 p.val (criticalMidpointNext p).val := by
    simp [criticalMidpointPartial, HVGeometry.pairLinear, detForm_apply, det2, point]
    ring_nf
    simp
  intro hz
  rw [det2_linearMap, hz, zero_mul] at hi
  exact (mul_ne_zero ht.ne' hd) hi.symm

noncomputable def criticalMidpointPartialEquiv (p : criticalMidpointSet) : E ≃ₗ[ℝ] E :=
  (criticalMidpointPartial p).equivOfDetNeZero (criticalMidpointPartial_det_ne_zero p)


/-- The two equations used to continue a neighboring midpoint. -/
noncomputable def criticalMidpointConstraints (p q : E) : E :=
  gauge ratioMinimizingBody q • point 1 0 + det2 p q • point 0 1

theorem hasFDerivAt_criticalMidpointConstraints (p : criticalMidpointSet) :
    HasFDerivAt (criticalMidpointConstraints p.val)
      (criticalMidpointPartial p).toContinuousLinearMap (criticalMidpointNext p).val := by
  have hn : (criticalMidpointNext p).val ≠ 0 := by
    intro hz
    have ht := criticalMidpointNext_fixed_det p
    rw [hz] at ht
    simp only [det2, PiLp.zero_apply, mul_zero, sub_self] at ht
    have : (0:ℝ) < Real.sqrt 3 / 2 := by positivity
    linarith
  have hg := (hasFDerivAt_minimizerGauge hn).smul_const (point 1 0)
  have hd := ((detForm p.val).toContinuousLinearMap.hasFDerivAt (x := (criticalMidpointNext p).val)).smul_const (point 0 1)
  have h := hg.add hd
  convert! h using 1
  ext v i
  fin_cases i <;>
    simp [criticalMidpointPartial, HVGeometry.pairLinear, point, detForm_apply]

theorem criticalMidpointPartial_isInvertible (p : criticalMidpointSet) :
    (criticalMidpointPartial p).toContinuousLinearMap.IsInvertible := by
  exact ⟨(criticalMidpointPartialEquiv p).toContinuousLinearEquiv, rfl⟩

#print axioms minimizerGaugeGradient_eq_sideNormal
#print axioms criticalMidpointNext_transverse
#print axioms criticalMidpointPartial_det_ne_zero
#print axioms hasFDerivAt_criticalMidpointConstraints
#print axioms criticalMidpointPartial_isInvertible
end Certificate.Packing
