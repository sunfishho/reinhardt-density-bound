import Certificate.CriticalMidpointOrientation

/-! A regular curve in the actual midpoint locus remains regular under the
successor. The existence and coverage of a full boundary curve are separate. -/
namespace Certificate.Packing
open Set Filter Topology
set_option maxHeartbeats 0

lemma criticalMidpoint_vector_decomposition (p : criticalMidpointSet) (v : E) :
    v = minimizerGaugeGradient p.val v • p.val +
      det2 p.val v • criticalMidpointTangent p := by
  rw [← det_criticalMidpointTangent]
  calc
    v = det2 p.val (criticalMidpointTangent p) • v := by
      rw [criticalMidpointTangent_det, one_smul]
    _ = _ := by
      ext i
      fin_cases i <;> simp [det2] <;> ring

theorem criticalMidpointNextDerivative_ne_zero_on_tangent (p : criticalMidpointSet)
    {v : E} (hv : v ≠ 0) (ht : minimizerGaugeGradient p.val v = 0) :
    criticalMidpointNextDerivative p v ≠ 0 := by
  have he := criticalMidpoint_vector_decomposition p v
  rw [ht, zero_smul, zero_add] at he
  have hk : det2 p.val v ≠ 0 := by
    intro hz
    rw [hz, zero_smul] at he
    exact hv he
  calc
    criticalMidpointNextDerivative p v =
        det2 p.val v • criticalMidpointNextDerivative p (criticalMidpointTangent p) := by
      conv_lhs => rw [he, map_smul]
    _ ≠ 0 := smul_ne_zero hk (criticalMidpointNextDerivative_tangent_ne_zero p)

theorem criticalMidpointCurve_velocity_tangent {γ : ℝ → criticalMidpointSet} {t : ℝ} {v : E}
    (hγ : HasDerivAt (fun s => (γ s).val) v t) :
    minimizerGaugeGradient (γ t).val v = 0 := by
  have hg := (hasFDerivAt_minimizerGauge (criticalMidpoint_ne_zero (γ t))).comp_hasDerivAt t hγ
  have he : (fun s => gauge ratioMinimizingBody (γ s).val) = fun _ : ℝ => (1 : ℝ) := by
    funext s
    exact criticalMidpoint_gauge (γ s)
  change HasDerivAt (fun s => gauge ratioMinimizingBody (γ s).val)
    (minimizerGaugeGradient (γ t).val v) t at hg
  rw [he] at hg
  exact hg.unique (hasDerivAt_const t 1)

/-- Derivative transport preserves regularity without a separately supplied
tangency hypothesis: belonging to the midpoint locus supplies tangency. -/
theorem criticalMidpointNext_regular_curve {γ : ℝ → criticalMidpointSet} {t : ℝ} {v : E}
    (hγ : HasDerivAt (fun s => (γ s).val) v t) (hv : v ≠ 0) :
    HasDerivAt (fun s => (criticalMidpointNext (γ s)).val)
      (criticalMidpointNextDerivative (γ t) v) t ∧
      criticalMidpointNextDerivative (γ t) v ≠ 0 :=
  ⟨hasDerivAt_criticalMidpointNext_comp hγ,
    criticalMidpointNextDerivative_ne_zero_on_tangent (γ t) hv
      (criticalMidpointCurve_velocity_tangent hγ)⟩

#print axioms criticalMidpoint_vector_decomposition
#print axioms criticalMidpointNextDerivative_ne_zero_on_tangent
#print axioms criticalMidpointCurve_velocity_tangent
#print axioms criticalMidpointNext_regular_curve
end Certificate.Packing
