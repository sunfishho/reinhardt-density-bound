import Certificate.CriticalMidpointDynamics

/-! The continuous successor on the critical midpoint locus is a homeomorphism
with the six-point balance identities and fixed positive determinant. -/
namespace Certificate.Packing
open Set MeasureTheory HexParameters Topology
set_option maxHeartbeats 0

lemma Hex.sideRelabel_det (H : Hex) (i : Fin 6) :
    det2 (H.sideRelabel i).v (H.sideRelabel i).w=det2 H.v H.w := by
  fin_cases i <;> simp [sideRelabel,rotate_det]

lemma Hex.sideRelabel_next_midpoint (H : Hex) (i : Fin 6) :
    (H.sideRelabel i).midpoint 1=H.midpoint (i+1) := by
  fin_cases i
  · rfl
  · change H.rotate.midpoint 1=H.midpoint 2
    simp [rotate,midpoint]; module
  · change H.rotate.rotate.midpoint 1=H.midpoint 3
    simp [rotate,midpoint]
  · change H.rotate.rotate.rotate.midpoint 1=H.midpoint 4
    simp [rotate,midpoint]
  · change H.rotate.rotate.rotate.rotate.midpoint 1=H.midpoint 5
    simp [rotate,midpoint]; module
  · change H.rotate.rotate.rotate.rotate.rotate.midpoint 1=H.midpoint 0
    simp [rotate,midpoint]

noncomputable def criticalHexagonMidpoint (H : Hex)
    (hH : ratioMinimizingBody ⊆ H.set)
    (he : volume H.set=criticalHexArea ratioMinimizingBody) (i : Fin 6) : criticalMidpointSet :=
  ⟨H.midpoint i,critical_hexagon_midpoint_mem_set H hH he i⟩

theorem criticalMidpointNext_side (H : Hex)
    (hH : ratioMinimizingBody ⊆ H.set)
    (he : volume H.set=criticalHexArea ratioMinimizingBody)
    (hp : 0 < det2 H.v H.w) (i : Fin 6) :
    criticalMidpointNext (criticalHexagonMidpoint H hH he i)=
      criticalHexagonMidpoint H hH he (i+1) := by
  have hs : ratioMinimizingBody ⊆ (H.sideRelabel i).set := by rwa [H.sideRelabel_set]
  have ha : volume (H.sideRelabel i).set=criticalHexArea ratioMinimizingBody := by
    rwa [H.sideRelabel_set]
  have hpos : 0 < det2 (H.sideRelabel i).v (H.sideRelabel i).w := by
    rwa [H.sideRelabel_det]
  have h0 : criticalHexagonMidpoint (H.sideRelabel i) hs ha 0=
      criticalHexagonMidpoint H hH he i := by
    apply Subtype.ext
    exact H.sideRelabel_midpoint i
  apply Subtype.ext
  rw [← h0]
  exact (criticalMidpointNext_of_hexagon (H.sideRelabel i) hs ha hpos).trans
    (H.sideRelabel_next_midpoint i)

lemma exists_positive_criticalHexagonMidpoint (p : criticalMidpointSet) :
    ∃ (H : Hex) (hH : ratioMinimizingBody ⊆ H.set)
      (he : volume H.set=criticalHexArea ratioMinimizingBody),
      0 < det2 H.v H.w ∧ criticalHexagonMidpoint H hH he 0=p := by
  let d := positiveCriticalRepresentative p
  refine ⟨d.val.toHex d.property.1.1,d.property.1.2.1,
    critical_parameter_area d.property.1,positiveCriticalFamily_pos d.property,?_⟩
  apply Subtype.ext
  exact positiveCriticalRepresentative_point p

/-- The second successor is the difference of the first successor and the
starting point: this is the six-point balance relation on the actual locus. -/
theorem criticalMidpointNext_balance (p : criticalMidpointSet) :
    (criticalMidpointNext (criticalMidpointNext p)).val=
      (criticalMidpointNext p).val-p.val := by
  obtain ⟨H,hH,he,hp,rfl⟩ := exists_positive_criticalHexagonMidpoint p
  simp only [criticalMidpointNext_side H hH he hp]
  exact H.midpoint_two_eq

theorem criticalMidpointNext_third (p : criticalMidpointSet) :
    (criticalMidpointNext (criticalMidpointNext (criticalMidpointNext p))).val= -p.val := by
  rw [criticalMidpointNext_balance,criticalMidpointNext_balance]
  abel

theorem criticalMidpointNext_sixth (p : criticalMidpointSet) :
    criticalMidpointNext (criticalMidpointNext (criticalMidpointNext
      (criticalMidpointNext (criticalMidpointNext (criticalMidpointNext p)))))=p := by
  apply Subtype.ext
  rw [criticalMidpointNext_third,criticalMidpointNext_third,neg_neg]

/-- Successor and predecessor are both continuous. The domain remains the
critical midpoint set; no boundary-coverage or order assertion is implicit. -/
noncomputable def criticalMidpointHomeomorph : criticalMidpointSet ≃ₜ criticalMidpointSet where
  toFun := criticalMidpointNext
  invFun := fun p => criticalMidpointNext (criticalMidpointNext
    (criticalMidpointNext (criticalMidpointNext (criticalMidpointNext p))))
  left_inv := criticalMidpointNext_sixth
  right_inv := criticalMidpointNext_sixth
  continuous_toFun := continuous_criticalMidpointNext
  continuous_invFun := continuous_criticalMidpointNext.comp
    (continuous_criticalMidpointNext.comp (continuous_criticalMidpointNext.comp
      (continuous_criticalMidpointNext.comp continuous_criticalMidpointNext)))

theorem criticalMidpointNext_fixed_det (p : criticalMidpointSet) :
    det2 p.val (criticalMidpointNext p).val=Real.sqrt 3/2 := by
  obtain ⟨H,hH,he,hp,rfl⟩ := exists_positive_criticalHexagonMidpoint p
  rw [criticalMidpointNext_side H hH he hp]
  change det2 (H.midpoint 0) (H.midpoint 1)=_
  rw [H.midpoint_det]
  have ha := congrArg ENNReal.toReal he
  rw [H.volume_eq_covolume,ratioMinimizingBody_properties.2.1,
    ENNReal.toReal_ofReal (abs_nonneg _),ENNReal.toReal_ofReal (by positivity),
    abs_of_pos hp] at ha
  rw [ha]
  ring

theorem criticalMidpointNext_ne (p : criticalMidpointSet) : criticalMidpointNext p ≠ p := by
  intro h
  have hd := criticalMidpointNext_fixed_det p
  rw [h,det2_self] at hd
  have : (0:ℝ)<Real.sqrt 3/2 := by positivity
  linarith

/-- All six points of the uniquely oriented critical configuration vary
continuously with its first midpoint. -/
noncomputable def criticalMidpointConfiguration (p : criticalMidpointSet) (i : Fin 6) : E :=
  ![p.val,(criticalMidpointNext p).val,(criticalMidpointNext p).val-p.val,
    -p.val,-(criticalMidpointNext p).val,p.val-(criticalMidpointNext p).val] i

theorem continuous_criticalMidpointConfiguration (i : Fin 6) :
    Continuous (fun p => criticalMidpointConfiguration p i) := by
  have h := continuous_subtype_val.comp continuous_criticalMidpointNext
  fin_cases i <;> simp only [criticalMidpointConfiguration] <;> fun_prop

theorem criticalMidpointConfiguration_of_hexagon (H : Hex)
    (hH : ratioMinimizingBody ⊆ H.set)
    (he : volume H.set=criticalHexArea ratioMinimizingBody)
    (hp : 0 < det2 H.v H.w) (i : Fin 6) :
    criticalMidpointConfiguration (criticalHexagonMidpoint H hH he 0) i=H.midpoint i := by
  have hn : (criticalMidpointNext (criticalHexagonMidpoint H hH he 0)).val=H.midpoint 1 :=
    criticalMidpointNext_of_hexagon H hH he hp
  unfold criticalMidpointConfiguration
  rw [hn]
  fin_cases i <;> simp [criticalHexagonMidpoint,Hex.midpoint] <;> module

theorem criticalMidpointConfiguration_mem (p : criticalMidpointSet) (i : Fin 6) :
    criticalMidpointConfiguration p i ∈ criticalMidpointSet := by
  obtain ⟨H,hH,he,hp,rfl⟩ := exists_positive_criticalHexagonMidpoint p
  rw [criticalMidpointConfiguration_of_hexagon H hH he hp]
  exact critical_hexagon_midpoint_mem_set H hH he i

#print axioms criticalMidpointNext_side
#print axioms criticalMidpointNext_balance
#print axioms criticalMidpointNext_third
#print axioms criticalMidpointNext_sixth
#print axioms criticalMidpointHomeomorph
#print axioms criticalMidpointNext_fixed_det
#print axioms criticalMidpointNext_ne
#print axioms continuous_criticalMidpointConfiguration
#print axioms criticalMidpointConfiguration_of_hexagon
#print axioms criticalMidpointConfiguration_mem
end Certificate.Packing
