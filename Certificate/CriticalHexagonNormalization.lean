import Certificate.MinimizerHexagonConstruction

/-! Explicit initial coordinate normalization of the attained critical hexagon.
All six side midpoints become the sixth roots of unity. This is an algebraic
normalization; midpoint membership in the minimizing body is not assumed. -/
namespace Certificate.Packing
open Set MeasureTheory HVGeometry
set_option maxHeartbeats 0

noncomputable def Hex.midpoint (H : Hex) : Fin 6 → E :=
  ![(1/2:ℝ) • (H.a+H.b),(1/2:ℝ) • (H.b+H.c),(1/2:ℝ) • (H.c-H.a),
    -(1/2:ℝ) • (H.a+H.b),-(1/2:ℝ) • (H.b+H.c),-(1/2:ℝ) • (H.c-H.a)]

lemma Hex.midpoint_det (H : Hex) : det2 (H.midpoint 0) (H.midpoint 1)=det2 H.v H.w/4 := by
  simp [Hex.midpoint,Hex.v,Hex.w,det2]; ring

lemma Hex.midpoint_det_ne_zero (H : Hex) : det2 (H.midpoint 0) (H.midpoint 1) ≠ 0 := by
  rw [H.midpoint_det]; exact div_ne_zero H.hdet (by norm_num)

lemma root01_det : det2 (root 0) (root 1)=Real.sqrt 3/2 := by
  norm_num [root,s0,s1,pt,det2]

noncomputable def Hex.midpointFrame (H : Hex) : E ≃ₗ[ℝ] E :=
  (pairFrame (H.midpoint 0) (H.midpoint 1) H.midpoint_det_ne_zero).symm.trans
    (pairFrame (root 0) (root 1) (by rw [root01_det]; positivity))

lemma Hex.midpointFrame_first (H : Hex) :
    H.midpointFrame (H.midpoint 0)=root 0 ∧ H.midpointFrame (H.midpoint 1)=root 1 := by
  have h0 : pairFrame (H.midpoint 0) (H.midpoint 1) H.midpoint_det_ne_zero (point 1 0)=H.midpoint 0 := by
    simp [point]
  have h1 : pairFrame (H.midpoint 0) (H.midpoint 1) H.midpoint_det_ne_zero (point 0 1)=H.midpoint 1 := by
    simp [point]
  have hi0 : (pairFrame (H.midpoint 0) (H.midpoint 1) H.midpoint_det_ne_zero).symm
      (H.midpoint 0)=point 1 0 := by
    apply (pairFrame (H.midpoint 0) (H.midpoint 1) H.midpoint_det_ne_zero).injective
    rw [LinearEquiv.apply_symm_apply]
    exact h0.symm
  have hi1 : (pairFrame (H.midpoint 0) (H.midpoint 1) H.midpoint_det_ne_zero).symm
      (H.midpoint 1)=point 0 1 := by
    apply (pairFrame (H.midpoint 0) (H.midpoint 1) H.midpoint_det_ne_zero).injective
    rw [LinearEquiv.apply_symm_apply]
    exact h1.symm
  constructor
  · unfold Hex.midpointFrame
    rw [LinearEquiv.trans_apply,hi0]
    simp [point]
  · unfold Hex.midpointFrame
    rw [LinearEquiv.trans_apply,hi1]
    simp [point]

/-- The map normalizes the entire six-point configuration, not just a basis. -/
theorem Hex.midpointFrame_all (H : Hex) (i : Fin 6) : H.midpointFrame (H.midpoint i)=root i := by
  obtain ⟨h0,h1⟩ := H.midpointFrame_first
  have h2 : H.midpointFrame (H.midpoint 2)=root 2 := by
    have he : H.midpoint 2=H.midpoint 1-H.midpoint 0 := by simp [Hex.midpoint]; module
    rw [he,map_sub,h0,h1]
    ext j; fin_cases j <;> simp [root,s0,s1,s2,pt] <;> ring
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · change H.midpointFrame (-(1/2:ℝ) • (H.a+H.b))=root 3
    rw [neg_smul,map_neg]
    change -H.midpointFrame (H.midpoint 0)= -root 0
    rw [h0]
  · change H.midpointFrame (-(1/2:ℝ) • (H.b+H.c))=root 4
    rw [neg_smul,map_neg]
    change -H.midpointFrame (H.midpoint 1)= -root 1
    rw [h1]
  · change H.midpointFrame (-(1/2:ℝ) • (H.c-H.a))=root 5
    rw [neg_smul,map_neg]
    change -H.midpointFrame (H.midpoint 2)= -root 2
    rw [h2]

/-- The scalar normalization already established makes this coordinate change
area preserving, even when the input vertices have the opposite orientation. -/
theorem Hex.midpointFrame_abs_det (H : Hex) (hn : |det2 H.v H.w|=2*Real.sqrt 3) :
    |LinearMap.det (H.midpointFrame : E →ₗ[ℝ] E)|=1 := by
  have hh : det2 (H.midpointFrame (H.midpoint 0)) (H.midpointFrame (H.midpoint 1)) =
      LinearMap.det (H.midpointFrame : E →ₗ[ℝ] E)*det2 (H.midpoint 0) (H.midpoint 1) :=
    det2_linearMap (H.midpointFrame : E →ₗ[ℝ] E) (H.midpoint 0) (H.midpoint 1)
  rw [H.midpointFrame_first.1,H.midpointFrame_first.2,root01_det,H.midpoint_det] at hh
  have ha := congrArg abs hh
  simp only [abs_mul,abs_div,hn,abs_of_nonneg (Real.sqrt_nonneg 3)] at ha
  have hs : 0 < Real.sqrt (3:ℝ) := by positivity
  norm_num at ha
  nlinarith

noncomputable def ratioMinimizingInitialFrame : E ≃ₗ[ℝ] E := ratioMinimizingHexagon.midpointFrame
noncomputable def initiallyNormalizedMinimizer : Set E := ratioMinimizingInitialFrame '' ratioMinimizingBody

theorem initiallyNormalizedMinimizer_properties :
    IsSymmetricConvexDisc initiallyNormalizedMinimizer ∧
    criticalHexArea initiallyNormalizedMinimizer=ENNReal.ofReal (2*Real.sqrt 3) ∧
    (∀ K : Set E, IsSymmetricConvexDisc K → hexagonRatio initiallyNormalizedMinimizer ≤ hexagonRatio K) ∧
    (∀ i : Fin 6, ratioMinimizingInitialFrame (ratioMinimizingHexagon.midpoint i)=root i) := by
  have hd : |LinearMap.det (ratioMinimizingInitialFrame : E →ₗ[ℝ] E)|=1 :=
    ratioMinimizingHexagon.midpointFrame_abs_det ratioMinimizingHexagon_properties.2.2.1
  refine ⟨symmetricConvexDisc_linear_image ratioMinimizingBody_properties.1 _,?_,?_,?_⟩
  · rw [initiallyNormalizedMinimizer,criticalHexArea_linear_image,hd,ENNReal.ofReal_one,one_mul,
      ratioMinimizingBody_properties.2.1]
  · intro K hK
    rw [initiallyNormalizedMinimizer,hexagonRatio_linear_image]
    exact ratioMinimizingBody_properties.2.2.2.1 K hK
  · exact ratioMinimizingHexagon.midpointFrame_all

#print axioms Hex.midpointFrame_all
#print axioms Hex.midpointFrame_abs_det
#print axioms initiallyNormalizedMinimizer_properties
end Certificate.Packing
