import Certificate.HexagonMidpointContact

/-! Exact second variation for rotating a side about its midpoint. For a
genuine hexagon the quadratic term strictly decreases its area. -/
namespace Certificate.Packing
open Set MeasureTheory
set_option maxHeartbeats 0
namespace Hex

lemma strict_outer_det_pos (H : Hex) (hs : H.Strict) (hD : 0 < det2 H.v H.w) :
    0 < det2 H.a H.c := by
  have hn := (H.fan_determinants_nonneg hD.le).2.2
  have he : det2 (HVGeometry.pairLinear H.φ₁ H.φ₃ H.a)
      (HVGeometry.pairLinear H.φ₁ H.φ₃ H.c) = 1+H.φ₁ H.c := by
    simp [HVGeometry.pairLinear,det2,point,H.ha₁,H.ha₃,H.hc₃]
  have hne : det2 H.a H.c ≠ 0 := by
    intro hz
    rw [det2_linearMap,hz,mul_zero] at he
    have hc := (abs_lt.1 hs.2.2).1
    linarith
  exact lt_of_le_of_ne hn (Ne.symm hne)

lemma slide_pair_det_neg (H : Hex) (hs : H.Strict) (hD : 0 < det2 H.v H.w) :
    det2 H.slideA H.slideB < 0 := by
  have hi := form_det_identity H.φ₃ H.a H.b H.c
  rw [H.ha₃,H.hc₃] at hi
  have hac := H.strict_outer_det_pos hs hD
  have hbc := (abs_lt.1 hs.2.1).2
  have hn : det2 H.a H.b-det2 H.a H.c-det2 H.b H.c < 0 := by
    nlinarith [mul_pos (show 0 < 1-H.φ₃ H.b by linarith) hac]
  have he : det2 H.slideA H.slideB =
      (det2 H.a H.b-det2 H.a H.c-det2 H.b H.c)/((1+H.φ₁ H.c)*(1-H.φ₁ H.c)) := by
    rw [div_mul_eq_div_div]
    simp [slideA,slideB,det2]; ring
  rw [he]
  obtain ⟨hc0,hc1⟩ := abs_lt.1 hs.2.2
  exact div_neg_of_neg_of_pos hn (mul_pos (by linarith) (by linarith))

lemma midpoint_fixed_quadratic (H : Hex) (hs : H.Strict) (ζ : E →ₗ[ℝ] ℝ)
    (hz : ζ H.a+ζ H.b=0) :
    det2 H.a H.b*(ζ H.a*ζ H.slideB+ζ H.b*ζ H.slideA)-
      ζ H.a*ζ H.b*det2 H.slideA H.slideB = -(ζ H.a)^2*det2 H.slideA H.slideB := by
  let F := HVGeometry.pairLinear H.φ₁ ζ
  have hab : LinearMap.det F*det2 H.a H.b= -2*ζ H.a := by
    rw [← det2_linearMap]
    simp [F,HVGeometry.pairLinear,det2,point,H.ha₁,H.hb₁]
    linarith
  obtain ⟨hA,_,hB,_⟩ := H.slide_evaluations hs
  have hAB : LinearMap.det F*det2 H.slideA H.slideB=ζ H.slideB-ζ H.slideA := by
    rw [← det2_linearMap]
    simp [F,HVGeometry.pairLinear,det2,point,hA,hB]
  have hr : det2 H.a H.b*(ζ H.slideB-ζ H.slideA)= -2*ζ H.a*det2 H.slideA H.slideB := by
    rw [← hAB]
    calc
      det2 H.a H.b*(LinearMap.det F*det2 H.slideA H.slideB) =
          (LinearMap.det F*det2 H.a H.b)*det2 H.slideA H.slideB := by ring
      _ = _ := by rw [hab]
  have hb : ζ H.b= -ζ H.a := by linarith
  rw [hb]
  nlinarith [congrArg (fun s : ℝ => ζ H.a*s) hr]

/-- If the new normal fixes the side midpoint, its exact area change is
quadratic, with no omitted remainder term. -/
theorem moved_det_difference_of_midpoint_fixed (H : Hex) (hs : H.Strict)
    (ζ : E →ₗ[ℝ] ℝ) (hz : ζ H.a+ζ H.b=0) (t : ℝ)
    (ha : 1+t*ζ H.slideA ≠ 0) (hb : 1+t*ζ H.slideB ≠ 0) :
    det2 (H.movedA ζ t+H.movedB ζ t) (H.movedB ζ t+H.c)-det2 H.v H.w =
      t^2*(ζ H.a)^2*det2 H.slideA H.slideB/((1+t*ζ H.slideA)*(1+t*ζ H.slideB)) := by
  rw [H.moved_det_difference hs ζ t ha hb,hz,H.midpoint_fixed_quadratic hs ζ hz]
  ring

#print axioms slide_pair_det_neg
#print axioms moved_det_difference_of_midpoint_fixed
end Hex
end Certificate.Packing
