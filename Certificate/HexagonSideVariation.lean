import Certificate.HexagonParameters

/-! A local variation of one pair of opposite sides. The other two strips
remain fixed. Strict unused-strip inequalities ensure that the perturbed
vertices still describe a genuine hexagon. -/
namespace Certificate.Packing
open Set MeasureTheory Filter
set_option maxHeartbeats 0

namespace Hex

def Strict (H : Hex) : Prop :=
  |H.φ₂ H.a| < 1 ∧ |H.φ₃ H.b| < 1 ∧ |H.φ₁ H.c| < 1

noncomputable def slideA (H : Hex) : E := (1/(1+H.φ₁ H.c)) • (H.a+H.c)
noncomputable def slideB (H : Hex) : E := (1/(1-H.φ₁ H.c)) • (H.b-H.c)

lemma slide_evaluations (H : Hex) (hs : H.Strict) :
    H.φ₁ H.slideA=1 ∧ H.φ₃ H.slideA=0 ∧
    H.φ₁ H.slideB=1 ∧ H.φ₂ H.slideB=0 := by
  obtain ⟨hc0,hc1⟩ := abs_lt.1 hs.2.2
  have hp : 1+H.φ₁ H.c ≠ 0 := by linarith
  have hm : 1-H.φ₁ H.c ≠ 0 := by linarith
  simp [slideA,slideB,map_add,map_sub,H.ha₁,H.ha₃,H.hb₁,H.hb₂,H.hc₂,H.hc₃,hp,hm]
  field_simp

noncomputable def movedA (H : Hex) (ζ : E →ₗ[ℝ] ℝ) (t : ℝ) : E :=
  H.a-(t*ζ H.a/(1+t*ζ H.slideA)) • H.slideA
noncomputable def movedB (H : Hex) (ζ : E →ₗ[ℝ] ℝ) (t : ℝ) : E :=
  H.b-(t*ζ H.b/(1+t*ζ H.slideB)) • H.slideB

@[simp] lemma movedA_zero (H : Hex) (ζ : E →ₗ[ℝ] ℝ) : H.movedA ζ 0=H.a := by simp [movedA]
@[simp] lemma movedB_zero (H : Hex) (ζ : E →ₗ[ℝ] ℝ) : H.movedB ζ 0=H.b := by simp [movedB]

lemma movedA_continuousAt (H : Hex) (ζ : E →ₗ[ℝ] ℝ) : ContinuousAt (H.movedA ζ) 0 := by
  unfold movedA
  fun_prop (disch := norm_num)
lemma movedB_continuousAt (H : Hex) (ζ : E →ₗ[ℝ] ℝ) : ContinuousAt (H.movedB ζ) 0 := by
  unfold movedB
  fun_prop (disch := norm_num)

lemma moved_incidence (H : Hex) (hs : H.Strict) (ζ : E →ₗ[ℝ] ℝ) (t : ℝ)
    (ha : 1+t*ζ H.slideA ≠ 0) (hb : 1+t*ζ H.slideB ≠ 0) :
    (H.φ₁+t • ζ) (H.movedA ζ t)=1 ∧ H.φ₃ (H.movedA ζ t)= -1 ∧
    (H.φ₁+t • ζ) (H.movedB ζ t)=1 ∧ H.φ₂ (H.movedB ζ t)=1 := by
  obtain ⟨hA,hA3,hB,hB2⟩ := H.slide_evaluations hs
  refine ⟨?_,?_,?_,?_⟩
  · simp [movedA,map_sub,map_smul,H.ha₁,hA]
    field_simp; ring
  · simp [movedA,map_sub,map_smul,H.ha₃,hA3]
  · simp [movedB,map_sub,map_smul,H.hb₁,hB]
    field_simp; ring
  · simp [movedB,map_sub,map_smul,H.hb₂,hB2]

lemma form_det_identity (φ : E →ₗ[ℝ] ℝ) (a b c : E) :
    φ a*det2 b c-φ b*det2 a c+φ c*det2 a b=0 := by
  rw [← HexParameters.form_coordinates φ a,← HexParameters.form_coordinates φ b,
    ← HexParameters.form_coordinates φ c]
  unfold det2; ring

lemma slide_determinants (H : Hex) (hs : H.Strict) :
    det2 H.slideA (H.b+H.c)=det2 H.a H.b ∧
    det2 (H.a-H.c) H.slideB=det2 H.a H.b := by
  have hi := form_det_identity H.φ₁ H.a H.b H.c
  rw [H.ha₁,H.hb₁] at hi
  obtain ⟨hc0,hc1⟩ := abs_lt.1 hs.2.2
  have hp : 1+H.φ₁ H.c ≠ 0 := by linarith
  have hm : 1-H.φ₁ H.c ≠ 0 := by linarith
  constructor
  · have he : det2 H.slideA (H.b+H.c)=
        (det2 H.a H.b+det2 H.a H.c-det2 H.b H.c)/(1+H.φ₁ H.c) := by
      simp [slideA,det2]; ring
    rw [he,div_eq_iff hp]; linarith
  · have he : det2 (H.a-H.c) H.slideB=
        (det2 H.a H.b-det2 H.a H.c+det2 H.b H.c)/(1-H.φ₁ H.c) := by
      simp [slideB,det2]; ring
    rw [he,div_eq_iff hm]; linarith

/-- Exact area variation, retaining the quadratic term rather than taking
an informal first variation. -/
lemma moved_det_difference (H : Hex) (hs : H.Strict) (ζ : E →ₗ[ℝ] ℝ) (t : ℝ)
    (ha : 1+t*ζ H.slideA ≠ 0) (hb : 1+t*ζ H.slideB ≠ 0) :
    det2 (H.movedA ζ t+H.movedB ζ t) (H.movedB ζ t+H.c)-det2 H.v H.w =
    -t*(det2 H.a H.b*(ζ H.a+ζ H.b)+t*
      (det2 H.a H.b*(ζ H.a*ζ H.slideB+ζ H.b*ζ H.slideA)-
        ζ H.a*ζ H.b*det2 H.slideA H.slideB))/
      ((1+t*ζ H.slideA)*(1+t*ζ H.slideB)) := by
  have he : ∀ q r : ℝ,
      det2 (H.a-q • H.slideA+(H.b-r • H.slideB)) (H.b-r • H.slideB+H.c)-det2 H.v H.w =
      -q*det2 H.slideA (H.b+H.c)-r*det2 (H.a-H.c) H.slideB+q*r*det2 H.slideA H.slideB := by
    intro q r; simp [det2,Hex.v,Hex.w]; ring
  unfold movedA movedB
  rw [he,(H.slide_determinants hs).1,(H.slide_determinants hs).2]
  field_simp; ring

#print axioms moved_det_difference
end Hex
end Certificate.Packing
