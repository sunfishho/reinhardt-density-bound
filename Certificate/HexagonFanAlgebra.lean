import Certificate.DiscAffineNormalization

/-! Orientation and vertex geometry of an arbitrary enclosing symmetric
hexagon, including repeated vertices and redundant supporting strips. -/
namespace Certificate.Packing
open Set MeasureTheory
set_option maxHeartbeats 0

noncomputable def detForm (v : E) : E →ₗ[ℝ] ℝ := v 0 • coord 1-v 1 • coord 0
@[simp] lemma detForm_apply (v x : E) : detForm v x = det2 v x := by
  simp [detForm,det2]

lemma det2_self (x : E) : det2 x x = 0 := by unfold det2; ring
lemma det2_swap (x y : E) : det2 x y = -det2 y x := by unfold det2; ring
lemma det2_neg_left (x y : E) : det2 (-x) y = -det2 x y := by simp [det2]; ring
lemma det2_neg_right (x y : E) : det2 x (-y) = -det2 x y := by simp [det2]; ring

/-- Reversing the vertex order changes the lattice orientation, not the set. -/
noncomputable def Hex.reverse (H : Hex) : Hex where
  φ₁ := H.φ₂
  φ₂ := H.φ₁
  φ₃ := -H.φ₃
  a := H.c
  b := H.b
  c := H.a
  ha₁ := H.hc₂
  ha₃ := by simp [H.hc₃]
  hb₁ := H.hb₂
  hb₂ := H.hb₁
  hc₂ := H.ha₁
  hc₃ := by simp [H.ha₃]
  hin_a := H.hin_c
  hin_b := by simpa using H.hin_b
  hin_c := H.hin_a
  hdet := by
    change det2 (H.c+H.b) (H.b+H.a) ≠ 0
    rw [add_comm H.c H.b,add_comm H.b H.a,det2_swap]
    exact neg_ne_zero.mpr H.hdet

lemma Hex.reverse_set (H : Hex) : H.reverse.set = H.set := by
  ext x
  simp [Hex.reverse,Hex.set,and_comm,and_left_comm]

lemma Hex.reverse_det (H : Hex) : det2 H.reverse.v H.reverse.w = -det2 H.v H.w := by
  change det2 (H.c+H.b) (H.b+H.a) = -det2 (H.a+H.b) (H.b+H.c)
  rw [add_comm H.c H.b,add_comm H.b H.a,det2_swap]

/-- The middle vertex in lattice coordinates has both coordinates in [0,1/2].
No pair of strip functionals is assumed linearly independent. -/
theorem Hex.middle_coordinates (H : Hex) :
    ∃ α β : ℝ, H.b = α • H.v+β • H.w ∧
      0 ≤ α ∧ α ≤ 1/2 ∧ 0 ≤ β ∧ β ≤ 1/2 := by
  let z := (pairFrame H.v H.w H.hdet).symm H.b
  have he : H.b = z 0 • H.v+z 1 • H.w :=
    ((pairFrame H.v H.w H.hdet).apply_symm_apply H.b).symm
  have h1 := congrArg H.φ₁ he
  have h2 := congrArg H.φ₂ he
  have h3 := congrArg H.φ₃ he
  simp only [Hex.v,Hex.w,map_add,map_smul,smul_eq_mul,H.ha₁,H.hb₁,H.hb₂,H.hc₂,
    H.ha₃,H.hc₃] at h1 h2 h3
  obtain ⟨hs0,hs1⟩ := abs_le.1 H.hin_a
  obtain ⟨ht0,ht1⟩ := abs_le.1 H.hin_c
  obtain ⟨hu0,hu1⟩ := abs_le.1 H.hin_b
  have hup : (H.φ₃ H.b)^2 ≤ 1 := by nlinarith
  have hprod : 0 ≤ (1-2*z 0)*(1-2*z 1) := by
    have hid : (1-2*z 0)*(1-2*z 1) =
        (1-(H.φ₃ H.b)^2)*(1-z 0-z 1)^2 := by
      have hh : H.φ₃ H.b*(1-z 0-z 1)=z 1-z 0 := by nlinarith [h3]
      nlinarith [sq_nonneg (H.φ₃ H.b*(1-z 0-z 1)-(z 1-z 0)),
        congrArg (fun t : ℝ => t^2) hh]
    rw [hid]; positivity
  have ha0 : 0 ≤ z 0 := by
    by_contra h; have ha : z 0 < 0 := lt_of_not_ge h
    have hb : 1/2 < z 1 := by
      by_contra hb; have hb' : z 1 ≤ 1/2 := le_of_not_gt hb
      have hterm : z 1*(1+H.φ₁ H.c) ≤ 1 := by
        calc
          z 1*(1+H.φ₁ H.c) ≤ (1/2)*(1+H.φ₁ H.c) := mul_le_mul_of_nonneg_right hb' (by linarith)
          _ ≤ 1 := by linarith
      nlinarith [h1]
    have : (1-2*z 0)*(1-2*z 1) < 0 := mul_neg_of_pos_of_neg (by linarith) (by linarith)
    linarith
  have hb0 : 0 ≤ z 1 := by
    by_contra h; have hb : z 1 < 0 := lt_of_not_ge h
    have ha : 1/2 < z 0 := by
      by_contra ha; have ha' : z 0 ≤ 1/2 := le_of_not_gt ha
      have hterm : z 0*(H.φ₂ H.a+1) ≤ 1 := by
        calc
          z 0*(H.φ₂ H.a+1) ≤ (1/2)*(H.φ₂ H.a+1) := mul_le_mul_of_nonneg_right ha' (by linarith)
          _ ≤ 1 := by linarith
      nlinarith [h2]
    have : (1-2*z 0)*(1-2*z 1) < 0 := mul_neg_of_neg_of_pos (by linarith) (by linarith)
    linarith
  refine ⟨z 0,z 1,he,ha0,?_,hb0,?_⟩
  · nlinarith [mul_nonneg hb0 (show 0 ≤ 1+H.φ₁ H.c by linarith)]
  · nlinarith [mul_nonneg ha0 (show 0 ≤ H.φ₂ H.a+1 by linarith)]

/-- All three fan determinants have the orientation of the lattice. -/
theorem Hex.fan_determinants_nonneg (H : Hex) (hD : 0 ≤ det2 H.v H.w) :
    0 ≤ det2 H.a H.b ∧ 0 ≤ det2 H.b H.c ∧ 0 ≤ det2 H.a H.c := by
  obtain ⟨α,β,hb,ha0,ha1,hb0,hb1⟩ := H.middle_coordinates
  have ha : H.a = (1-α) • H.v-β • H.w := by
    have hv : H.a = H.v-H.b := by simp [Hex.v]
    rw [hv,hb]; module
  have hc : H.c = -α • H.v+(1-β) • H.w := by
    have hw : H.c = H.w-H.b := by simp [Hex.w]
    rw [hw,hb]; module
  have hab : det2 H.a H.b = β*det2 H.v H.w := by rw [ha,hb]; simp [det2]; ring
  have hbc : det2 H.b H.c = α*det2 H.v H.w := by rw [hb,hc]; simp [det2]; ring
  have hac : det2 H.a H.c = (1-α-β)*det2 H.v H.w := by rw [ha,hc]; simp [det2]; ring
  rw [hab,hbc,hac]
  exact ⟨mul_nonneg hb0 hD,mul_nonneg ha0 hD,mul_nonneg (by linarith) hD⟩

#print axioms Hex.middle_coordinates
#print axioms Hex.fan_determinants_nonneg
end Certificate.Packing
