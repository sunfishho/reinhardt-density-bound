import Certificate.HexagonRelabeling

/-! A hexagon with a collapsed side or redundant supporting strip is an
invertible linear image of a square. The statement concerns its actual set. -/
namespace Certificate.Packing
open Set
set_option maxHeartbeats 0

lemma linear_forms_eq_of_pair (f g : E →ₗ[ℝ] ℝ) (u v : E) (hd : det2 u v ≠ 0)
    (hu : f u=g u) (hv : f v=g v) : f=g := by
  ext x
  obtain ⟨z,rfl⟩ := (pairFrame u v hd).surjective x
  simp [map_add,map_smul,hu,hv]

lemma abs_convex_comb_le_one {a b x y : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1)
    (hx : |x| ≤ 1) (hy : |y| ≤ 1) : |a*x+b*y| ≤ 1 := by
  calc
    |a*x+b*y| ≤ |a*x|+|b*y| := abs_add_le _ _
    _ = a*|x|+b*|y| := by rw [abs_mul,abs_mul,abs_of_nonneg ha,abs_of_nonneg hb]
    _ ≤ a*1+b*1 := add_le_add (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hb)
    _ = 1 := by simpa using hab

lemma exists_square_image_of_two_strips (S : Set E) (f g : E →ₗ[ℝ] ℝ) (u v : E)
    (hd : det2 (HVGeometry.pairLinear f g u) (HVGeometry.pairLinear f g v) ≠ 0)
    (he : S={x | |f x| ≤ 1 ∧ |g x| ≤ 1}) : ∃ L : E ≃ₗ[ℝ] E, L '' S=square := by
  let F := HVGeometry.pairLinear f g
  have hF : LinearMap.det F ≠ 0 := by
    intro hz
    have hh := det2_linearMap F u v
    rw [hz,zero_mul] at hh
    exact hd hh
  let L := F.equivOfDetNeZero hF
  refine ⟨L,?_⟩
  have hcoord (x : E) : (L x) 0=f x ∧ (L x) 1=g x := by exact ⟨rfl,rfl⟩
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    rw [he] at hy
    exact hy
  · intro hx
    refine ⟨L.symm x,?_,L.apply_symm_apply x⟩
    rw [he]
    have hh := hcoord (L.symm x)
    rw [L.apply_symm_apply] at hh
    change |x 0| ≤ 1 ∧ |x 1| ≤ 1 at hx
    change |f (L.symm x)| ≤ 1 ∧ |g (L.symm x)| ≤ 1
    rw [← hh.1,← hh.2]
    exact hx

namespace Hex

lemma exists_square_image_of_c_eq_one (H : Hex) (hc : H.φ₁ H.c=1) :
    ∃ L : E ≃ₗ[ℝ] E, L '' H.set=square := by
  let F := HVGeometry.pairLinear H.φ₁ H.φ₃
  have hi : det2 (F H.a) (F H.c)=2 := by
    norm_num [F,HVGeometry.pairLinear,det2,point,H.ha₁,H.ha₃,H.hc₃,hc]
  have hd : det2 H.a H.c ≠ 0 := by
    intro hz
    rw [det2_linearMap,hz,mul_zero] at hi
    norm_num at hi
  have hform : H.φ₂=((H.φ₂ H.a+1)/2) • H.φ₁+((1-H.φ₂ H.a)/2) • H.φ₃ := by
    apply linear_forms_eq_of_pair _ _ H.a H.c hd
    · simp [H.ha₁,H.ha₃]; ring
    · simp [H.hc₂,H.hc₃,hc]; ring
  apply exists_square_image_of_two_strips H.set H.φ₁ H.φ₃ H.a H.c (by rw [hi]; norm_num)
  ext x
  constructor
  · intro hx; exact ⟨hx.1,hx.2.2⟩
  · rintro ⟨h1,h3⟩
    refine ⟨h1,?_,h3⟩
    rw [hform]
    change |(H.φ₂ H.a+1)/2*H.φ₁ x+(1-H.φ₂ H.a)/2*H.φ₃ x| ≤ 1
    have ha := abs_le.1 H.hin_a
    exact abs_convex_comb_le_one (by linarith) (by linarith) (by ring) h1 h3

lemma exists_square_image_of_c_eq_neg_one (H : Hex) (hc : H.φ₁ H.c= -1) :
    ∃ L : E ≃ₗ[ℝ] E, L '' H.set=square := by
  let F := HVGeometry.pairLinear H.φ₁ H.φ₂
  have hi : det2 (F H.b) (F H.c)=2 := by
    norm_num [F,HVGeometry.pairLinear,det2,point,H.hb₁,H.hb₂,H.hc₂,hc]
  have hd : det2 H.b H.c ≠ 0 := by
    intro hz
    rw [det2_linearMap,hz,mul_zero] at hi
    norm_num at hi
  have hform : H.φ₃=((1-H.φ₃ H.b)/2) • (-H.φ₁)+((H.φ₃ H.b+1)/2) • H.φ₂ := by
    apply linear_forms_eq_of_pair _ _ H.b H.c hd
    · simp [H.hb₁,H.hb₂]; ring
    · simp [H.hc₃,H.hc₂,hc]; ring
  apply exists_square_image_of_two_strips H.set H.φ₁ H.φ₂ H.b H.c (by rw [hi]; norm_num)
  ext x
  constructor
  · intro hx; exact ⟨hx.1,hx.2.1⟩
  · rintro ⟨h1,h2⟩
    refine ⟨h1,h2,?_⟩
    rw [hform]
    change |(1-H.φ₃ H.b)/2*(-H.φ₁ x)+(H.φ₃ H.b+1)/2*H.φ₂ x| ≤ 1
    have hb := abs_le.1 H.hin_b
    exact abs_convex_comb_le_one (by linarith) (by linarith) (by ring) (by simpa using h1) h2

lemma exists_square_image_of_abs_c_eq_one (H : Hex) (hc : |H.φ₁ H.c|=1) :
    ∃ L : E ≃ₗ[ℝ] E, L '' H.set=square := by
  rcases (abs_eq (by norm_num : (0:ℝ) ≤ 1)).1 hc with h | h
  · exact H.exists_square_image_of_c_eq_one h
  · exact H.exists_square_image_of_c_eq_neg_one h

theorem exists_square_image_of_not_strict (H : Hex) (hs : ¬ H.Strict) :
    ∃ L : E ≃ₗ[ℝ] E, L '' H.set=square := by
  by_cases ha : |H.φ₂ H.a| < 1
  · by_cases hb : |H.φ₃ H.b| < 1
    · exact H.exists_square_image_of_abs_c_eq_one
        (le_antisymm H.hin_c (le_of_not_gt (fun hc => hs ⟨ha,hb,hc⟩)))
    · have he : |H.rotate.rotate.φ₁ H.rotate.rotate.c|=1 := by
        change |H.φ₃ (-H.b)|=1
        simpa using le_antisymm H.hin_b (le_of_not_gt hb)
      obtain ⟨L,hL⟩ := H.rotate.rotate.exists_square_image_of_abs_c_eq_one he
      exact ⟨L,by simpa only [rotate_set] using hL⟩
  · have he : |H.rotate.φ₁ H.rotate.c|=1 := by
      change |H.φ₂ (-H.a)|=1
      simpa using le_antisymm H.hin_a (le_of_not_gt ha)
    obtain ⟨L,hL⟩ := H.rotate.exists_square_image_of_abs_c_eq_one he
    exact ⟨L,by simpa only [rotate_set] using hL⟩

#print axioms exists_square_image_of_not_strict
end Hex
end Certificate.Packing
