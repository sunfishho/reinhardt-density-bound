import Certificate.RegularHexagonArea

/-! Measure-theoretic assembly tools for the HV area bound. -/
namespace Certificate.Packing
open MeasureTheory Set Pointwise
set_option maxHeartbeats 0

noncomputable def triangle (p q r : E) : Set E := p +ᵥ Tri (q-p) (r-p)

lemma isCompact_triangle (p q r : E) : IsCompact (triangle p q r) :=
  (isCompact_Tri _ _).vadd _

lemma convex_superlevel (φ : E →ₗ[ℝ] ℝ) (c : ℝ) : Convex ℝ {x | c ≤ φ x} := by
  intro x hx y hy a b ha hb hab
  change c ≤ φ (a • x+b • y)
  rw [map_add,map_smul,map_smul,smul_eq_mul,smul_eq_mul]
  have h1 := mul_le_mul_of_nonneg_left hx ha
  have h2 := mul_le_mul_of_nonneg_left hy hb
  calc
    c = a*c+b*c := by rw [← add_mul,hab,one_mul]
    _ ≤ a*φ x+b*φ y := add_le_add h1 h2

lemma triangle_superlevel (φ : E →ₗ[ℝ] ℝ) (c : ℝ) {p q r : E}
    (hp : c ≤ φ p) (hq : c ≤ φ q) (hr : c ≤ φ r) :
    ∀ x ∈ triangle p q r, c ≤ φ x :=
  Tri_subset_of_mem _ (convex_superlevel φ c) hp hq hr

lemma triangle_sublevel (φ : E →ₗ[ℝ] ℝ) (c : ℝ) {p q r : E}
    (hp : φ p ≤ c) (hq : φ q ≤ c) (hr : φ r ≤ c) :
    ∀ x ∈ triangle p q r, φ x ≤ c := by
  have h := triangle_superlevel (-φ) (-c) (p:=p) (q:=q) (r:=r)
    (by simpa using hp) (by simpa using hq) (by simpa using hr)
  simpa using h

lemma measure_level_zero (φ : E →ₗ[ℝ] ℝ) (hφ : φ ≠ 0) (c : ℝ) :
    volume {x | φ x=c} = 0 := by
  have hk : φ.ker ≠ ⊤ := by
    intro hk
    apply hφ
    ext x
    have hx : x ∈ φ.ker := by rw [hk]; trivial
    exact hx
  by_cases he : ∃ p, φ p=c
  · obtain ⟨p,hp⟩ := he
    have heq : {x | φ x=c} = p +ᵥ (φ.ker : Set E) := by
      ext x
      constructor
      · intro hx
        refine Set.mem_vadd_set.2 ⟨x-p,?_,by simp⟩
        change φ (x-p)=0
        rw [map_sub,hx,hp,sub_self]
      · intro hx
        obtain ⟨y,hy,rfl⟩ := Set.mem_vadd_set.1 hx
        change φ (p+y)=c
        rw [map_add,hp,show φ y=0 from hy,add_zero]
    rw [heq,measure_vadd]
    exact Measure.addHaar_submodule volume φ.ker hk
  · have heq : {x | φ x=c} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.2
      intro x hx
      exact he ⟨x,hx⟩
    rw [heq,measure_empty]

lemma measure_inter_zero_of_separation (φ : E →ₗ[ℝ] ℝ) (hφ : φ ≠ 0) (c : ℝ)
    {A B : Set E} (hA : ∀ x ∈ A, c ≤ φ x) (hB : ∀ x ∈ B, φ x ≤ c) :
    volume (A ∩ B) = 0 := by
  apply measure_mono_null (t := {x | φ x=c})
  · rintro x ⟨ha,hb⟩
    exact le_antisymm (hB x hb) (hA x ha)
  · exact measure_level_zero φ hφ c

lemma triangleArea_swap (p q r : E) : triangleArea p q r = triangleArea p r q := by
  rw [triangleArea_eq_det,triangleArea_eq_det]
  have h : det2 (q-p) (r-p) = -det2 (r-p) (q-p) := by unfold det2; ring
  rw [h,abs_neg]

end Certificate.Packing
