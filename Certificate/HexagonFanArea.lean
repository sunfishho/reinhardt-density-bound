import Certificate.HexagonFanAlgebra
import Certificate.AreaAssemblyHelpers

/-! Area of a centrally ordered six-triangle fan; zero-area triangles are
allowed, so degenerate hexagons do not require a limiting argument. -/
namespace Certificate.Packing
open Set MeasureTheory
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false

lemma triangle_inter_null_weak (φ : E →ₗ[ℝ] ℝ) (p q r s : E)
    (hp : φ p=0) (hq : 0 ≤ φ q) (hdeg : φ q=0 → det2 p q=0)
    (hr : φ r ≤ 0) (hs : φ s ≤ 0) : volume (Tri p q ∩ Tri r s)=0 := by
  rcases hq.eq_or_lt with h | h
  · apply measure_mono_null inter_subset_left
    rw [volume_Tri,hdeg h.symm]
    norm_num
  · exact triangles_inter_null_of_separation φ p q r s hp h hr hs

noncomputable def fanVertex (a b c : E) : Fin 6 → E := ![a,b,c,-a,-b,-c]
noncomputable def fanTriangle (a b c : E) (i : Fin 6) : Set E :=
  Tri (fanVertex a b c i) (fanVertex a b c (HVGeometry.next i))

lemma fanTriangle_inter_null (a b c : E)
    (hab : 0 ≤ det2 a b) (hbc : 0 ≤ det2 b c) (hac : 0 ≤ det2 a c) :
    Pairwise (fun i j => AEDisjoint volume (fanTriangle a b c i) (fanTriangle a b c j)) := by
  have h01 : volume (fanTriangle a b c 0 ∩ fanTriangle a b c 1)=0 := by
    change volume (Tri a b ∩ Tri b c)=0
    rw [Tri_swap a b]
    apply triangle_inter_null_weak (-detForm b) b a b c <;>
      simp only [LinearMap.neg_apply,detForm_apply,det2_neg_left,det2_neg_right,
        det2_self,det2_swap b a,det2_swap c a,det2_swap c b] <;> intros <;> linarith
  have h02 : volume (fanTriangle a b c 0 ∩ fanTriangle a b c 2)=0 := by
    change volume (Tri a b ∩ Tri c (-a))=0
    rw [Tri_swap a b]
    apply triangle_inter_null_weak (-detForm b) b a c (-a) <;>
      simp only [LinearMap.neg_apply,detForm_apply,det2_neg_left,det2_neg_right,
        det2_self,det2_swap b a,det2_swap c a,det2_swap c b] <;> intros <;> linarith
  have h03 : volume (fanTriangle a b c 0 ∩ fanTriangle a b c 3)=0 := by
    change volume (Tri a b ∩ Tri (-a) (-b))=0
    apply triangle_inter_null_weak (detForm a) a b (-a) (-b) <;>
      simp only [LinearMap.neg_apply,detForm_apply,det2_neg_left,det2_neg_right,
        det2_self,det2_swap b a,det2_swap c a,det2_swap c b] <;> intros <;> linarith
  have h04 : volume (fanTriangle a b c 0 ∩ fanTriangle a b c 4)=0 := by
    change volume (Tri a b ∩ Tri (-b) (-c))=0
    apply triangle_inter_null_weak (detForm a) a b (-b) (-c) <;>
      simp only [LinearMap.neg_apply,detForm_apply,det2_neg_left,det2_neg_right,
        det2_self,det2_swap b a,det2_swap c a,det2_swap c b] <;> intros <;> linarith
  have h05 : volume (fanTriangle a b c 0 ∩ fanTriangle a b c 5)=0 := by
    change volume (Tri a b ∩ Tri (-c) a)=0
    apply triangle_inter_null_weak (detForm a) a b (-c) a <;>
      simp only [LinearMap.neg_apply,detForm_apply,det2_neg_left,det2_neg_right,
        det2_self,det2_swap b a,det2_swap c a,det2_swap c b] <;> intros <;> linarith
  have h12 : volume (fanTriangle a b c 1 ∩ fanTriangle a b c 2)=0 := by
    change volume (Tri b c ∩ Tri c (-a))=0
    rw [Tri_swap b c]
    apply triangle_inter_null_weak (-detForm c) c b c (-a) <;>
      simp only [LinearMap.neg_apply,detForm_apply,det2_neg_left,det2_neg_right,
        det2_self,det2_swap b a,det2_swap c a,det2_swap c b] <;> intros <;> linarith
  have h13 : volume (fanTriangle a b c 1 ∩ fanTriangle a b c 3)=0 := by
    change volume (Tri b c ∩ Tri (-a) (-b))=0
    rw [Tri_swap b c]
    apply triangle_inter_null_weak (-detForm c) c b (-a) (-b) <;>
      simp only [LinearMap.neg_apply,detForm_apply,det2_neg_left,det2_neg_right,
        det2_self,det2_swap b a,det2_swap c a,det2_swap c b] <;> intros <;> linarith
  have h14 : volume (fanTriangle a b c 1 ∩ fanTriangle a b c 4)=0 := by
    change volume (Tri b c ∩ Tri (-b) (-c))=0
    apply triangle_inter_null_weak (detForm b) b c (-b) (-c) <;>
      simp only [LinearMap.neg_apply,detForm_apply,det2_neg_left,det2_neg_right,
        det2_self,det2_swap b a,det2_swap c a,det2_swap c b] <;> intros <;> linarith
  have h15 : volume (fanTriangle a b c 1 ∩ fanTriangle a b c 5)=0 := by
    change volume (Tri b c ∩ Tri (-c) a)=0
    apply triangle_inter_null_weak (detForm b) b c (-c) a <;>
      simp only [LinearMap.neg_apply,detForm_apply,det2_neg_left,det2_neg_right,
        det2_self,det2_swap b a,det2_swap c a,det2_swap c b] <;> intros <;> linarith
  have h23 : volume (fanTriangle a b c 2 ∩ fanTriangle a b c 3)=0 := by
    change volume (Tri c (-a) ∩ Tri (-a) (-b))=0
    rw [Tri_swap c (-a)]
    apply triangle_inter_null_weak (-detForm (-a)) (-a) c (-a) (-b) <;>
      simp only [LinearMap.neg_apply,detForm_apply,det2_neg_left,det2_neg_right,
        det2_self,det2_swap b a,det2_swap c a,det2_swap c b] <;> intros <;> linarith
  have h24 : volume (fanTriangle a b c 2 ∩ fanTriangle a b c 4)=0 := by
    change volume (Tri c (-a) ∩ Tri (-b) (-c))=0
    rw [Tri_swap c (-a)]
    apply triangle_inter_null_weak (-detForm (-a)) (-a) c (-b) (-c) <;>
      simp only [LinearMap.neg_apply,detForm_apply,det2_neg_left,det2_neg_right,
        det2_self,det2_swap b a,det2_swap c a,det2_swap c b] <;> intros <;> linarith
  have h25 : volume (fanTriangle a b c 2 ∩ fanTriangle a b c 5)=0 := by
    change volume (Tri c (-a) ∩ Tri (-c) a)=0
    apply triangle_inter_null_weak (detForm c) c (-a) (-c) a <;>
      simp only [LinearMap.neg_apply,detForm_apply,det2_neg_left,det2_neg_right,
        det2_self,det2_swap b a,det2_swap c a,det2_swap c b] <;> intros <;> linarith
  have h34 : volume (fanTriangle a b c 3 ∩ fanTriangle a b c 4)=0 := by
    change volume (Tri (-a) (-b) ∩ Tri (-b) (-c))=0
    rw [Tri_swap (-a) (-b)]
    apply triangle_inter_null_weak (-detForm (-b)) (-b) (-a) (-b) (-c) <;>
      simp only [LinearMap.neg_apply,detForm_apply,det2_neg_left,det2_neg_right,
        det2_self,det2_swap b a,det2_swap c a,det2_swap c b] <;> intros <;> linarith
  have h35 : volume (fanTriangle a b c 3 ∩ fanTriangle a b c 5)=0 := by
    change volume (Tri (-a) (-b) ∩ Tri (-c) a)=0
    rw [Tri_swap (-a) (-b)]
    apply triangle_inter_null_weak (-detForm (-b)) (-b) (-a) (-c) a <;>
      simp only [LinearMap.neg_apply,detForm_apply,det2_neg_left,det2_neg_right,
        det2_self,det2_swap b a,det2_swap c a,det2_swap c b] <;> intros <;> linarith
  have h45 : volume (fanTriangle a b c 4 ∩ fanTriangle a b c 5)=0 := by
    change volume (Tri (-b) (-c) ∩ Tri (-c) a)=0
    rw [Tri_swap (-b) (-c)]
    apply triangle_inter_null_weak (-detForm (-c)) (-c) (-b) (-c) a <;>
      simp only [LinearMap.neg_apply,detForm_apply,det2_neg_left,det2_neg_right,
        det2_self,det2_swap b a,det2_swap c a,det2_swap c b] <;> intros <;> linarith
  intro i j hij
  change volume (fanTriangle a b c i ∩ fanTriangle a b c j)=0
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · exact h01
  · exact h02
  · exact h03
  · exact h04
  · exact h05
  · rw [Set.inter_comm]; exact h01
  · exact (hij rfl).elim
  · exact h12
  · exact h13
  · exact h14
  · exact h15
  · rw [Set.inter_comm]; exact h02
  · rw [Set.inter_comm]; exact h12
  · exact (hij rfl).elim
  · exact h23
  · exact h24
  · exact h25
  · rw [Set.inter_comm]; exact h03
  · rw [Set.inter_comm]; exact h13
  · rw [Set.inter_comm]; exact h23
  · exact (hij rfl).elim
  · exact h34
  · exact h35
  · rw [Set.inter_comm]; exact h04
  · rw [Set.inter_comm]; exact h14
  · rw [Set.inter_comm]; exact h24
  · rw [Set.inter_comm]; exact h34
  · exact (hij rfl).elim
  · exact h45
  · rw [Set.inter_comm]; exact h05
  · rw [Set.inter_comm]; exact h15
  · rw [Set.inter_comm]; exact h25
  · rw [Set.inter_comm]; exact h35
  · rw [Set.inter_comm]; exact h45
  · exact (hij rfl).elim

/-- The union area is the sum of the three oriented determinants. -/
theorem volume_hexagon_fan (a b c : E)
    (hab : 0 ≤ det2 a b) (hbc : 0 ≤ det2 b c) (hac : 0 ≤ det2 a c) :
    volume (⋃ i : Fin 6, fanTriangle a b c i) =
      ENNReal.ofReal (det2 a b+det2 b c+det2 a c) := by
  rw [measure_iUnion₀ (fanTriangle_inter_null a b c hab hbc hac)
    (fun i => (isCompact_Tri _ _).measurableSet.nullMeasurableSet),tsum_fintype]
  simp only [Fin.sum_univ_six]
  change volume (Tri a b)+volume (Tri b c)+volume (Tri c (-a))+
    volume (Tri (-a) (-b))+volume (Tri (-b) (-c))+volume (Tri (-c) a) = _
  simp only [volume_Tri,det2_neg_left,det2_neg_right,det2_swap c a,neg_neg,
    abs_of_nonneg hab,abs_of_nonneg hbc,abs_of_nonneg hac]
  repeat rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  ring

#print axioms volume_hexagon_fan
end Certificate.Packing
