import Certificate.PackingLattice

/-! Plane triangle areas for the Hales–Vajjha geometric estimate.
The segment-nullity and triangle-containment proofs are adapted from the
recovered Fable lattice reduction; the exact area and homothety results
below are verified here. -/
namespace Certificate.Packing
open MeasureTheory Set Pointwise
set_option maxHeartbeats 0

lemma segment_subset_vadd_F (p q w : E) (ε : ℝ) :
    segment ℝ p q ⊆ p +ᵥ F (q - p) (ε • w) := by
  rintro z ⟨a, b, ha, hb, hab, rfl⟩
  refine Set.mem_vadd_set.2 ⟨b • (q - p), ⟨![b, 0], ?_, ?_⟩, ?_⟩
  · rw [Set.mem_Icc]
    constructor <;> intro i <;> fin_cases i <;> simp [hb] <;> linarith
  · simp [Fin.sum_univ_two]
  · rw [vadd_eq_add]
    have : a = 1 - b := by linarith
    subst this
    module

lemma det2_smul_right (v w : E) (ε : ℝ) : det2 v (ε • w) = ε * det2 v w := by
  simp only [det2, PiLp.smul_apply, smul_eq_mul]; ring

lemma volume_segment (p q : E) : volume (segment ℝ p q) = 0 := by
  set w : E := WithLp.toLp 2 ![-((q - p) 1), (q - p) 0] with hw
  set C : ℝ := |det2 (q - p) w| with hC
  have key : ∀ ε : ℝ, 0 < ε → volume (segment ℝ p q) ≤ ENNReal.ofReal (ε * C) := by
    intro ε hε
    calc volume (segment ℝ p q) ≤ volume (p +ᵥ F (q - p) (ε • w)) :=
          measure_mono (segment_subset_vadd_F p q w ε)
      _ = ENNReal.ofReal |det2 (q - p) (ε • w)| := by rw [measure_vadd, volume_F]
      _ = ENNReal.ofReal (ε * C) := by rw [det2_smul_right, abs_mul, abs_of_pos hε]
  apply le_antisymm _ (zero_le)
  apply ENNReal.le_of_forall_pos_le_add
  intro δ hδ _
  rw [zero_add]
  have hC0 : 0 ≤ C := abs_nonneg _
  have hδ' : (0:ℝ) < (δ:ℝ) := NNReal.coe_pos.2 hδ
  calc volume (segment ℝ p q) ≤ ENNReal.ofReal ((δ:ℝ) / (C + 1) * C) := key _ (by positivity)
    _ ≤ ENNReal.ofReal (δ:ℝ) := by
        apply ENNReal.ofReal_le_ofReal
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        nlinarith
    _ = (δ : ENNReal) := ENNReal.ofReal_coe_nnreal

/-- closed triangle with vertices `0, p, q` -/
def Tri (p q : E) : Set E :=
  (fun ab : ℝ × ℝ => ab.1 • p + ab.2 • q) '' {ab | 0 ≤ ab.1 ∧ 0 ≤ ab.2 ∧ ab.1 + ab.2 ≤ 1}

lemma isCompact_Tri (p q : E) : IsCompact (Tri p q) := by
  apply IsCompact.image _ (by fun_prop)
  apply IsCompact.of_isClosed_subset
    (isCompact_Icc.prod isCompact_Icc : IsCompact (Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1))
  · show IsClosed ({ab : ℝ × ℝ | 0 ≤ ab.1} ∩ ({ab | 0 ≤ ab.2} ∩ {ab | ab.1 + ab.2 ≤ 1}))
    exact (isClosed_le continuous_const continuous_fst).inter
      ((isClosed_le continuous_const continuous_snd).inter
        (isClosed_le (continuous_fst.add continuous_snd) continuous_const))
  · rintro ⟨a, b⟩ ⟨ha, hb, hab⟩
    exact ⟨⟨ha, by linarith⟩, ⟨hb, by linarith⟩⟩

lemma isCompact_F (v w : E) : IsCompact (F v w) := by
  unfold F parallelepiped
  exact isCompact_Icc.image (by fun_prop)

lemma F_subset_Tri_union (p q : E) :
    F p q ⊆ Tri p q ∪ ((p + q) +ᵥ ((-1 : ℝ) • Tri p q)) := by
  rintro z ⟨t, ht, rfl⟩
  rw [Set.mem_Icc] at ht
  have h0 : ∀ i, 0 ≤ t i := fun i => ht.1 i
  have h1 : ∀ i, t i ≤ 1 := fun i => ht.2 i
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  by_cases h : t 0 + t 1 ≤ 1
  · left; exact ⟨(t 0, t 1), ⟨h0 0, h0 1, h⟩, rfl⟩
  · right
    refine Set.mem_vadd_set.2 ⟨(-1 : ℝ) • ((1 - t 0) • p + (1 - t 1) • q),
      Set.smul_mem_smul_set ⟨(1 - t 0, 1 - t 1), ⟨by linarith [h1 0], by linarith [h1 1], by linarith⟩, rfl⟩, ?_⟩
    rw [vadd_eq_add]; module

lemma volume_Tri_ge (p q : E) : ENNReal.ofReal |det2 p q| ≤ 2 * volume (Tri p q) := by
  have h1 : volume (F p q) ≤ volume (Tri p q) + volume ((p + q) +ᵥ ((-1 : ℝ) • Tri p q)) :=
    (measure_mono (F_subset_Tri_union p q)).trans (measure_union_le _ _)
  rw [volume_F, measure_vadd, Measure.addHaar_smul, finrank_euclideanSpace_fin] at h1
  norm_num at h1
  rw [two_mul]; exact h1

lemma Tri_subset_of_mem (K : Set E) (hK : Convex ℝ K) {p q r : E}
    (hp : p ∈ K) (hq : q ∈ K) (hr : r ∈ K) : p +ᵥ Tri (q - p) (r - p) ⊆ K := by
  intro z hz
  obtain ⟨y, ⟨⟨α, β⟩, ⟨hα, hβ, hαβ⟩, rfl⟩, rfl⟩ := Set.mem_vadd_set.1 hz
  simp only [vadd_eq_add]
  have hcv : Convex ℝ K := hK
  by_cases h0 : α + β = 0
  · have hα0 : α = 0 := by linarith
    have hβ0 : β = 0 := by linarith
    subst hα0 hβ0; simpa using hp
  · have hpos : 0 < α + β := lt_of_le_of_ne (by linarith) (Ne.symm h0)
    have hz1 : (α / (α + β)) • q + (β / (α + β)) • r ∈ K :=
      hcv hq hr (by positivity) (by positivity) (by field_simp)
    have hz2 : (1 - (α + β)) • p + (α + β) • ((α / (α + β)) • q + (β / (α + β)) • r) ∈ K :=
      hcv hp hz1 (by linarith) hpos.le (by ring)
    convert hz2 using 1
    rw [smul_add, smul_smul, smul_smul, mul_div_cancel₀ _ h0, mul_div_cancel₀ _ h0]
    module


lemma Tri_subset_F (p q : E) : Tri p q ⊆ F p q := by
  rintro z ⟨⟨a,b⟩, ⟨ha,hb,hab⟩, rfl⟩
  refine ⟨![a,b], ?_, ?_⟩
  · rw [Set.mem_Icc]
    constructor <;> intro i <;> fin_cases i <;> simp <;> linarith
  · simp [Fin.sum_univ_two]

lemma reflected_Tri_subset_F (p q : E) :
    (p+q) +ᵥ ((-1:ℝ) • Tri p q) ⊆ F p q := by
  intro z hz
  obtain ⟨y, hy, rfl⟩ := Set.mem_vadd_set.1 hz
  obtain ⟨u, ⟨⟨a,b⟩, ⟨ha,hb,hab⟩, rfl⟩, rfl⟩ := Set.mem_smul_set.1 hy
  refine ⟨![1-a,1-b], ?_, ?_⟩
  · rw [Set.mem_Icc]
    constructor <;> intro i <;> fin_cases i <;> simp <;> linarith
  · simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, vadd_eq_add]
    module

lemma Tri_inter_reflected_subset_segment (p q : E) (hd : det2 p q ≠ 0) :
    Tri p q ∩ ((p+q) +ᵥ ((-1:ℝ) • Tri p q)) ⊆ segment ℝ p q := by
  rintro z ⟨⟨⟨a,b⟩, ⟨ha,hb,hab⟩, rfl⟩, hz⟩
  obtain ⟨y, hy, hyz⟩ := Set.mem_vadd_set.1 hz
  obtain ⟨u, ⟨⟨c,d⟩, ⟨hc,hd',hcd⟩, rfl⟩, rfl⟩ := Set.mem_smul_set.1 hy
  have he0 := congrArg (fun x : E => x 0) hyz
  have he1 := congrArg (fun x : E => x 1) hyz
  simp only [vadd_eq_add, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at he0 he1
  have hac : a+c=1 := by
    apply (mul_left_inj' hd).1
    dsimp [det2]
    linear_combination -q 1 * he0 + q 0 * he1
  have hbd : b+d=1 := by
    apply (mul_left_inj' hd).1
    dsimp [det2]
    linear_combination p 1 * he0 - p 0 * he1
  exact ⟨a,b,ha,hb,by linarith,rfl⟩

/-- Exact Lebesgue area, including degenerate triangles. -/
theorem volume_Tri (p q : E) :
    volume (Tri p q) = ENNReal.ofReal (|det2 p q| / 2) := by
  by_cases hd : det2 p q = 0
  · have h := measure_mono (μ := volume) (Tri_subset_F p q)
    rw [volume_F, hd, abs_zero, ENNReal.ofReal_zero] at h
    simp only [hd, abs_zero, zero_div, ENNReal.ofReal_zero]
    exact le_antisymm h zero_le
  · have hi : volume (Tri p q ∩ ((p+q) +ᵥ ((-1:ℝ) • Tri p q))) = 0 :=
      measure_mono_null (Tri_inter_reflected_subset_segment p q hd) (volume_segment p q)
    have hu : Tri p q ∪ ((p+q) +ᵥ ((-1:ℝ) • Tri p q)) = F p q :=
      subset_antisymm (union_subset (Tri_subset_F p q) (reflected_Tri_subset_F p q))
        (F_subset_Tri_union p q)
    have hm := measure_union_add_inter (μ := volume) (Tri p q)
      (((isCompact_Tri p q).smul (-1:ℝ)).vadd (p+q)).measurableSet
    rw [hu, hi, add_zero, volume_F, measure_vadd, Measure.addHaar_smul,
      finrank_euclideanSpace_fin] at hm
    norm_num at hm
    have hfin : volume (Tri p q) ≠ ⊤ := (isCompact_Tri p q).measure_lt_top.ne
    apply (ENNReal.toReal_eq_toReal_iff' hfin ENNReal.ofReal_ne_top).1
    rw [ENNReal.toReal_ofReal (by positivity)]
    have hh := congrArg ENNReal.toReal hm
    rw [ENNReal.toReal_add hfin hfin, ENNReal.toReal_ofReal (abs_nonneg _)] at hh
    linarith

/-- Area of a triangle at an arbitrary base point. -/
theorem volume_triangle (p q r : E) :
    (volume (p +ᵥ Tri (q-p) (r-p))).toReal = |det2 (q-p) (r-p)|/2 := by
  rw [measure_vadd, volume_Tri, ENNReal.toReal_ofReal (by positivity)]

end Certificate.Packing
