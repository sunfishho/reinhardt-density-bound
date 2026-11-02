import Certificate.TriangleArea
import Certificate.CornerCut

/-! Actual area of the competing corner-cut hexagon. -/
namespace Certificate.Packing
open MeasureTheory Set Pointwise
set_option maxHeartbeats 0

def square : Set E := {x | |x 0| ≤ 1 ∧ |x 1| ≤ 1}
noncomputable def cornerTriangle (d e : ℝ) : Set E :=
  point 1 (-1) +ᵥ Tri (point (-d) 0) (point 0 e)

lemma mem_cornerTriangle_iff {d e : ℝ} (hd : 0 < d) (he : 0 < e) (x : E) :
    x ∈ cornerTriangle d e ↔ x 0 ≤ 1 ∧ -1 ≤ x 1 ∧ cornerDistance d e x ≤ 1 := by
  constructor
  · intro hx
    obtain ⟨y, ⟨⟨a,b⟩, ⟨ha,hb,hab⟩, rfl⟩, rfl⟩ := Set.mem_vadd_set.1 hx
    simp only [vadd_eq_add, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
      point_zero, point_one, mul_zero, add_zero, zero_add]
    refine ⟨by nlinarith, by nlinarith [mul_nonneg hb he.le], ?_⟩
    have hh : cornerDistance d e (point 1 (-1) + (a • point (-d) 0 + b • point 0 e)) = a+b := by
      simp [cornerDistance, hd.ne', he.ne']
      <;> field_simp <;> ring
    exact hh.le.trans hab
  · rintro ⟨hx,hy,hc⟩
    refine Set.mem_vadd_set.2 ⟨((1-x 0)/d) • point (-d) 0 + ((x 1+1)/e) • point 0 e,
      ⟨((1-x 0)/d,(x 1+1)/e), ⟨div_nonneg (by linarith) hd.le,
        div_nonneg (by linarith) he.le, hc⟩, rfl⟩, ?_⟩
    ext i
    fin_cases i <;> simp [vadd_eq_add, point] <;> field_simp <;> ring

lemma cornerTriangle_subset_square {d e : ℝ} (hd : 0 < d) (he : 0 < e)
    (hd1 : d ≤ 1) (he1 : e ≤ 1) : cornerTriangle d e ⊆ square := by
  intro x hx
  obtain ⟨y, ⟨⟨a,b⟩, ⟨ha,hb,hab⟩, rfl⟩, rfl⟩ := Set.mem_vadd_set.1 hx
  change |1+(a*(-d)+b*0)| ≤ 1 ∧ |-1+(a*0+b*e)| ≤ 1
  have ha1 : a ≤ 1 := by linarith
  have hb1 : b ≤ 1 := by linarith
  have had := mul_le_one₀ ha1 hd.le hd1
  have hbe := mul_le_one₀ hb1 he.le he1
  constructor <;> rw [abs_le] <;> constructor <;> nlinarith [mul_nonneg ha hd.le, mul_nonneg hb he.le]

lemma mem_cutHex_iff {d e : ℝ} (hd : 0 < d) (he : 0 < e)
    (hd1 : d ≤ 1) (he1 : e ≤ 1) (x : E) :
    x ∈ (cutHex d e hd he hd1 he1).set ↔
      x ∈ square ∧ 1 ≤ cornerDistance d e x ∧ 1 ≤ cornerDistance d e (-x) := by
  change (|x 0| ≤ 1 ∧ |x 1| ≤ 1 ∧ |cutForm d e x| ≤ 1) ↔ _
  simp only [cutForm_apply, abs_le]
  rw [le_div_iff₀ (cut_denom_pos hd he he1),
    div_le_iff₀ (cut_denom_pos hd he he1), cornerDistance_ge_iff hd he x,
    cornerDistance_ge_iff hd he (-x)]
  simp only [square, Set.mem_setOf_eq, PiLp.neg_apply, abs_le]
  constructor
  · rintro ⟨hx,hy,h1,h2⟩; exact ⟨⟨hx,hy⟩,by linarith,by linarith⟩
  · rintro ⟨⟨hx,hy⟩,h1,h2⟩; exact ⟨hx,hy,by linarith,by linarith⟩

lemma cornerTriangle_level_one {d e : ℝ} (hd : 0 < d) (he : 0 < e) {x : E}
    (hx : x ∈ cornerTriangle d e) (hc : 1 ≤ cornerDistance d e x) :
    x ∈ segment ℝ (point (1-d) (-1)) (point 1 (-1+e)) := by
  obtain ⟨y, ⟨⟨a,b⟩, ⟨ha,hb,hab⟩, rfl⟩, rfl⟩ := Set.mem_vadd_set.1 hx
  have hh : cornerDistance d e (point 1 (-1) + (a • point (-d) 0 + b • point 0 e)) = a+b := by
    simp [cornerDistance, hd.ne', he.ne'] <;> field_simp <;> ring
  change 1 ≤ cornerDistance d e (point 1 (-1) + (a • point (-d) 0 + b • point 0 e)) at hc
  rw [hh] at hc
  have hab' : a+b=1 := le_antisymm hab hc
  refine ⟨a,b,ha,hb,hab',?_⟩
  ext i
  fin_cases i <;> simp [vadd_eq_add, point] <;> nlinarith

lemma volume_cornerTriangle {d e : ℝ} (hd : 0 < d) (he : 0 < e) :
    volume (cornerTriangle d e) = ENNReal.ofReal (d*e/2) := by
  rw [cornerTriangle, measure_vadd, volume_Tri]
  congr 1
  simp [det2, point, abs_mul, abs_of_pos hd, abs_of_pos he]

lemma square_eq_parallelepiped :
    square = point 1 (-1) +ᵥ F (point (-2) 0) (point 0 2) := by
  ext x
  constructor
  · rintro ⟨hx,hy⟩
    have hx' := abs_le.1 hx
    have hy' := abs_le.1 hy
    refine Set.mem_vadd_set.2 ⟨((1-x 0)/2) • point (-2) 0 + ((x 1+1)/2) • point 0 2,
      ⟨![(1-x 0)/2,(x 1+1)/2], ?_, ?_⟩, ?_⟩
    · rw [Set.mem_Icc]
      constructor <;> intro i <;> fin_cases i <;> simp <;> linarith
    · simp [Fin.sum_univ_two]
    · ext i; fin_cases i <;> simp [vadd_eq_add, point] <;> ring
  · intro hx
    obtain ⟨y, ⟨t,ht,rfl⟩, rfl⟩ := Set.mem_vadd_set.1 hx
    have h0 := ht.1 0
    have h1 := ht.2 0
    have h2 := ht.1 1
    have h3 := ht.2 1
    change 0 ≤ t 0 at h0
    change t 0 ≤ 1 at h1
    change 0 ≤ t 1 at h2
    change t 1 ≤ 1 at h3
    simp only [F, parallelepiped, vadd_eq_add, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one] at *
    change |1+((t 0)*(-2)+(t 1)*0)| ≤ 1 ∧ |-1+((t 0)*0+(t 1)*2)| ≤ 1
    constructor <;> rw [abs_le] <;> constructor <;> nlinarith

lemma volume_square : volume square = 4 := by
  rw [square_eq_parallelepiped, measure_vadd, volume_F]
  norm_num [det2, point]

lemma isCompact_square : IsCompact square := by
  rw [square_eq_parallelepiped]
  exact (isCompact_F _ _).vadd _

lemma square_neg {x : E} (hx : x ∈ square) : -x ∈ square := by
  simpa [square] using hx

lemma cutHex_neg {d e : ℝ} (hd : 0 < d) (he : 0 < e)
    (hd1 : d ≤ 1) (he1 : e ≤ 1) {x : E}
    (hx : x ∈ (cutHex d e hd he hd1 he1).set) :
    -x ∈ (cutHex d e hd he hd1 he1).set := by
  simpa only [Hex.set, Set.mem_setOf_eq, map_neg, abs_neg] using hx

lemma cutHex_inter_cornerTriangle_null {d e : ℝ} (hd : 0 < d) (he : 0 < e)
    (hd1 : d ≤ 1) (he1 : e ≤ 1) :
    volume ((cutHex d e hd he hd1 he1).set ∩ cornerTriangle d e) = 0 := by
  apply measure_mono_null (t := segment ℝ (point (1-d) (-1)) (point 1 (-1+e)))
  · rintro x ⟨hx,hc⟩
    exact cornerTriangle_level_one hd he hc ((mem_cutHex_iff hd he hd1 he1 x).1 hx).2.1
  · exact volume_segment _ _

lemma cornerTriangle_disjoint_neg {d e : ℝ} (hd : 0 < d) (he : 0 < e)
    (he1 : e ≤ 1) :
    Disjoint (cornerTriangle d e) ((-1:ℝ) • cornerTriangle d e) := by
  rw [Set.disjoint_left]
  intro x hx hn
  have hx' := ((mem_cornerTriangle_iff hd he x).1 hx).2.2
  obtain ⟨y,hy,hyx⟩ := Set.mem_smul_set.1 hn
  have hyx' : y = -x := by rw [← hyx]; simp
  subst y
  have hn' := ((mem_cornerTriangle_iff hd he (-x)).1 hy).2.2
  unfold cornerDistance at hx' hn'
  rw [div_add_div _ _ hd.ne' he.ne', div_le_iff₀ (mul_pos hd he)] at hx' hn'
  simp only [PiLp.neg_apply] at hn'
  have hh := cut_denom_pos hd he he1
  nlinarith

lemma square_eq_cutHex_union {d e : ℝ} (hd : 0 < d) (he : 0 < e)
    (hd1 : d ≤ 1) (he1 : e ≤ 1) :
    square = (cutHex d e hd he hd1 he1).set ∪
      (cornerTriangle d e ∪ ((-1:ℝ) • cornerTriangle d e)) := by
  ext x
  constructor
  · intro hx
    by_cases hc : 1 ≤ cornerDistance d e x
    · by_cases hn : 1 ≤ cornerDistance d e (-x)
      · exact Or.inl ((mem_cutHex_iff hd he hd1 he1 x).2 ⟨hx,hc,hn⟩)
      · right; right
        refine Set.mem_smul_set.2 ⟨-x, ?_, by simp⟩
        exact (mem_cornerTriangle_iff hd he (-x)).2
          ⟨(abs_le.1 (square_neg hx).1).2, (abs_le.1 (square_neg hx).2).1, (not_le.1 hn).le⟩
    · right; left
      exact (mem_cornerTriangle_iff hd he x).2
        ⟨(abs_le.1 hx.1).2, (abs_le.1 hx.2).1, (not_le.1 hc).le⟩
  · rintro (hx | hx | hx)
    · exact ((mem_cutHex_iff hd he hd1 he1 x).1 hx).1
    · exact cornerTriangle_subset_square hd he hd1 he1 hx
    · obtain ⟨y,hy,rfl⟩ := Set.mem_smul_set.1 hx
      simpa using square_neg (cornerTriangle_subset_square hd he hd1 he1 hy)

/-- The explicit competing hexagon has actual Lebesgue area `4-d*e`,
which is also its lattice covolume. -/
theorem volume_cutHex {d e : ℝ} (hd : 0 < d) (he : 0 < e)
    (hd1 : d ≤ 1) (he1 : e ≤ 1) :
    (volume (cutHex d e hd he hd1 he1).set).toReal = 4-d*e := by
  let H := cutHex d e hd he hd1 he1
  let C := cornerTriangle d e
  have hC : IsCompact C := (isCompact_Tri _ _).vadd _
  have hN : IsCompact ((-1:ℝ) • C) := hC.smul _
  have hnull : volume (H.set ∩ C) = 0 := cutHex_inter_cornerTriangle_null hd he hd1 he1
  have hnull' : volume (H.set ∩ ((-1:ℝ) • C)) = 0 := by
    have hi : H.set ∩ ((-1:ℝ) • C) ⊆ (-1:ℝ) • (H.set ∩ C) := by
      rintro x ⟨hx,hn⟩
      obtain ⟨y,hy,hyx⟩ := Set.mem_smul_set.1 hn
      refine Set.mem_smul_set.2 ⟨y,⟨?_,hy⟩,hyx⟩
      have hn := cutHex_neg hd he hd1 he1 hx
      simpa [← hyx] using hn
    apply measure_mono_null hi
    rw [Measure.addHaar_smul, hnull, mul_zero]
  have hu0 : volume (H.set ∩ (C ∪ ((-1:ℝ) • C))) = 0 := by
    rw [inter_union_distrib_left, measure_union_null hnull hnull']
  have hu := measure_union_add_inter (μ := volume) H.set (hC.measurableSet.union hN.measurableSet)
  rw [← square_eq_cutHex_union hd he hd1 he1, volume_square, hu0, add_zero,
    measure_union (cornerTriangle_disjoint_neg hd he he1) hN.measurableSet,
    Measure.addHaar_smul, finrank_euclideanSpace_fin, volume_cornerTriangle hd he] at hu
  have hHfin : volume H.set ≠ ⊤ := (measure_mono
    (show H.set ⊆ square from fun x hx => ((mem_cutHex_iff hd he hd1 he1 x).1 hx).1)).trans_lt
      isCompact_square.measure_lt_top |>.ne
  have hCfin : volume C ≠ ⊤ := hC.measure_lt_top.ne
  have hNfin : volume ((-1:ℝ) • C) ≠ ⊤ := hN.measure_lt_top.ne
  have ht := congrArg ENNReal.toReal hu
  norm_num [ENNReal.toReal_add, hHfin, hCfin, hNfin, ENNReal.toReal_ofReal (show 0 ≤ d*e/2 by positivity)] at ht
  change (volume H.set).toReal = _
  nlinarith

end Certificate.Packing
