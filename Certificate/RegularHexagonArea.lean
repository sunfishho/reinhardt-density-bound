import Certificate.HVTriangleGeometry
import Certificate.CornerCut

/-! The inscribed regular-hexagon area bound used in HV 5.0.6 (and already
in Reinhardt's existence argument). Triangle overlaps are proved null;
no polygon-area formula or disjointness assumption is imported. -/
namespace Certificate.Packing
open MeasureTheory Set Pointwise
set_option maxHeartbeats 0

@[simp] lemma coord_eval (i : Fin 2) (x : E) : coord i x = x i := rfl

lemma Tri_swap (p q : E) : Tri p q = Tri q p := by
  ext x
  constructor <;> rintro ⟨⟨a,b⟩,⟨ha,hb,hab⟩,rfl⟩ <;>
    exact ⟨(b,a),⟨hb,ha,by linarith⟩,by simp [add_comm]⟩

lemma triangles_inter_null_of_separation (φ : E →ₗ[ℝ] ℝ) (p q r s : E)
    (hp : φ p=0) (hq : 0 < φ q) (hr : φ r ≤ 0) (hs : φ s ≤ 0) :
    volume (Tri p q ∩ Tri r s) = 0 := by
  apply measure_mono_null (t := segment ℝ (0:E) p)
  · rintro x ⟨⟨⟨a,b⟩,⟨ha,hb,hab⟩,rfl⟩,hx⟩
    obtain ⟨⟨c,d⟩,⟨hc,hd,hcd⟩,he⟩ := hx
    have hh := congrArg φ he
    simp only [map_add,map_smul,smul_eq_mul,hp,mul_zero,zero_add] at hh
    have hb0 : b=0 := by
      have hle : b*φ q ≤ 0 := by nlinarith [mul_nonpos_of_nonneg_of_nonpos hc hr,
        mul_nonpos_of_nonneg_of_nonpos hd hs]
      nlinarith
    refine ⟨1-a,a,by linarith,ha,by ring,?_⟩
    simp [hb0]
  · exact volume_segment _ _

namespace HVGeometry
noncomputable def root : Fin 6 → E := ![s0,s1,s2,-s0,-s1,-s2]
def next : Fin 6 → Fin 6 := ![1,2,3,4,5,0]
noncomputable def wedge (i : Fin 6) : Set E := Tri (root i) (root (next i))
noncomputable def inscribedHexagon : Set E := ⋃ i, wedge i

lemma wedge_inter_null : Pairwise (fun i j => AEDisjoint volume (wedge i) (wedge j)) := by
  have hs : 0 < Real.sqrt (3:ℝ) := Real.sqrt_pos.2 (by norm_num)
  have h01 : volume (wedge 0 ∩ wedge 1) = 0 := by
    have h := triangles_inter_null_of_separation (Real.sqrt 3 • coord 0 - coord 1) (root 1) (root 0) (root 1) (root 2)
    have hh : volume (Tri (root 1) (root 0) ∩ Tri (root 1) (root 2)) = 0 := by
      apply h <;> simp only [LinearMap.smul_apply,LinearMap.sub_apply,LinearMap.add_apply,LinearMap.neg_apply,smul_eq_mul,coord_eval] <;> dsimp [root,s0,s1,s2,pt] <;> norm_num <;> nlinarith
    simpa only [wedge,show next 0 = 1 from rfl,
      show next 1 = 2 from rfl,Tri_swap (root 0) (root 1)] using hh
  have h02 : volume (wedge 0 ∩ wedge 2) = 0 := by
    have h := triangles_inter_null_of_separation (Real.sqrt 3 • coord 0 - coord 1) (root 1) (root 0) (root 2) (root 3)
    have hh : volume (Tri (root 1) (root 0) ∩ Tri (root 2) (root 3)) = 0 := by
      apply h <;> simp only [LinearMap.smul_apply,LinearMap.sub_apply,LinearMap.add_apply,LinearMap.neg_apply,smul_eq_mul,coord_eval] <;> dsimp [root,s0,s1,s2,pt] <;> norm_num <;> nlinarith
    simpa only [wedge,show next 0 = 1 from rfl,
      show next 2 = 3 from rfl,Tri_swap (root 0) (root 1)] using hh
  have h03 : volume (wedge 0 ∩ wedge 3) = 0 := by
    have h := triangles_inter_null_of_separation (coord 1) (root 0) (root 1) (root 3) (root 4)
    have hh : volume (Tri (root 0) (root 1) ∩ Tri (root 3) (root 4)) = 0 := by
      apply h <;> simp only [LinearMap.smul_apply,LinearMap.sub_apply,LinearMap.add_apply,LinearMap.neg_apply,smul_eq_mul,coord_eval] <;> dsimp [root,s0,s1,s2,pt] <;> norm_num <;> nlinarith
    simpa only [wedge,show next 0 = 1 from rfl,
      show next 3 = 4 from rfl] using hh
  have h04 : volume (wedge 0 ∩ wedge 4) = 0 := by
    have h := triangles_inter_null_of_separation (coord 1) (root 0) (root 1) (root 4) (root 5)
    have hh : volume (Tri (root 0) (root 1) ∩ Tri (root 4) (root 5)) = 0 := by
      apply h <;> simp only [LinearMap.smul_apply,LinearMap.sub_apply,LinearMap.add_apply,LinearMap.neg_apply,smul_eq_mul,coord_eval] <;> dsimp [root,s0,s1,s2,pt] <;> norm_num <;> nlinarith
    simpa only [wedge,show next 0 = 1 from rfl,
      show next 4 = 5 from rfl] using hh
  have h05 : volume (wedge 0 ∩ wedge 5) = 0 := by
    have h := triangles_inter_null_of_separation (coord 1) (root 0) (root 1) (root 5) (root 0)
    have hh : volume (Tri (root 0) (root 1) ∩ Tri (root 5) (root 0)) = 0 := by
      apply h <;> simp only [LinearMap.smul_apply,LinearMap.sub_apply,LinearMap.add_apply,LinearMap.neg_apply,smul_eq_mul,coord_eval] <;> dsimp [root,s0,s1,s2,pt] <;> norm_num <;> nlinarith
    simpa only [wedge,show next 0 = 1 from rfl,
      show next 5 = 0 from rfl] using hh
  have h12 : volume (wedge 1 ∩ wedge 2) = 0 := by
    have h := triangles_inter_null_of_separation (Real.sqrt 3 • coord 0 + coord 1) (root 2) (root 1) (root 2) (root 3)
    have hh : volume (Tri (root 2) (root 1) ∩ Tri (root 2) (root 3)) = 0 := by
      apply h <;> simp only [LinearMap.smul_apply,LinearMap.sub_apply,LinearMap.add_apply,LinearMap.neg_apply,smul_eq_mul,coord_eval] <;> dsimp [root,s0,s1,s2,pt] <;> norm_num <;> nlinarith
    simpa only [wedge,show next 1 = 2 from rfl,
      show next 2 = 3 from rfl,Tri_swap (root 1) (root 2)] using hh
  have h13 : volume (wedge 1 ∩ wedge 3) = 0 := by
    have h := triangles_inter_null_of_separation (Real.sqrt 3 • coord 0 + coord 1) (root 2) (root 1) (root 3) (root 4)
    have hh : volume (Tri (root 2) (root 1) ∩ Tri (root 3) (root 4)) = 0 := by
      apply h <;> simp only [LinearMap.smul_apply,LinearMap.sub_apply,LinearMap.add_apply,LinearMap.neg_apply,smul_eq_mul,coord_eval] <;> dsimp [root,s0,s1,s2,pt] <;> norm_num <;> nlinarith
    simpa only [wedge,show next 1 = 2 from rfl,
      show next 3 = 4 from rfl,Tri_swap (root 1) (root 2)] using hh
  have h14 : volume (wedge 1 ∩ wedge 4) = 0 := by
    have h := triangles_inter_null_of_separation (Real.sqrt 3 • coord 0 + coord 1) (root 2) (root 1) (root 4) (root 5)
    have hh : volume (Tri (root 2) (root 1) ∩ Tri (root 4) (root 5)) = 0 := by
      apply h <;> simp only [LinearMap.smul_apply,LinearMap.sub_apply,LinearMap.add_apply,LinearMap.neg_apply,smul_eq_mul,coord_eval] <;> dsimp [root,s0,s1,s2,pt] <;> norm_num <;> nlinarith
    simpa only [wedge,show next 1 = 2 from rfl,
      show next 4 = 5 from rfl,Tri_swap (root 1) (root 2)] using hh
  have h15 : volume (wedge 1 ∩ wedge 5) = 0 := by
    have h := triangles_inter_null_of_separation (-(Real.sqrt 3 • coord 0 - coord 1)) (root 1) (root 2) (root 5) (root 0)
    have hh : volume (Tri (root 1) (root 2) ∩ Tri (root 5) (root 0)) = 0 := by
      apply h <;> simp only [LinearMap.smul_apply,LinearMap.sub_apply,LinearMap.add_apply,LinearMap.neg_apply,smul_eq_mul,coord_eval] <;> dsimp [root,s0,s1,s2,pt] <;> norm_num <;> nlinarith
    simpa only [wedge,show next 1 = 2 from rfl,
      show next 5 = 0 from rfl] using hh
  have h23 : volume (wedge 2 ∩ wedge 3) = 0 := by
    have h := triangles_inter_null_of_separation (coord 1) (root 3) (root 2) (root 3) (root 4)
    have hh : volume (Tri (root 3) (root 2) ∩ Tri (root 3) (root 4)) = 0 := by
      apply h <;> simp only [LinearMap.smul_apply,LinearMap.sub_apply,LinearMap.add_apply,LinearMap.neg_apply,smul_eq_mul,coord_eval] <;> dsimp [root,s0,s1,s2,pt] <;> norm_num <;> nlinarith
    simpa only [wedge,show next 2 = 3 from rfl,
      show next 3 = 4 from rfl,Tri_swap (root 2) (root 3)] using hh
  have h24 : volume (wedge 2 ∩ wedge 4) = 0 := by
    have h := triangles_inter_null_of_separation (coord 1) (root 3) (root 2) (root 4) (root 5)
    have hh : volume (Tri (root 3) (root 2) ∩ Tri (root 4) (root 5)) = 0 := by
      apply h <;> simp only [LinearMap.smul_apply,LinearMap.sub_apply,LinearMap.add_apply,LinearMap.neg_apply,smul_eq_mul,coord_eval] <;> dsimp [root,s0,s1,s2,pt] <;> norm_num <;> nlinarith
    simpa only [wedge,show next 2 = 3 from rfl,
      show next 4 = 5 from rfl,Tri_swap (root 2) (root 3)] using hh
  have h25 : volume (wedge 2 ∩ wedge 5) = 0 := by
    have h := triangles_inter_null_of_separation (coord 1) (root 3) (root 2) (root 5) (root 0)
    have hh : volume (Tri (root 3) (root 2) ∩ Tri (root 5) (root 0)) = 0 := by
      apply h <;> simp only [LinearMap.smul_apply,LinearMap.sub_apply,LinearMap.add_apply,LinearMap.neg_apply,smul_eq_mul,coord_eval] <;> dsimp [root,s0,s1,s2,pt] <;> norm_num <;> nlinarith
    simpa only [wedge,show next 2 = 3 from rfl,
      show next 5 = 0 from rfl,Tri_swap (root 2) (root 3)] using hh
  have h34 : volume (wedge 3 ∩ wedge 4) = 0 := by
    have h := triangles_inter_null_of_separation (-(Real.sqrt 3 • coord 0 - coord 1)) (root 4) (root 3) (root 4) (root 5)
    have hh : volume (Tri (root 4) (root 3) ∩ Tri (root 4) (root 5)) = 0 := by
      apply h <;> simp only [LinearMap.smul_apply,LinearMap.sub_apply,LinearMap.add_apply,LinearMap.neg_apply,smul_eq_mul,coord_eval] <;> dsimp [root,s0,s1,s2,pt] <;> norm_num <;> nlinarith
    simpa only [wedge,show next 3 = 4 from rfl,
      show next 4 = 5 from rfl,Tri_swap (root 3) (root 4)] using hh
  have h35 : volume (wedge 3 ∩ wedge 5) = 0 := by
    have h := triangles_inter_null_of_separation (-(Real.sqrt 3 • coord 0 - coord 1)) (root 4) (root 3) (root 5) (root 0)
    have hh : volume (Tri (root 4) (root 3) ∩ Tri (root 5) (root 0)) = 0 := by
      apply h <;> simp only [LinearMap.smul_apply,LinearMap.sub_apply,LinearMap.add_apply,LinearMap.neg_apply,smul_eq_mul,coord_eval] <;> dsimp [root,s0,s1,s2,pt] <;> norm_num <;> nlinarith
    simpa only [wedge,show next 3 = 4 from rfl,
      show next 5 = 0 from rfl,Tri_swap (root 3) (root 4)] using hh
  have h45 : volume (wedge 4 ∩ wedge 5) = 0 := by
    have h := triangles_inter_null_of_separation (-(Real.sqrt 3 • coord 0 + coord 1)) (root 5) (root 4) (root 5) (root 0)
    have hh : volume (Tri (root 5) (root 4) ∩ Tri (root 5) (root 0)) = 0 := by
      apply h <;> simp only [LinearMap.smul_apply,LinearMap.sub_apply,LinearMap.add_apply,LinearMap.neg_apply,smul_eq_mul,coord_eval] <;> dsimp [root,s0,s1,s2,pt] <;> norm_num <;> nlinarith
    simpa only [wedge,show next 4 = 5 from rfl,
      show next 5 = 0 from rfl,Tri_swap (root 4) (root 5)] using hh
  intro i j hij
  change volume (wedge i ∩ wedge j) = 0
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

lemma volume_wedge (i : Fin 6) : volume (wedge i) = ENNReal.ofReal (Real.sqrt 3/4) := by
  rw [wedge,volume_Tri]
  have hd : det2 (root i) (root (next i)) = Real.sqrt 3/2 := by
    fin_cases i <;> dsimp [root,next,s0,s1,s2,pt,det2] <;> ring
  rw [hd,abs_of_nonneg (by positivity)]
  congr 1; ring

/-- Exact area of the six triangles filling the regular unit-circumradius hexagon. -/
theorem volume_inscribedHexagon :
    volume inscribedHexagon = ENNReal.ofReal (3*Real.sqrt 3/2) := by
  rw [inscribedHexagon,measure_iUnion₀ wedge_inter_null
    (fun i => (isCompact_Tri (root i) (root (next i))).measurableSet.nullMeasurableSet)]
  simp only [volume_wedge]
  rw [tsum_fintype]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin]
  rw [nsmul_eq_mul]
  norm_num only [Nat.cast_ofNat]
  have he : (6:ENNReal)*ENNReal.ofReal (Real.sqrt 3/4) = ENNReal.ofReal (6*(Real.sqrt 3/4)) := by
    rw [ENNReal.ofReal_mul (by norm_num)]; norm_num
  rw [he]; congr 1; ring

/-- A convex body containing all six side midpoints has the baseline area. -/
theorem baseline_area_lower_bound (K : Set E) (hcomp : IsCompact K) (hconv : Convex ℝ K)
    (hroot : ∀ i : Fin 6, root i ∈ K) : 3*Real.sqrt 3/2 ≤ (volume K).toReal := by
  have hzero : (0:E) ∈ K := by
    have h := hconv (hroot 0) (hroot 3) (by norm_num : (0:ℝ) ≤ 1/2)
      (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
    simpa [root] using h
  have hsub : inscribedHexagon ⊆ K := by
    apply iUnion_subset
    intro i
    have h := Tri_subset_of_mem K hconv hzero (hroot i) (hroot (next i))
    simpa only [zero_vadd,sub_zero,wedge] using h
  have hfin : volume K ≠ ⊤ := hcomp.measure_lt_top.ne
  have hm := ENNReal.toReal_mono hfin (measure_mono hsub)
  rw [volume_inscribedHexagon,ENNReal.toReal_ofReal (by positivity)] at hm
  exact hm

#print axioms volume_inscribedHexagon
#print axioms baseline_area_lower_bound
end HVGeometry
end Certificate.Packing
