import Certificate.HVCornerRegions
import Certificate.HVAreaExpression

/-! Lebesgue-area assembly for the six corner contributions in HV 5.0.6.
All nonoverlap claims are discharged using the explicit corner sectors. -/
namespace Certificate.Packing.HVGeometry
open MeasureTheory Set Pointwise
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false

noncomputable def vertex (u v w : ℝ) : Fin 6 → E :=
  ![p0 u v w,p1 u v w,p2 u v w,-p0 u v w,-p1 u v w,-p2 u v w]

lemma vertex_mem_cornerRegion (u v w : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w)
    (he2 : u*v+v*w+w*u=1) (i : Fin 6) : vertex u v w i ∈ cornerRegion i := by
  have hs := Real.sqrt_nonneg (3:ℝ)
  have hsuv := mul_nonneg (mul_nonneg hs hu) hv
  have hsuw := mul_nonneg (mul_nonneg hs hu) hw
  have hsvw := mul_nonneg (mul_nonneg hs hv) hw
  have he : Real.sqrt 3*(u*v+v*w+w*u)=Real.sqrt 3 := by rw [he2]; ring
  fin_cases i <;>
    dsimp [vertex,cornerRegion,leftNormal,rightNormal,baseNormal,baseLevel] <;>
    simp only [rayA,rayB,rayC,LinearMap.neg_apply,LinearMap.add_apply,LinearMap.sub_apply,
      LinearMap.smul_apply,smul_eq_mul,coord_eval] <;>
    dsimp [p0,p1,p2,s0,s1,s2,pt] <;> norm_num <;> (repeat' constructor) <;> nlinarith

lemma corner_triangle_subset_region (u v w : ℝ)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w) (he2 : u*v+v*w+w*u=1) (i : Fin 6) :
    triangle (root i) (vertex u v w i) (root (next i)) ⊆ cornerRegion i :=
  Tri_subset_of_mem _ (convex_cornerRegion i) (roots_mem_cornerRegion i).1
    (vertex_mem_cornerRegion u v w hu hv hw he2 i) (roots_mem_cornerRegion i).2

lemma inscribedHexagon_subset (K : Set E) (hconv : Convex ℝ K)
    (hroot : ∀ i : Fin 6, root i ∈ K) : inscribedHexagon ⊆ K := by
  have hzero : (0:E) ∈ K := by
    have h := hconv (hroot 0) (hroot 3) (by norm_num : (0:ℝ) ≤ 1/2)
      (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
    simpa [root] using h
  apply iUnion_subset
  intro i
  have h := Tri_subset_of_mem K hconv hzero (hroot i) (hroot (next i))
  simpa only [zero_vadd,sub_zero,wedge] using h

/-- The inscribed hexagon and any six compact pieces in their corresponding
corner sectors may be added without double-counting area. -/
theorem corner_pieces_area_lower_bound (K : Set E) (hcomp : IsCompact K)
    (hbase : inscribedHexagon ⊆ K) (S : Fin 6 → Set E)
    (hc : ∀ i, IsCompact (S i)) (hsub : ∀ i, S i ⊆ K)
    (hregion : ∀ i, S i ⊆ cornerRegion i) :
    3*Real.sqrt 3/2 + ∑ i, (volume (S i)).toReal ≤ (volume K).toReal := by
  have hpair : Pairwise (fun i j => AEDisjoint volume (S i) (S j)) := by
    intro i j hij
    exact measure_mono_null (inter_subset_inter (hregion i) (hregion j))
      (cornerRegion_inter_null hij)
  have hunion : volume (⋃ i, S i) = ∑ i, volume (S i) := by
    rw [measure_iUnion₀ hpair (fun i => (hc i).measurableSet.nullMeasurableSet),tsum_fintype]
  have hnull : volume (inscribedHexagon ∩ ⋃ i, S i) = 0 := by
    rw [inter_iUnion]
    apply measure_iUnion_null
    intro i
    rw [inter_comm]
    exact measure_mono_null (inter_subset_inter_left _ (hregion i))
      (inscribedHexagon_cornerRegion_inter_null i)
  have hsum := measure_union_add_inter (μ:=volume) inscribedHexagon
    (MeasurableSet.iUnion (fun i => (hc i).measurableSet))
  rw [hnull,add_zero,hunion,volume_inscribedHexagon] at hsum
  have hle : ENNReal.ofReal (3*Real.sqrt 3/2) + ∑ i, volume (S i) ≤ volume K := by
    rw [← hsum]
    exact measure_mono (union_subset hbase (iUnion_subset hsub))
  have hfin : volume K ≠ ⊤ := hcomp.measure_lt_top.ne
  have hsfin : (∑ i, volume (S i)) ≠ ⊤ :=
    ENNReal.sum_ne_top.2 (fun i _ => (hc i).measure_lt_top.ne)
  have hh := ENNReal.toReal_mono hfin hle
  rw [ENNReal.toReal_add ENNReal.ofReal_ne_top hsfin,
    ENNReal.toReal_ofReal (by positivity),ENNReal.toReal_sum
      (fun i _ => (hc i).measure_lt_top.ne)] at hh
  exact hh

/-- No disjointness premise is needed: membership in the explicit corner
regions suffices and all boundary overlaps were proved null. -/
theorem six_corner_area_lower_bound (K : Set E) (hcomp : IsCompact K) (hconv : Convex ℝ K)
    (hroot : ∀ i : Fin 6, root i ∈ K) (r : Fin 6 → E)
    (hrK : ∀ i, r i ∈ K) (hr : ∀ i, r i ∈ cornerRegion i) :
    3*Real.sqrt 3/2 + ∑ i, triangleArea (root i) (r i) (root (next i)) ≤
      (volume K).toReal := by
  apply corner_pieces_area_lower_bound K hcomp (inscribedHexagon_subset K hconv hroot)
    (fun i => triangle (root i) (r i) (root (next i)))
    (fun i => isCompact_triangle _ _ _)
  · intro i
    exact Tri_subset_of_mem K hconv (hroot i) (hrK i) (hroot (next i))
  · intro i
    exact Tri_subset_of_mem _ (convex_cornerRegion i)
      (roots_mem_cornerRegion i).1 (hr i) (roots_mem_cornerRegion i).2

/-- Geometric version with contact points inside the original three corner
triangles and their negatives, as produced by the minimality argument. -/
theorem six_corner_area_lower_bound_of_triangle_contacts (K : Set E)
    (hcomp : IsCompact K) (hconv : Convex ℝ K) (hroot : ∀ i : Fin 6, root i ∈ K)
    (u v w : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w) (he2 : u*v+v*w+w*u=1)
    (r : Fin 6 → E) (hrK : ∀ i, r i ∈ K)
    (hr : ∀ i, r i ∈ triangle (root i) (vertex u v w i) (root (next i))) :
    3*Real.sqrt 3/2 + ∑ i, triangleArea (root i) (r i) (root (next i)) ≤
      (volume K).toReal :=
  six_corner_area_lower_bound K hcomp hconv hroot r hrK
    (fun i => corner_triangle_subset_region u v w hu hv hw he2 i (hr i))

#print axioms vertex_mem_cornerRegion
#print axioms corner_pieces_area_lower_bound
#print axioms six_corner_area_lower_bound_of_triangle_contacts
end Certificate.Packing.HVGeometry
