import Certificate.CriticalMidpointBoundaryGaps

/-! Boundary sectors in the basis of two consecutive critical midpoints.
The six triangles use elementary linear coordinate inequalities. -/
namespace Certificate.Packing
open Set Filter Topology
set_option maxHeartbeats 0

/-- The six closed triangles between consecutive vertices of an affine
regular hexagon and the sum of each consecutive pair. -/
def InCriticalHexSectors (a b : ℝ) : Prop :=
    (a ≤ 1 ∧ b ≤ 1 ∧ 1 ≤ a+b) ∨
    (-1 ≤ a ∧ 1 ≤ b ∧ a+b ≤ 1) ∨
    (a ≤ -1 ∧ b ≤ 1 ∧ -1 ≤ a+b) ∨
    (-1 ≤ a ∧ -1 ≤ b ∧ a+b ≤ -1) ∨
    (a ≤ 1 ∧ b ≤ -1 ∧ -1 ≤ a+b) ∨
    (1 ≤ a ∧ -1 ≤ b ∧ a+b ≤ 1)

/-- The balance relation and positive determinant force the next two
points into the next two triangles. This is the finite geometric core of
weak monotonicity. -/
theorem critical_hex_sectors_step {a b c d : ℝ}
    (ha : a < 1) (hb : b < 1) (hab : 1 < a+b)
    (hs : InCriticalHexSectors c d)
    (ht : InCriticalHexSectors (c-a) (d-b))
    (hdet : 0 < a*d-b*c) :
    (-1 ≤ c ∧ 1 ≤ d ∧ c+d ≤ 1) ∧
    (c-a ≤ -1 ∧ d-b ≤ 1 ∧ -1 ≤ (c-a)+(d-b)) := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  rcases hs with ⟨hs1,hs2,hs3⟩ | ⟨hs1,hs2,hs3⟩ | ⟨hs1,hs2,hs3⟩ |
    ⟨hs1,hs2,hs3⟩ | ⟨hs1,hs2,hs3⟩ | ⟨hs1,hs2,hs3⟩ <;>
    rcases ht with ⟨ht1,ht2,ht3⟩ | ⟨ht1,ht2,ht3⟩ | ⟨ht1,ht2,ht3⟩ |
      ⟨ht1,ht2,ht3⟩ | ⟨ht1,ht2,ht3⟩ | ⟨ht1,ht2,ht3⟩
  all_goals first | exact ⟨⟨by linarith,by linarith,by linarith⟩,
    ⟨by linarith,by linarith,by linarith⟩⟩ | exfalso; nlinarith

/-- Coordinates of any boundary point in the positive cone of consecutive
critical midpoints lie in the associated closed triangle. -/
theorem minimizer_boundary_cone_triangle (p : criticalMidpointSet) {x : E}
    (hx : x ∈ frontier ratioMinimizingBody) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (he : x = a • p.val + b • (criticalMidpointNext p).val) :
    a ≤ 1 ∧ b ≤ 1 ∧ 1 ≤ a+b := by
  have hK := ratioMinimizingBody_properties.1
  have hxK := frontier_subset_iff_isClosed.2 hK.2.1.isClosed hx
  have hs (q : criticalMidpointSet) :
      NormalizedSupportAt ratioMinimizingBody q.val (minimizerGaugeGradient q.val).toLinearMap := by
    have hh := minimizerGaugeGradient_support (criticalMidpoint_ne_zero q)
    simpa only [minimizerRadialFoot,criticalMidpoint_gauge,inv_one,one_smul] using hh
  have hleft := (hs p).2 x hxK
  have hright := (hs (criticalMidpointNext p)).2 x hxK
  have hp := (hs p).1
  have hq := (hs (criticalMidpointNext p)).1
  change minimizerGaugeGradient p.val p.val = 1 at hp
  change minimizerGaugeGradient (criticalMidpointNext p).val (criticalMidpointNext p).val = 1 at hq
  change minimizerGaugeGradient p.val x ≤ 1 at hleft
  change minimizerGaugeGradient (criticalMidpointNext p).val x ≤ 1 at hright
  rw [he,map_add,map_smul,map_smul,hp] at hleft
  rw [he,map_add,map_smul,map_smul,hq] at hright
  simp only [smul_eq_mul,mul_one] at hleft hright
  have hpos := criticalMidpointNext_forward_transverse p
  have hpos' := criticalMidpointNext_transverse p
  have hsum := gauge_add_le hK.1 (absorbent_nhds_zero (disc_mem_nhds_zero hK))
    (a • p.val) (b • (criticalMidpointNext p).val)
  rw [← he,(gauge_eq_one_iff_mem_frontier hK.1 (disc_mem_nhds_zero hK)).2 hx,
    gauge_smul_of_nonneg ha,gauge_smul_of_nonneg hb,
    criticalMidpoint_gauge,criticalMidpoint_gauge] at hsum
  simp only [smul_eq_mul,mul_one] at hsum
  exact ⟨by nlinarith [mul_nonneg hb hpos.le],
    by nlinarith [mul_nonneg ha hpos'.le],hsum⟩

/-- Away from the two rays, the triangle inequalities are strict. The
base edge is excluded by uniqueness of support and the strict adjacent
support inequality, without a strict-convexity assumption on the body. -/
theorem minimizer_boundary_cone_strict_triangle (p : criticalMidpointSet) {x : E}
    (hx : x ∈ frontier ratioMinimizingBody) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (he : x = a • p.val + b • (criticalMidpointNext p).val) :
    a < 1 ∧ b < 1 ∧ 1 < a+b := by
  have hK := ratioMinimizingBody_properties.1
  have hxK := frontier_subset_iff_isClosed.2 hK.2.1.isClosed hx
  have hs (q : criticalMidpointSet) :
      NormalizedSupportAt ratioMinimizingBody q.val (minimizerGaugeGradient q.val).toLinearMap := by
    have hh := minimizerGaugeGradient_support (criticalMidpoint_ne_zero q)
    simpa only [minimizerRadialFoot,criticalMidpoint_gauge,inv_one,one_smul] using hh
  have hpK := frontier_subset_iff_isClosed.2 hK.2.1.isClosed
    (criticalMidpointSet_subset_frontier p.property)
  have hqK := frontier_subset_iff_isClosed.2 hK.2.1.isClosed
    (criticalMidpointSet_subset_frontier (criticalMidpointNext p).property)
  have hleft := (hs p).2 x hxK
  have hright := (hs (criticalMidpointNext p)).2 x hxK
  change minimizerGaugeGradient p.val x ≤ 1 at hleft
  change minimizerGaugeGradient (criticalMidpointNext p).val x ≤ 1 at hright
  rw [he,map_add,map_smul,map_smul] at hleft hright
  have hp := (hs p).1
  have hq := (hs (criticalMidpointNext p)).1
  change minimizerGaugeGradient p.val p.val = 1 at hp
  change minimizerGaugeGradient (criticalMidpointNext p).val (criticalMidpointNext p).val = 1 at hq
  simp only [smul_eq_mul,hp,hq,mul_one] at hleft hright
  have hpos := criticalMidpointNext_forward_transverse p
  have hpos' := criticalMidpointNext_transverse p
  have hlt := criticalMidpointNext_forward_transverse_lt_one p
  have hsum := (minimizer_boundary_cone_triangle p hx ha.le hb.le he).2.2
  refine ⟨by nlinarith [mul_pos hb hpos],by nlinarith [mul_pos ha hpos'],?_⟩
  apply lt_of_le_of_ne hsum
  intro hsumEq
  obtain ⟨φ,hφ⟩ := exists_normalized_support_at_frontier hK hx
  have hpa := hφ.2 p.val hpK
  have hqa := hφ.2 (criticalMidpointNext p).val hqK
  have hval := hφ.1
  rw [he,map_add,map_smul,map_smul] at hval
  simp only [smul_eq_mul] at hval
  have hpEq : φ p.val = 1 := by
    apply le_antisymm hpa
    by_contra hh
    have hh' : φ p.val < 1 := lt_of_not_ge hh
    nlinarith [mul_pos ha (sub_pos.mpr hh'),mul_nonneg hb.le (sub_nonneg.mpr hqa)]
  have hsame := minimizer_normalized_support_unique hpK ⟨hpEq,hφ.2⟩ (hs p)
  have hv := LinearMap.congr_fun hsame (criticalMidpointNext p).val
  change φ (criticalMidpointNext p).val = minimizerGaugeGradient p.val (criticalMidpointNext p).val at hv
  rw [hpEq,hv] at hval
  nlinarith [mul_pos hb (sub_pos.mpr hlt)]

/-- The six closed triangles cover the whole minimizing boundary, expressed
in the basis of any consecutive pair of critical midpoints. -/
theorem minimizer_boundary_in_critical_hex_sectors (p : criticalMidpointSet) {x : E}
    (hx : x ∈ frontier ratioMinimizingBody) {a b : ℝ}
    (he : x = a • p.val + b • (criticalMidpointNext p).val) : InCriticalHexSectors a b := by
  let q := criticalMidpointNext p
  let r := criticalMidpointNext q
  let s := criticalMidpointNext r
  let t := criticalMidpointNext s
  let u := criticalMidpointNext t
  have hr : r.val = q.val-p.val := criticalMidpointNext_balance p
  have hs : s.val = -p.val := criticalMidpointNext_third p
  have ht : t.val = -q.val := criticalMidpointNext_third q
  have hu : u.val = p.val-q.val := by
    have hh : u.val = -r.val := criticalMidpointNext_third r
    rw [hh,hr]; abel
  have hv : (criticalMidpointNext u).val = p.val :=
    congrArg Subtype.val (criticalMidpointNext_sixth p)
  by_cases ha : 0 ≤ a
  · by_cases hb : 0 ≤ b
    · exact Or.inl (minimizer_boundary_cone_triangle p hx ha hb he)
    · have hb' : b ≤ 0 := (lt_of_not_ge hb).le
      by_cases hab : 0 ≤ a+b
      · have hh := minimizer_boundary_cone_triangle u hx (neg_nonneg.mpr hb') hab (by
          change x = (-b) • u.val + (a+b) • (criticalMidpointNext u).val
          rw [hu,hv,he]; module)
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by linarith [hh.2.2],
          by linarith [hh.1],hh.2.1⟩))))
      · have hh := minimizer_boundary_cone_triangle t hx
          (show 0 ≤ -a-b by linarith) ha (by
            change x = (-a-b) • t.val + a • u.val
            rw [ht,hu,he]; module)
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hh.2.1,
          by linarith [hh.2.2],by linarith [hh.1]⟩))))
  · have ha' : a ≤ 0 := (lt_of_not_ge ha).le
    by_cases hb : 0 ≤ b
    · by_cases hab : 0 ≤ a+b
      · have hh := minimizer_boundary_cone_triangle q hx hab (neg_nonneg.mpr ha') (by
          change x = (a+b) • q.val + (-a) • r.val
          rw [hr,he]; module)
        exact Or.inr (Or.inl ⟨by linarith [hh.2.1],by linarith [hh.2.2],hh.1⟩)
      · have hh := minimizer_boundary_cone_triangle r hx hb
          (show 0 ≤ -a-b by linarith) (by
            change x = b • r.val + (-a-b) • s.val
            rw [hr,hs,he]; module)
        exact Or.inr (Or.inr (Or.inl ⟨by linarith [hh.2.2],hh.1,
          by linarith [hh.2.1]⟩))
    · have hh := minimizer_boundary_cone_triangle s hx (neg_nonneg.mpr ha')
        (show 0 ≤ -b by linarith) (by
          change x = (-a) • s.val + (-b) • t.val
          rw [hs,ht,he]; module)
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by linarith [hh.1],
        by linarith [hh.2.1],by linarith [hh.2.2]⟩)))

#print axioms critical_hex_sectors_step
#print axioms minimizer_boundary_cone_triangle
#print axioms minimizer_boundary_cone_strict_triangle
#print axioms minimizer_boundary_in_critical_hex_sectors
end Certificate.Packing
