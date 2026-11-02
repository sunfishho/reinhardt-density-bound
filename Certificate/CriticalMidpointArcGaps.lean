import Certificate.CriticalMidpointOrder

/-! Empty angular arcs in the compact midpoint locus determine flat support
faces. Global order transports such empty arcs through the successor map. -/
namespace Certificate.Packing
open Set Filter Topology
set_option maxHeartbeats 0

lemma criticalMidpoint_gradient_support (p : criticalMidpointSet) :
    NormalizedSupportAt ratioMinimizingBody p.val (minimizerGaugeGradient p.val).toLinearMap := by
  have h := minimizerGaugeGradient_support (criticalMidpoint_ne_zero p)
  simpa only [minimizerRadialFoot,criticalMidpoint_gauge,inv_one,one_smul] using h

lemma criticalMidpoint_mem_body (p : criticalMidpointSet) : p.val ∈ ratioMinimizingBody :=
  frontier_subset_iff_isClosed.2 ratioMinimizingBody_properties.1.2.1.isClosed
    (criticalMidpointSet_subset_frontier p.property)

/-- A flat boundary segment has one normalized support form at both ends. -/
theorem criticalMidpoint_flat_segment_support (a b : criticalMidpointSet)
    (hflat : segment ℝ a.val b.val ⊆ frontier ratioMinimizingBody) :
    ∃ ψ : E →ₗ[ℝ] ℝ, NormalizedSupportAt ratioMinimizingBody a.val ψ ∧
      NormalizedSupportAt ratioMinimizingBody b.val ψ := by
  have hm := hflat (show (1/2:ℝ) • a.val+(1/2:ℝ) • b.val ∈ segment ℝ a.val b.val from
    ⟨1/2,1/2,by norm_num,by norm_num,by norm_num,rfl⟩)
  obtain ⟨ψ,hψ⟩ := exists_normalized_support_at_frontier ratioMinimizingBody_properties.1 hm
  have ha := hψ.2 a.val (criticalMidpoint_mem_body a)
  have hb := hψ.2 b.val (criticalMidpoint_mem_body b)
  have he := hψ.1
  simp only [map_add,map_smul,smul_eq_mul] at he
  exact ⟨ψ,⟨by linarith,hψ.2⟩,⟨by linarith,hψ.2⟩⟩

/-- Between points on the same supporting face, angular betweenness on the
boundary is ordinary open-segment membership. -/
theorem minimizer_boundary_angular_mem_openSegment (a b : criticalMidpointSet)
    (hd : 0 < det2 a.val b.val) {ψ : E →ₗ[ℝ] ℝ}
    (haψ : NormalizedSupportAt ratioMinimizingBody a.val ψ)
    (hbψ : NormalizedSupportAt ratioMinimizingBody b.val ψ)
    {x : E} (hx : x ∈ frontier ratioMinimizingBody)
    (hax : 0 < det2 a.val x) (hxb : 0 < det2 x b.val) :
    x ∈ openSegment ℝ a.val b.val := by
  let L := pairFrame a.val b.val hd.ne'
  let c := L.symm x 0
  let d := L.symm x 1
  have hcoords := pairFrame_coordinates a.val b.val hd.ne' x
  have hc : 0 < c := by change 0 < (pairFrame a.val b.val hd.ne').symm x 0; rw [hcoords.1]; exact div_pos hxb hd
  have hd' : 0 < d := by change 0 < (pairFrame a.val b.val hd.ne').symm x 1; rw [hcoords.2]; exact div_pos hax hd
  have he : x = c • a.val+d • b.val := (L.apply_symm_apply x).symm
  have hK := ratioMinimizingBody_properties.1
  have hxK := frontier_subset_iff_isClosed.2 hK.2.1.isClosed hx
  have hs := haψ.2 x hxK
  rw [he,map_add,map_smul,map_smul,haψ.1,hbψ.1] at hs
  simp only [smul_eq_mul,mul_one] at hs
  have hg := gauge_add_le hK.1 (absorbent_nhds_zero (disc_mem_nhds_zero hK))
    (c • a.val) (d • b.val)
  rw [← he,(gauge_eq_one_iff_mem_frontier hK.1 (disc_mem_nhds_zero hK)).2 hx,
    gauge_smul_of_nonneg hc.le,gauge_smul_of_nonneg hd'.le,
    criticalMidpoint_gauge,criticalMidpoint_gauge] at hg
  simp only [smul_eq_mul,mul_one] at hg
  exact ⟨c,d,hc,hd',le_antisymm hs hg,he.symm⟩

def CriticalMidpointArcEmpty (a b : criticalMidpointSet) : Prop :=
  ∀ r : criticalMidpointSet, ¬ (0 < det2 a.val r.val ∧ 0 < det2 r.val b.val)

theorem criticalMidpoint_flat_gap_arc_empty (a b : criticalMidpointSet)
    (hd : 0 < det2 a.val b.val)
    (hflat : segment ℝ a.val b.val ⊆ frontier ratioMinimizingBody)
    (hgap : Disjoint (openSegment ℝ a.val b.val) criticalMidpointSet) :
    CriticalMidpointArcEmpty a b := by
  obtain ⟨ψ,haψ,hbψ⟩ := criticalMidpoint_flat_segment_support a b hflat
  intro r hr
  exact Set.disjoint_left.1 hgap
    (minimizer_boundary_angular_mem_openSegment a b hd haψ hbψ
      (criticalMidpointSet_subset_frontier r.property) hr.1 hr.2) r.property

/-- An empty angular interval must be a supporting face. The convex-hull
reconstruction of the body extends a bound on all critical midpoints to K. -/
theorem criticalMidpoint_empty_arc_support (a b : criticalMidpointSet)
    (hd : 0 < det2 a.val b.val) (hempty : CriticalMidpointArcEmpty a b) :
    ∃ ψ : E →ₗ[ℝ] ℝ, NormalizedSupportAt ratioMinimizingBody a.val ψ ∧
      NormalizedSupportAt ratioMinimizingBody b.val ψ := by
  let L := pairFrame a.val b.val hd.ne'
  let ψ : E →ₗ[ℝ] ℝ := (coord 0+coord 1).comp L.symm.toLinearMap
  have hA : L (point 1 0) = a.val := by simp [L,point]
  have hB : L (point 0 1) = b.val := by simp [L,point]
  have hA' : L.symm a.val = point 1 0 := by rw [← hA,L.symm_apply_apply]
  have hB' : L.symm b.val = point 0 1 := by rw [← hB,L.symm_apply_apply]
  have hψa : ψ a.val = 1 := by simp [ψ,hA',coord_eval,point]
  have hψb : ψ b.val = 1 := by simp [ψ,hB',coord_eval,point]
  have hbound : criticalMidpointSet ⊆ {x : E | ψ x ≤ 1} := by
    intro x hx
    let c := L.symm x 0
    let d := L.symm x 1
    have he : x = c • a.val+d • b.val := (L.apply_symm_apply x).symm
    have hψx : ψ x = c+d := by rw [he,map_add,map_smul,map_smul,hψa,hψb]; simp
    change ψ x ≤ 1
    rw [hψx]
    have hxK := criticalMidpoint_mem_body ⟨x,hx⟩
    by_cases hc : 0 < c
    · by_cases hd' : 0 < d
      · exfalso
        apply hempty ⟨x,hx⟩
        have hax : det2 a.val x = d*det2 a.val b.val := by rw [he]; simp [det2]; ring
        have hxb : det2 x b.val = c*det2 a.val b.val := by rw [he]; simp [det2]; ring
        exact ⟨by change 0 < det2 a.val x; rw [hax]; exact mul_pos hd' hd,
          by change 0 < det2 x b.val; rw [hxb]; exact mul_pos hc hd⟩
      · have hdn : d ≤ 0 := le_of_not_gt hd'
        let φ := (minimizerGaugeGradient a.val).toLinearMap
        have hφ := criticalMidpoint_gradient_support a
        have hs : φ x ≤ 1 := hφ.2 x hxK
        have haφ : φ a.val = 1 := hφ.1
        have hbφ : φ b.val ≤ 1 := hφ.2 b.val (criticalMidpoint_mem_body b)
        rw [he,map_add,map_smul,map_smul,haφ] at hs
        simp only [smul_eq_mul,mul_one] at hs
        nlinarith [mul_nonneg (neg_nonneg.mpr hdn) (sub_nonneg.mpr hbφ)]
    · have hcn : c ≤ 0 := le_of_not_gt hc
      let φ := (minimizerGaugeGradient b.val).toLinearMap
      have hφ := criticalMidpoint_gradient_support b
      have hs : φ x ≤ 1 := hφ.2 x hxK
      have hbφ : φ b.val = 1 := hφ.1
      have haφ : φ a.val ≤ 1 := hφ.2 a.val (criticalMidpoint_mem_body a)
      rw [he,map_add,map_smul,map_smul,hbφ] at hs
      simp only [smul_eq_mul,mul_one] at hs
      nlinarith [mul_nonneg (neg_nonneg.mpr hcn) (sub_nonneg.mpr haφ)]
  have hhalf : Convex ℝ {x : E | ψ x ≤ 1} := (convex_Iic (1:ℝ)).linear_preimage ψ
  have hK : ratioMinimizingBody ⊆ {x : E | ψ x ≤ 1} := by
    rw [← convexHull_criticalMidpointSet_eq_minimizer]
    exact convexHull_min hbound hhalf
  exact ⟨ψ,⟨hψa,fun x hx => hK hx⟩,⟨hψb,fun x hx => hK hx⟩⟩

/-- Empty midpoint intervals propagate to their successor intervals. -/
theorem criticalMidpointNext_preserves_empty_arc (a b : criticalMidpointSet)
    (h : CriticalMidpointArcEmpty a b) :
    CriticalMidpointArcEmpty (criticalMidpointNext a) (criticalMidpointNext b) := by
  intro s hs
  obtain ⟨r,hr⟩ := criticalMidpointHomeomorph.surjective s
  change criticalMidpointNext r = s at hr
  subst s
  exact h r ⟨(criticalMidpointNext_det_pos_iff a r).1 hs.1,
    (criticalMidpointNext_det_pos_iff r b).1 hs.2⟩

/-- The two endpoints of an empty interval have the same normalized normal. -/
theorem criticalMidpoint_empty_arc_gradient_eq (a b : criticalMidpointSet)
    (hd : 0 < det2 a.val b.val) (h : CriticalMidpointArcEmpty a b) :
    minimizerGaugeGradient a.val = minimizerGaugeGradient b.val := by
  obtain ⟨ψ,haψ,hbψ⟩ := criticalMidpoint_empty_arc_support a b hd h
  have ha := minimizer_normalized_support_unique (criticalMidpoint_mem_body a)
    (criticalMidpoint_gradient_support a) haψ
  have hb := minimizer_normalized_support_unique (criticalMidpoint_mem_body b)
    hbψ (criticalMidpoint_gradient_support b)
  ext x
  exact LinearMap.congr_fun (ha.trans hb) x

#print axioms criticalMidpoint_flat_segment_support
#print axioms minimizer_boundary_angular_mem_openSegment
#print axioms criticalMidpoint_flat_gap_arc_empty
#print axioms criticalMidpoint_empty_arc_support
#print axioms criticalMidpointNext_preserves_empty_arc
#print axioms criticalMidpoint_empty_arc_gradient_eq
end Certificate.Packing
