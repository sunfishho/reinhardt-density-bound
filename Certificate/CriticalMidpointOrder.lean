import Certificate.CriticalMidpointSectors

/-! Strict ordering of critical configurations between successive reference
midpoints. Membership is expressed by positive planar determinants. -/
namespace Certificate.Packing
open Set Filter Topology
set_option maxHeartbeats 0

lemma det2_two_combinations (p q : E) (a b c d : ℝ) :
    det2 (a • p+b • q) (c • p+d • q) = (a*d-b*c)*det2 p q := by
  simp only [det2,PiLp.add_apply,PiLp.smul_apply,smul_eq_mul]
  ring

lemma criticalMidpointNext_det_pos (p : criticalMidpointSet) :
    0 < det2 p.val (criticalMidpointNext p).val := by
  rw [criticalMidpointNext_fixed_det]
  positivity

/-- The open counterclockwise sector from a midpoint to its successor. -/
def InCriticalMidpointSector (p : criticalMidpointSet) (x : E) : Prop :=
  ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ x = a • p.val+b • (criticalMidpointNext p).val

lemma inCriticalMidpointSector_iff_det_pos (p : criticalMidpointSet) (x : E) :
    InCriticalMidpointSector p x ↔
      0 < det2 p.val x ∧ 0 < det2 x (criticalMidpointNext p).val := by
  have hd := criticalMidpointNext_det_pos p
  constructor
  · rintro ⟨a,b,ha,hb,rfl⟩
    have h1 : det2 p.val (a • p.val+b • (criticalMidpointNext p).val) =
        b*det2 p.val (criticalMidpointNext p).val := by
      simp [det2]; ring
    have h2 : det2 (a • p.val+b • (criticalMidpointNext p).val) (criticalMidpointNext p).val =
        a*det2 p.val (criticalMidpointNext p).val := by
      simp [det2]; ring
    rw [h1,h2]
    exact ⟨mul_pos hb hd,mul_pos ha hd⟩
  · rintro ⟨h1,h2⟩
    let L := pairFrame p.val (criticalMidpointNext p).val hd.ne'
    have hc := pairFrame_coordinates p.val (criticalMidpointNext p).val hd.ne' x
    refine ⟨L.symm x 0,L.symm x 1,?_,?_,?_⟩
    · change 0 < (pairFrame p.val (criticalMidpointNext p).val hd.ne').symm x 0
      rw [hc.1]; exact div_pos h2 hd
    · change 0 < (pairFrame p.val (criticalMidpointNext p).val hd.ne').symm x 1
      rw [hc.2]; exact div_pos h1 hd
    · exact (L.apply_symm_apply x).symm

/-- Strict triangle membership transports to the next reference triangle.
The fixed determinant excludes the endpoints of the weak sector calculation. -/
theorem criticalMidpointNext_triangle_order (p r : criticalMidpointSet) {a b : ℝ}
    (ha : a < 1) (hb : b < 1) (hab : 1 < a+b)
    (he : r.val = a • p.val+b • (criticalMidpointNext p).val) :
    ∃ c d : ℝ, (criticalMidpointNext r).val = c • p.val+d • (criticalMidpointNext p).val ∧
      -1 < c ∧ 1 < d ∧ c+d < 1 := by
  have hd := criticalMidpointNext_det_pos p
  let L := pairFrame p.val (criticalMidpointNext p).val hd.ne'
  let c := L.symm (criticalMidpointNext r).val 0
  let d := L.symm (criticalMidpointNext r).val 1
  have hs : (criticalMidpointNext r).val = c • p.val+d • (criticalMidpointNext p).val :=
    (L.apply_symm_apply _).symm
  have ht : (criticalMidpointNext (criticalMidpointNext r)).val =
      (c-a) • p.val+(d-b) • (criticalMidpointNext p).val := by
    rw [criticalMidpointNext_balance,hs,he]; module
  have hss := minimizer_boundary_in_critical_hex_sectors p
    (criticalMidpointSet_subset_frontier (criticalMidpointNext r).property) hs
  have htt := minimizer_boundary_in_critical_hex_sectors p
    (criticalMidpointSet_subset_frontier (criticalMidpointNext (criticalMidpointNext r)).property) ht
  have hdet : a*d-b*c = 1 := by
    have hh := criticalMidpointNext_fixed_det r
    rw [he,hs,det2_two_combinations,← criticalMidpointNext_fixed_det p] at hh
    apply mul_right_cancel₀ hd.ne'
    simpa only [one_mul] using hh
  have hw := (critical_hex_sectors_step ha hb hab hss htt (by rw [hdet]; norm_num)).1
  have hc : c < 0 := by
    by_contra h
    have hc0 : c = 0 := by linarith [hw.2.1,hw.2.2]
    have hd1 : d = 1 := by linarith [hw.2.1,hw.2.2]
    rw [hc0,hd1] at hdet
    nlinarith
  have hcd : 0 < c+d := by
    by_contra h
    have hc1 : c = -1 := by linarith [hw.1,hw.2.1]
    have hd1 : d = 1 := by linarith [hw.1,hw.2.1]
    rw [hc1,hd1] at hdet
    nlinarith
  have hcone := minimizer_boundary_cone_strict_triangle (criticalMidpointNext p)
    (criticalMidpointSet_subset_frontier (criticalMidpointNext r).property)
    hcd (neg_pos.mpr hc) (by
      change (criticalMidpointNext r).val = (c+d) • (criticalMidpointNext p).val +
        (-c) • (criticalMidpointNext (criticalMidpointNext p)).val
      rw [criticalMidpointNext_balance,hs]; module)
  exact ⟨c,d,hs,by linarith [hcone.2.1],by linarith [hcone.2.2],hcone.1⟩

/-- If one critical midpoint lies strictly between two consecutive reference
midpoints, its successor lies strictly between their successors. -/
theorem criticalMidpointNext_preserves_sector (p r : criticalMidpointSet)
    (h : InCriticalMidpointSector p r.val) :
    InCriticalMidpointSector (criticalMidpointNext p) (criticalMidpointNext r).val := by
  obtain ⟨a,b,ha,hb,he⟩ := h
  have hh := minimizer_boundary_cone_strict_triangle p
    (criticalMidpointSet_subset_frontier r.property) ha hb he
  obtain ⟨c,d,hs,hc,hd,hcd⟩ := criticalMidpointNext_triangle_order p r hh.1 hh.2.1 hh.2.2 he
  have hc0 : c < 0 := by linarith
  have hsum : 0 < c+d := by linarith
  refine ⟨c+d,-c,hsum,neg_pos.mpr hc0,?_⟩
  rw [criticalMidpointNext_balance,hs]; module

/-- All six critical midpoints advance through the corresponding sectors.
The statement for every iterate also includes the sixfold periodic cycle. -/
theorem criticalMidpointNext_iterate_preserves_sector (p r : criticalMidpointSet)
    (h : InCriticalMidpointSector p r.val) (n : ℕ) :
    InCriticalMidpointSector (criticalMidpointNext^[n] p) (criticalMidpointNext^[n] r).val := by
  induction n with
  | zero => exact h
  | succ n ih =>
      simpa only [Function.iterate_succ_apply'] using criticalMidpointNext_preserves_sector _ _ ih

lemma criticalMidpoint_eq_of_pos_smul (p r : criticalMidpointSet) {b : ℝ}
    (hb : 0 < b) (he : r.val = b • p.val) : r = p := by
  have hg := criticalMidpoint_gauge r
  rw [he,gauge_smul_of_nonneg hb.le,criticalMidpoint_gauge] at hg
  have hb1 : b = 1 := by simpa using hg
  apply Subtype.ext
  simpa [hb1] using he

/-- Successor preserves counterclockwise order throughout each open
semicircle, not merely for nearby points or within one reference sector. -/
theorem criticalMidpointNext_preserves_det_pos (p r : criticalMidpointSet)
    (h : 0 < det2 p.val r.val) :
    0 < det2 (criticalMidpointNext p).val (criticalMidpointNext r).val := by
  have hd := criticalMidpointNext_det_pos p
  let q := criticalMidpointNext p
  let t := criticalMidpointNext q
  let u := criticalMidpointNext t
  have ht : t.val = q.val-p.val := criticalMidpointNext_balance p
  have hu : u.val = -p.val := criticalMidpointNext_third p
  have hv : (criticalMidpointNext u).val = -q.val := criticalMidpointNext_third q
  let L := pairFrame p.val q.val hd.ne'
  let a := L.symm r.val 0
  let b := L.symm r.val 1
  have he : r.val = a • p.val+b • q.val := (L.apply_symm_apply _).symm
  have hb : 0 < b := by
    have hh := (pairFrame_coordinates p.val q.val hd.ne' r.val).2
    change 0 < (pairFrame p.val q.val hd.ne').symm r.val 1
    rw [hh]; exact div_pos h hd
  by_cases ha : 0 < a
  · exact ((inCriticalMidpointSector_iff_det_pos q _).1
      (criticalMidpointNext_preserves_sector p r ⟨a,b,ha,hb,he⟩)).1
  by_cases ha0 : a = 0
  · have hrq : r = q := criticalMidpoint_eq_of_pos_smul q r hb (by simpa [ha0] using he)
    rw [hrq]
    exact criticalMidpointNext_det_pos q
  have han : a < 0 := lt_of_le_of_ne (le_of_not_gt ha) ha0
  by_cases hab : 0 < a+b
  · have hsector : InCriticalMidpointSector q r.val := by
      refine ⟨a+b,-a,hab,neg_pos.mpr han,?_⟩
      change r.val = (a+b) • q.val+(-a) • t.val
      rw [ht,he]; module
    obtain ⟨c,d,hc,hd',hs⟩ := criticalMidpointNext_preserves_sector q r hsector
    change (criticalMidpointNext r).val = c • t.val+d • u.val at hs
    change 0 < det2 q.val (criticalMidpointNext r).val
    rw [hs,ht,hu]
    have hid : det2 q.val (c • (q.val-p.val)+d • (-p.val)) = (c+d)*det2 p.val q.val := by
      simp [det2]; ring
    rw [hid]
    exact mul_pos (add_pos hc hd') hd
  by_cases hab0 : a+b = 0
  · have hrt : r = t := criticalMidpoint_eq_of_pos_smul t r hb (by
      rw [ht,he]
      have haEq : a = -b := by linarith
      rw [haEq]; module)
    rw [hrt]
    change 0 < det2 q.val u.val
    rw [hu,det2_neg_right,det2_swap,neg_neg]
    exact hd
  · have habn : a+b < 0 := lt_of_le_of_ne (le_of_not_gt hab) hab0
    have hsector : InCriticalMidpointSector t r.val := by
      refine ⟨b,-a-b,hb,by linarith,?_⟩
      change r.val = b • t.val+(-a-b) • u.val
      rw [ht,hu,he]; module
    obtain ⟨c,d,hc,hd',hs⟩ := criticalMidpointNext_preserves_sector t r hsector
    change (criticalMidpointNext r).val = c • u.val+d • (criticalMidpointNext u).val at hs
    change 0 < det2 q.val (criticalMidpointNext r).val
    rw [hs,hu,hv]
    have hid : det2 q.val (c • (-p.val)+d • (-q.val)) = c*det2 p.val q.val := by
      simp [det2]; ring
    rw [hid]
    exact mul_pos hc hd

/-- Both directions follow because six successors return to the starting
point. This gives a global order comparison on the actual midpoint locus. -/
theorem criticalMidpointNext_det_pos_iff (p r : criticalMidpointSet) :
    0 < det2 (criticalMidpointNext p).val (criticalMidpointNext r).val ↔
      0 < det2 p.val r.val := by
  constructor
  · intro h
    have h1 := criticalMidpointNext_preserves_det_pos _ _ h
    have h2 := criticalMidpointNext_preserves_det_pos _ _ h1
    have h3 := criticalMidpointNext_preserves_det_pos _ _ h2
    have h4 := criticalMidpointNext_preserves_det_pos _ _ h3
    have h5 := criticalMidpointNext_preserves_det_pos _ _ h4
    simpa only [criticalMidpointNext_sixth] using h5
  · exact criticalMidpointNext_preserves_det_pos p r

#print axioms det2_two_combinations
#print axioms criticalMidpointNext_det_pos
#print axioms inCriticalMidpointSector_iff_det_pos
#print axioms criticalMidpointNext_triangle_order
#print axioms criticalMidpointNext_preserves_sector
#print axioms criticalMidpointNext_iterate_preserves_sector
#print axioms criticalMidpoint_eq_of_pos_smul
#print axioms criticalMidpointNext_preserves_det_pos
#print axioms criticalMidpointNext_det_pos_iff
end Certificate.Packing
