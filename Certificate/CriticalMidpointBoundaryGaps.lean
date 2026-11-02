import Certificate.CriticalMidpointSupportFace
import Mathlib.Analysis.Convex.Strict.Extreme

/-! Every extreme boundary point is a critical midpoint. Possible missing
midpoints lie inside straight supporting segments with critical endpoints. -/
namespace Certificate.Packing
open Set Filter Topology
set_option maxHeartbeats 0

lemma minimizer_support_face_subset_frontier {u : E}
    {ψ : E →ₗ[ℝ] ℝ} (hψ : NormalizedSupportAt ratioMinimizingBody u ψ) :
    {x ∈ ratioMinimizingBody | ψ x = 1} ⊆ frontier ratioMinimizingBody := by
  rintro x ⟨hx,hface⟩
  apply (gauge_eq_one_iff_mem_frontier ratioMinimizingBody_properties.1.1
    (disc_mem_nhds_zero ratioMinimizingBody_properties.1)).1
  refine le_antisymm (gauge_le_one_of_mem hx) ?_
  simpa only [hface] using normalized_support_le_gauge hψ x

/-- Every boundary point lies on a straight boundary segment joining two
critical midpoints. This includes singleton segments. -/
theorem minimizer_frontier_critical_segment {x : E}
    (hx : x ∈ frontier ratioMinimizingBody) :
    ∃ a ∈ criticalMidpointSet, ∃ b ∈ criticalMidpointSet,
      x ∈ segment ℝ a b ∧ segment ℝ a b ⊆ frontier ratioMinimizingBody := by
  have hxK := frontier_subset_iff_isClosed.2 ratioMinimizingBody_properties.1.2.1.isClosed hx
  obtain ⟨ψ,hψ⟩ := exists_normalized_support_at_frontier ratioMinimizingBody_properties.1 hx
  obtain ⟨a,ha,b,hb,he⟩ := minimizer_support_face_segment hxK hψ
  exact ⟨a,ha,b,hb,he ▸ ⟨hxK,hψ.1⟩,he ▸ minimizer_support_face_subset_frontier hψ⟩

/-- If a boundary point is not a critical midpoint, it lies strictly between
critical endpoints of a nontrivial flat boundary segment. -/
theorem missing_criticalMidpoint_in_flat_segment {x : E}
    (hx : x ∈ frontier ratioMinimizingBody) (hmiss : x ∉ criticalMidpointSet) :
    ∃ a ∈ criticalMidpointSet, ∃ b ∈ criticalMidpointSet,
      a ≠ b ∧ x ∈ openSegment ℝ a b ∧ segment ℝ a b ⊆ frontier ratioMinimizingBody := by
  obtain ⟨a,ha,b,hb,hseg,hflat⟩ := minimizer_frontier_critical_segment hx
  have hax : a ≠ x := fun he => hmiss (he ▸ ha)
  have hbx : b ≠ x := fun he => hmiss (he ▸ hb)
  have hab : a ≠ b := by
    intro he
    have hh : x = a := by simpa [← he] using hseg
    exact hmiss (hh ▸ ha)
  exact ⟨a,ha,b,hb,hab,mem_openSegment_of_ne_left_right hax hbx hseg,hflat⟩

/-- All extreme points of the actual minimizing body belong to the compact
critical-midpoint locus. No strict convexity hypothesis is used. -/
theorem minimizer_extremePoints_subset_criticalMidpointSet :
    ratioMinimizingBody.extremePoints ℝ ⊆ criticalMidpointSet := by
  intro x hx
  have hfront : x ∈ frontier ratioMinimizingBody :=
    ⟨subset_closure hx.1,fun hi => Set.disjoint_left.1
      (disjoint_interior_extremePoints ratioMinimizingBody) hi hx⟩
  by_contra hmiss
  obtain ⟨a,ha,b,hb,_,hseg,_⟩ := missing_criticalMidpoint_in_flat_segment hfront hmiss
  have haK := frontier_subset_iff_isClosed.2 ratioMinimizingBody_properties.1.2.1.isClosed
    (criticalMidpointSet_subset_frontier ha)
  have hbK := frontier_subset_iff_isClosed.2 ratioMinimizingBody_properties.1.2.1.isClosed
    (criticalMidpointSet_subset_frontier hb)
  exact hmiss (hx.2 haK hbK hseg ▸ ha)

lemma minimizer_frontier_subset_convexHull_criticalMidpointSet :
    frontier ratioMinimizingBody ⊆ convexHull ℝ criticalMidpointSet := by
  intro x hx
  obtain ⟨a,ha,b,hb,hseg,_⟩ := minimizer_frontier_critical_segment hx
  exact (convex_convexHull ℝ criticalMidpointSet).segment_subset
    (subset_convexHull ℝ _ ha) (subset_convexHull ℝ _ hb) hseg

/-- The ordinary convex hull, without taking closure, reconstructs the whole
minimizing body from its critical midpoints. -/
theorem convexHull_criticalMidpointSet_eq_minimizer :
    convexHull ℝ criticalMidpointSet = ratioMinimizingBody := by
  have hK := ratioMinimizingBody_properties.1
  have hsub : criticalMidpointSet ⊆ ratioMinimizingBody :=
    criticalMidpointSet_subset_frontier.trans (frontier_subset_iff_isClosed.2 hK.2.1.isClosed)
  apply subset_antisymm (convexHull_min hsub hK.1)
  have hc := convex_convexHull ℝ criticalMidpointSet
  have hz : (0 : E) ∈ convexHull ℝ criticalMidpointSet := by
    obtain ⟨p,hp⟩ := criticalMidpointSet_nonempty
    let q : criticalMidpointSet := ⟨p,hp⟩
    have hn : -p ∈ criticalMidpointSet := by
      have hh := (criticalMidpointNext (criticalMidpointNext (criticalMidpointNext q))).property
      rwa [criticalMidpointNext_third] at hh
    have hh := hc (subset_convexHull ℝ _ hp) (subset_convexHull ℝ _ hn)
      (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ)+1/2=1)
    simpa using hh
  intro x hx
  by_cases hzero : x = 0
  · simpa [hzero] using hz
  have hpos := disc_gauge_pos hK hzero
  have hf := minimizer_frontier_subset_convexHull_criticalMidpointSet
    (minimizerRadialFoot_frontier hzero)
  have hh := hc.smul_mem_of_zero_mem hz hf ⟨hpos.le,gauge_le_one_of_mem hx⟩
  simpa only [minimizerRadialFoot,smul_smul,mul_inv_cancel₀ hpos.ne',one_smul] using hh

/-- A missing boundary point lies in a genuine gap: the endpoints are
critical midpoints, the whole segment is on the boundary, and its open part
contains no critical midpoint. This does not yet rule such gaps out. -/
theorem missing_criticalMidpoint_has_flat_gap {x : E}
    (hx : x ∈ frontier ratioMinimizingBody) (hmiss : x ∉ criticalMidpointSet) :
    ∃ a ∈ criticalMidpointSet, ∃ b ∈ criticalMidpointSet,
      a ≠ b ∧ x ∈ openSegment ℝ a b ∧
      segment ℝ a b ⊆ frontier ratioMinimizingBody ∧
      Disjoint (openSegment ℝ a b) criticalMidpointSet := by
  have hK := ratioMinimizingBody_properties.1
  have hxK := frontier_subset_iff_isClosed.2 hK.2.1.isClosed hx
  obtain ⟨ψ,hψ⟩ := exists_normalized_support_at_frontier hK hx
  obtain ⟨H,hH,harea,i,hi⟩ := minimizer_support_face_midpoint hxK hψ
  let p : criticalMidpointSet := ⟨H.midpoint i,critical_hexagon_midpoint_mem_set H hH harea i⟩
  have hpψ : NormalizedSupportAt ratioMinimizingBody p.val ψ := ⟨hi,hψ.2⟩
  let χ := detForm p.val
  have hdec (y : E) (hy : ψ y = 1) : y = p.val + χ y • criticalMidpointTangent p :=
    criticalMidpoint_support_face_decomposition p hpψ hy
  have hinj {y z : E} (hy : ψ y = 1) (hz : ψ z = 1) (he : χ y = χ z) : y = z := by
    calc
      y = p.val + χ y • criticalMidpointTangent p := hdec y hy
      _ = p.val + χ z • criticalMidpointTangent p := by rw [he]
      _ = z := (hdec z hz).symm
  let L : Set E := {y ∈ criticalMidpointSet | ψ y = 1 ∧ χ y ≤ χ x}
  let R : Set E := {y ∈ criticalMidpointSet | ψ y = 1 ∧ χ x ≤ χ y}
  have hLc : IsCompact L := isCompact_criticalMidpointSet.inter_right
    ((isClosed_eq ψ.continuous_of_finiteDimensional continuous_const).inter
      (isClosed_le χ.continuous_of_finiteDimensional continuous_const))
  have hRc : IsCompact R := isCompact_criticalMidpointSet.inter_right
    ((isClosed_eq ψ.continuous_of_finiteDimensional continuous_const).inter
      (isClosed_le continuous_const χ.continuous_of_finiteDimensional))
  have hLn : L.Nonempty := by
    obtain ⟨a,ha,haψ,hmin⟩ := criticalMidpoint_support_face_max hxK hψ (-χ)
    refine ⟨a,ha,haψ,?_⟩
    simpa using hmin x hxK hψ.1
  have hRn : R.Nonempty := by
    obtain ⟨b,hb,hbψ,hmax⟩ := criticalMidpoint_support_face_max hxK hψ χ
    exact ⟨b,hb,hbψ,hmax x hxK hψ.1⟩
  obtain ⟨a,ha,hamax⟩ := hLc.exists_isMaxOn hLn χ.continuous_of_finiteDimensional.continuousOn
  obtain ⟨b,hb,hbmin⟩ := hRc.exists_isMinOn hRn χ.continuous_of_finiteDimensional.continuousOn
  have hax : χ a < χ x := lt_of_le_of_ne ha.2.2 (fun he => hmiss (hinj ha.2.1 hψ.1 he ▸ ha.1))
  have hxb : χ x < χ b := lt_of_le_of_ne hb.2.2 (fun he => hmiss (hinj hb.2.1 hψ.1 he.symm ▸ hb.1))
  have hab : a ≠ b := by intro he; rw [he] at hax; linarith
  have haK := frontier_subset_iff_isClosed.2 hK.2.1.isClosed (criticalMidpointSet_subset_frontier ha.1)
  have hbK := frontier_subset_iff_isClosed.2 hK.2.1.isClosed (criticalMidpointSet_subset_frontier hb.1)
  have hface : segment ℝ a b ⊆ {y ∈ ratioMinimizingBody | ψ y = 1} := by
    intro y hy
    refine ⟨hK.1.segment_subset haK hbK hy,?_⟩
    obtain ⟨s,t,hs,ht,hst,rfl⟩ := hy
    simpa [map_add,map_smul,ha.2.1,hb.2.1] using hst
  refine ⟨a,ha.1,b,hb.1,hab,?_,hface.trans (minimizer_support_face_subset_frontier hψ),?_⟩
  · have hscalar : χ x ∈ openSegment ℝ (χ a) (χ b) := Ioo_subset_openSegment ⟨hax,hxb⟩
    obtain ⟨s,t,hs,ht,hst,he⟩ := hscalar
    change s * χ a + t * χ b = χ x at he
    refine ⟨s,t,hs,ht,hst,?_⟩
    calc
      s • a + t • b = (s+t) • p.val + (s*χ a+t*χ b) • criticalMidpointTangent p := by
        conv_lhs => rw [hdec a ha.2.1,hdec b hb.2.1]
        module
      _ = x := by rw [hst,he,one_smul,← hdec x hψ.1]
  · apply Set.disjoint_left.2
    intro y hy hym
    have hyψ := (hface (openSegment_subset_segment ℝ a b hy)).2
    obtain ⟨s,t,hs,ht,hst,he⟩ := hy
    have hχ := congrArg χ he
    simp only [map_add,map_smul,smul_eq_mul] at hχ
    have hscalar : χ y ∈ openSegment ℝ (χ a) (χ b) := ⟨s,t,hs,ht,hst,hχ⟩
    have hbds := openSegment_subset_Ioo (hax.trans hxb) hscalar
    have hay := hbds.1
    have hyb := hbds.2
    by_cases hleft : χ y ≤ χ x
    · have hh := hamax (show y ∈ L from ⟨hym,hyψ,hleft⟩)
      exact (not_le_of_gt hay) hh
    · have hh := hbmin (show y ∈ R from ⟨hym,hyψ,(lt_of_not_ge hleft).le⟩)
      exact (not_le_of_gt hyb) hh

#print axioms minimizer_support_face_subset_frontier
#print axioms minimizer_frontier_critical_segment
#print axioms missing_criticalMidpoint_in_flat_segment
#print axioms minimizer_extremePoints_subset_criticalMidpointSet
#print axioms minimizer_frontier_subset_convexHull_criticalMidpointSet
#print axioms convexHull_criticalMidpointSet_eq_minimizer
#print axioms missing_criticalMidpoint_has_flat_gap
end Certificate.Packing
