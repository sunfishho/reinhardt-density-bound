import Certificate.CriticalMidpointArcGaps

/-! The flat-gap contradiction completes full critical-midpoint coverage of
the minimizing boundary. No coverage hypothesis is supplied. -/
namespace Certificate.Packing
open Set Filter Topology
set_option maxHeartbeats 0

/-- Three oriented side normals determine the first side midpoint of a
strict hexagon, by uniqueness of consecutive supporting-line intersections. -/
theorem Hex.first_midpoint_eq_of_normals (H G : Hex) (hs : H.Strict)
    (h1 : H.φ₁ = G.φ₁) (h2 : H.φ₂ = G.φ₂) (h3 : H.φ₃ = G.φ₃) :
    H.midpoint 0 = G.midpoint 0 := by
  let F := HVGeometry.pairLinear H.φ₁ H.φ₂
  have hF : LinearMap.det F ≠ 0 := by
    intro hz
    have hp : 0 < det2 (F H.a) (F H.b) := by
      have he : det2 (F H.a) (F H.b) = 1-H.φ₂ H.a := by
        simp [F,HVGeometry.pairLinear,det2,point,H.ha₁,H.hb₁,H.hb₂]
      rw [he]
      linarith [(abs_lt.1 hs.1).2]
    rw [det2_linearMap,hz,zero_mul] at hp
    exact lt_irrefl _ hp
  have hb : H.b = G.b := by
    apply (F.equivOfDetNeZero hF).injective
    change point (H.φ₁ H.b) (H.φ₂ H.b) = point (H.φ₁ G.b) (H.φ₂ G.b)
    rw [H.hb₁,H.hb₂,h1,h2,G.hb₁,G.hb₂]
  let J := HVGeometry.pairLinear H.φ₁ H.φ₃
  have hJ : LinearMap.det J ≠ 0 := by
    intro hz
    have hp : 0 < det2 (J H.a) (J H.c) := by
      have he : det2 (J H.a) (J H.c) = 1+H.φ₁ H.c := by
        simp [J,HVGeometry.pairLinear,det2,point,H.ha₁,H.ha₃,H.hc₃]
      rw [he]
      linarith [(abs_lt.1 hs.2.2).1]
    rw [det2_linearMap,hz,zero_mul] at hp
    exact lt_irrefl _ hp
  have ha : H.a = G.a := by
    apply (J.equivOfDetNeZero hJ).injective
    change point (H.φ₁ H.a) (H.φ₃ H.a) = point (H.φ₁ G.a) (H.φ₃ G.a)
    rw [H.ha₁,H.ha₃,h1,h3,G.ha₁,G.ha₃]
  simp [Hex.midpoint,ha,hb]

theorem criticalMidpoint_eq_of_three_normals (a b : criticalMidpointSet)
    (h0 : minimizerGaugeGradient a.val = minimizerGaugeGradient b.val)
    (h1 : minimizerGaugeGradient (criticalMidpointNext a).val =
      minimizerGaugeGradient (criticalMidpointNext b).val)
    (h2 : minimizerGaugeGradient (criticalMidpointNext (criticalMidpointNext a)).val =
      minimizerGaugeGradient (criticalMidpointNext (criticalMidpointNext b)).val) : a = b := by
  obtain ⟨H,hH,heH,hpH,rfl⟩ := exists_positive_criticalHexagonMidpoint a
  obtain ⟨G,hG,heG,hpG,rfl⟩ := exists_positive_criticalHexagonMidpoint b
  simp only [criticalMidpointNext_side H hH heH hpH,criticalMidpointNext_side G hG heG hpG] at h1 h2
  change minimizerGaugeGradient (H.midpoint 0) = minimizerGaugeGradient (G.midpoint 0) at h0
  change minimizerGaugeGradient (H.midpoint 1) = minimizerGaugeGradient (G.midpoint 1) at h1
  change minimizerGaugeGradient (H.midpoint 2) = minimizerGaugeGradient (G.midpoint 2) at h2
  have hf0 := congrArg ContinuousLinearMap.toLinearMap h0
  have hf1 := congrArg ContinuousLinearMap.toLinearMap h1
  have hf2 := congrArg ContinuousLinearMap.toLinearMap h2
  rw [minimizerGaugeGradient_eq_sideNormal H hH heH,minimizerGaugeGradient_eq_sideNormal G hG heG] at hf0 hf1 hf2
  change H.φ₁ = G.φ₁ at hf0
  change H.φ₂ = G.φ₂ at hf1
  change H.φ₃ = G.φ₃ at hf2
  apply Subtype.ext
  exact H.first_midpoint_eq_of_normals G (criticalHexagon_of_minimizer_strict H hH heH) hf0 hf1 hf2

/-- Empty counterclockwise intervals would give identical normals at three
successive pairs, hence identical endpoints, contradicting positive determinant. -/
theorem criticalMidpoint_no_empty_positive_arc (a b : criticalMidpointSet)
    (hd : 0 < det2 a.val b.val) : ¬ CriticalMidpointArcEmpty a b := by
  intro h
  have hd1 := criticalMidpointNext_preserves_det_pos a b hd
  have hd2 := criticalMidpointNext_preserves_det_pos _ _ hd1
  have h1 := criticalMidpointNext_preserves_empty_arc a b h
  have h2 := criticalMidpointNext_preserves_empty_arc _ _ h1
  have he := criticalMidpoint_eq_of_three_normals a b
    (criticalMidpoint_empty_arc_gradient_eq a b hd h)
    (criticalMidpoint_empty_arc_gradient_eq _ _ hd1 h1)
    (criticalMidpoint_empty_arc_gradient_eq _ _ hd2 h2)
  rw [he,det2_self] at hd
  exact lt_irrefl _ hd

theorem criticalMidpoint_flat_gap_impossible (a b : criticalMidpointSet)
    (hne : a.val ≠ b.val)
    (hflat : segment ℝ a.val b.val ⊆ frontier ratioMinimizingBody)
    (hgap : Disjoint (openSegment ℝ a.val b.val) criticalMidpointSet) : False := by
  obtain ⟨ψ,haψ,hbψ⟩ := criticalMidpoint_flat_segment_support a b hflat
  have hdne : det2 a.val b.val ≠ 0 := by
    intro hz
    have hh := criticalMidpoint_support_face_decomposition a haψ hbψ.1
    rw [hz,zero_smul,add_zero] at hh
    exact hne hh.symm
  rcases lt_or_gt_of_ne hdne with hneg | hpos
  · have hd : 0 < det2 b.val a.val := by rw [det2_swap]; linarith
    apply criticalMidpoint_no_empty_positive_arc b a hd
    apply criticalMidpoint_flat_gap_arc_empty b a hd
    · rwa [segment_symm]
    · rwa [openSegment_symm]
  · exact criticalMidpoint_no_empty_positive_arc a b hpos
      (criticalMidpoint_flat_gap_arc_empty a b hpos hflat hgap)

/-- Every point of the minimizing body's boundary is the side midpoint of
an actual critical hexagon. This discharges the remaining coverage assumption. -/
theorem criticalMidpointSet_eq_frontier_minimizer :
    criticalMidpointSet = frontier ratioMinimizingBody := by
  apply subset_antisymm criticalMidpointSet_subset_frontier
  intro x hx
  by_contra hmiss
  obtain ⟨a,ha,b,hb,hne,_,hflat,hgap⟩ := missing_criticalMidpoint_has_flat_gap hx hmiss
  exact criticalMidpoint_flat_gap_impossible ⟨a,ha⟩ ⟨b,hb⟩ hne hflat hgap

/-- Existence and geometric uniqueness now hold at every boundary point. -/
theorem exists_unique_critical_hexagon_at_frontier {p : E}
    (hp : p ∈ frontier ratioMinimizingBody) :
    ∃! S : Set E, ∃ H : Hex, IsCriticalHexagonAt p H ∧ H.set = S := by
  apply exists_unique_critical_hexagon_region
  rwa [criticalMidpointSet_eq_frontier_minimizer]

#print axioms Hex.first_midpoint_eq_of_normals
#print axioms criticalMidpoint_eq_of_three_normals
#print axioms criticalMidpoint_no_empty_positive_arc
#print axioms criticalMidpoint_flat_gap_impossible
#print axioms criticalMidpointSet_eq_frontier_minimizer
#print axioms exists_unique_critical_hexagon_at_frontier
end Certificate.Packing
