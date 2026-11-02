import Certificate.MinimizerSupportFaceContact
import Mathlib.Analysis.LocallyConvex.Separation

/-! Critical contacts determine every support value and hence the entire
minimizing body as a closed convex hull. This does not identify the contact
locus itself with the boundary. -/
namespace Certificate.Packing
open Set MeasureTheory
set_option maxHeartbeats 0

/-- Every nonzero linear functional attains its maximum over the minimizer
at a contact with an enclosing critical hexagon. -/
theorem minimizer_support_maximum_at_critical_contact (ψ : E →ₗ[ℝ] ℝ) (hne : ψ ≠ 0) :
    ∃ x ∈ criticalContactSet ratioMinimizingBody,
      ∀ y ∈ ratioMinimizingBody, ψ y ≤ ψ x := by
  have hK := ratioMinimizingBody_properties.1
  obtain ⟨u,hu,humax⟩ := hK.2.1.exists_isMaxOn (hK.2.2.1.mono interior_subset)
    ψ.continuous_of_finiteDimensional.continuousOn
  have hpos := support_level_pos (symmetricConvexDisc_zero_interior hK) u ψ hne
    (fun y hy => humax hy)
  have hnorm : NormalizedSupportAt ratioMinimizingBody u ((1/ψ u) • ψ) := by
    refine ⟨?_,?_⟩
    · simp [hpos.ne']
    · intro y hy
      change (1/ψ u)*ψ y ≤ 1
      rw [one_div_mul_eq_div,div_le_one hpos]
      exact humax hy
  obtain ⟨x,hx,hval⟩ := minimizer_support_face_contact hu hnorm
  have hvalue : ψ x=ψ u := by
    change (1/ψ u)*ψ x=1 at hval
    rw [one_div_mul_eq_div,div_eq_one_iff_eq hpos.ne'] at hval
    exact hval
  refine ⟨x,hx,?_⟩
  intro y hy
  rw [hvalue]
  exact humax hy

lemma minimizer_criticalContactSet_nonempty : (criticalContactSet ratioMinimizingBody).Nonempty := by
  have hne : coord 0 ≠ 0 := by
    intro he
    have hh := LinearMap.congr_fun he (point 1 0)
    norm_num [coord_eval,point] at hh
  obtain ⟨x,hx,_⟩ := minimizer_support_maximum_at_critical_contact (coord 0) hne
  exact ⟨x,hx⟩

/-- The closed convex hull of the contact locus is the minimizing body.
This is weaker than coverage of every boundary point by a critical edge. -/
theorem closure_convexHull_criticalContactSet_eq_minimizer :
    closure (convexHull ℝ (criticalContactSet ratioMinimizingBody))=ratioMinimizingBody := by
  have hK := ratioMinimizingBody_properties.1
  have hsub : criticalContactSet ratioMinimizingBody ⊆ ratioMinimizingBody :=
    (criticalContactSet_subset_frontier hK).trans (frontier_subset_iff_isClosed.2 hK.2.1.isClosed)
  apply subset_antisymm
  · exact closure_minimal (convexHull_min hsub hK.1) hK.2.1.isClosed
  · intro x hx
    by_contra hn
    obtain ⟨f,c,hfc,hcx⟩ := geometric_hahn_banach_closed_point
      (convex_convexHull ℝ (criticalContactSet ratioMinimizingBody)).closure isClosed_closure hn
    have hne : f.toLinearMap ≠ 0 := by
      intro he
      have hz (y : E) : f y=0 := by
        change f.toLinearMap y=0
        rw [he]; rfl
      obtain ⟨y,hy⟩ := minimizer_criticalContactSet_nonempty
      have hh := hfc y (subset_closure (subset_convexHull ℝ _ hy))
      rw [hz] at hh hcx
      linarith
    obtain ⟨y,hy,hmax⟩ := minimizer_support_maximum_at_critical_contact f.toLinearMap hne
    have hh := hfc y (subset_closure (subset_convexHull ℝ _ hy))
    have hm := hmax x hx
    change f x ≤ f y at hm
    linarith

#print axioms minimizer_support_maximum_at_critical_contact
#print axioms closure_convexHull_criticalContactSet_eq_minimizer
end Certificate.Packing
