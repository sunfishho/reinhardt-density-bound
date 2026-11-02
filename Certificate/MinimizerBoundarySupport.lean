import Certificate.MinimizerSupportFaceMidpoint
import Mathlib.Analysis.LocallyConvex.Separation

/-! Every boundary point of the minimizer lies on an edge of a critical
hexagon and has a unique supporting line. This does not yet make every
boundary point a critical side midpoint or construct the balanced frame. -/
namespace Certificate.Packing
open Set MeasureTheory HexParameters
set_option maxHeartbeats 0

lemma exists_normalized_support_at_frontier {K : Set E} (hK : IsSymmetricConvexDisc K)
    {u : E} (hu : u ∈ frontier K) : ∃ ψ : E →ₗ[ℝ] ℝ, NormalizedSupportAt K u ψ := by
  obtain ⟨f,hf,hs⟩ := geometric_hahn_banach_of_nonempty_interior_point hK.1 hu.2 hK.2.2.1
  have hne : f.toLinearMap ≠ 0 := by
    intro he
    apply hf
    ext x
    exact LinearMap.congr_fun he x
  have hp : (0:ℝ) < f u := support_level_pos (symmetricConvexDisc_zero_interior hK) u f.toLinearMap hne hs
  refine ⟨(1/f u) • f.toLinearMap,?_,?_⟩
  · simp [hp.ne']
  · intro x hx
    change (1/f u)*f x ≤ 1
    rw [one_div_mul_eq_div,div_le_one hp]
    exact hs x hx

/-- Averaging two support forms puts both on the same face. The critical
midpoint in that face has a unique support form, forcing the two to agree. -/
theorem minimizer_normalized_support_unique {u : E} (hu : u ∈ ratioMinimizingBody)
    {φ ψ : E →ₗ[ℝ] ℝ} (hφ : NormalizedSupportAt ratioMinimizingBody u φ)
    (hψ : NormalizedSupportAt ratioMinimizingBody u ψ) : φ=ψ := by
  let χ : E →ₗ[ℝ] ℝ := (1/2:ℝ) • (φ+ψ)
  have hχ : NormalizedSupportAt ratioMinimizingBody u χ := by
    constructor
    · norm_num [χ,hφ.1,hψ.1]
    · intro x hx
      change (1/2:ℝ)*(φ x+ψ x) ≤ 1
      linarith [hφ.2 x hx,hψ.2 x hx]
  obtain ⟨H,hH,ha,i,hi⟩ := minimizer_support_face_midpoint hu hχ
  have hmK := frontier_subset_iff_isClosed.2 ratioMinimizingBody_properties.1.2.1.isClosed
    (criticalHexagon_of_minimizer_midpoint_frontier H hH ha i)
  change (1/2:ℝ)*(φ (H.midpoint i)+ψ (H.midpoint i))=1 at hi
  have hmφ : φ (H.midpoint i)=1 := by linarith [hφ.2 _ hmK,hψ.2 _ hmK]
  have hmψ : ψ (H.midpoint i)=1 := by linarith [hφ.2 _ hmK,hψ.2 _ hmK]
  exact (criticalHexagon_of_minimizer_unique_support H hH ha i).unique
    ⟨hmφ,hφ.2⟩ ⟨hmψ,hψ.2⟩

theorem minimizer_frontier_unique_normalized_support {u : E} (hu : u ∈ frontier ratioMinimizingBody) :
    ∃! ψ : E →ₗ[ℝ] ℝ, NormalizedSupportAt ratioMinimizingBody u ψ := by
  obtain ⟨ψ,hψ⟩ := exists_normalized_support_at_frontier ratioMinimizingBody_properties.1 hu
  refine ⟨ψ,hψ,fun φ hφ => minimizer_normalized_support_unique ?_ hφ hψ⟩
  exact frontier_subset_iff_isClosed.2 ratioMinimizingBody_properties.1.2.1.isClosed hu

lemma critical_contact_of_sideNormal {H : Hex}
    (hH : ratioMinimizingBody ⊆ H.set) (ha : volume H.set=criticalHexArea ratioMinimizingBody)
    {u : E} (hu : u ∈ ratioMinimizingBody) (i : Fin 6) (he : H.sideNormal i u=1) :
    u ∈ criticalContactSet ratioMinimizingBody := by
  let G := H.sideRelabel i
  have hG : G.set=H.set := H.sideRelabel_set i
  have hd : ofHex G ∈ criticalFamily ratioMinimizingBody := by
    refine ⟨valid_ofHex G,encloses_ofHex (by rwa [hG]),?_⟩
    rw [covolume_ofHex,← ha,← hG,G.volume_eq_covolume,ENNReal.toReal_ofReal (abs_nonneg _)]
  refine mem_iUnion.2 ⟨0,⟨(ofHex G,u),⟨⟨hd,hu⟩,?_⟩,rfl⟩⟩
  change |(ofHex G).form 0 u|=1
  rw [form_ofHex]
  change |(H.sideRelabel i).φ₁ u|=1
  rw [H.sideRelabel_normal,he,abs_one]

/-- The entire boundary is covered by edges of critical hexagons, including
flat faces. Full coverage by their side midpoints is a stronger later step. -/
theorem criticalContactSet_eq_frontier_minimizer :
    criticalContactSet ratioMinimizingBody=frontier ratioMinimizingBody := by
  apply subset_antisymm (criticalContactSet_subset_frontier ratioMinimizingBody_properties.1)
  intro u hu
  have huK := frontier_subset_iff_isClosed.2 ratioMinimizingBody_properties.1.2.1.isClosed hu
  obtain ⟨ψ,hψ⟩ := exists_normalized_support_at_frontier ratioMinimizingBody_properties.1 hu
  obtain ⟨H,hH,ha,i,hi⟩ := minimizer_support_face_midpoint huK hψ
  have he : ψ=H.sideNormal i := H.support_unique_at_midpoint
    (criticalHexagon_of_minimizer_strict H hH ha) hH
    (fun F hF => by rw [ha]; exact criticalHexArea_le F hF) i ψ
    (normalizedSupportAt_abs ratioMinimizingBody_properties.1.2.2.2 hψ) hi
  exact critical_contact_of_sideNormal hH ha huK i (he ▸ hψ.1)

#print axioms exists_normalized_support_at_frontier
#print axioms minimizer_normalized_support_unique
#print axioms minimizer_frontier_unique_normalized_support
#print axioms criticalContactSet_eq_frontier_minimizer
end Certificate.Packing
