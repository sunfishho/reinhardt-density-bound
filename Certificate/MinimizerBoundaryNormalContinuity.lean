import Certificate.MinimizerBoundarySupport

/-! The normalized supporting form and an oriented tangent direction vary
continuously on the entire minimizer frontier. No differentiable boundary
parametrization or Lipschitz bound for these directions is assumed. -/
namespace Certificate.Packing
open Set MeasureTheory HexParameters Topology
set_option maxHeartbeats 0

noncomputable def criticalFirstSupportPairs : Set (HexParameters × E) :=
  (criticalFamily ratioMinimizingBody ×ˢ ratioMinimizingBody) ∩
    {p | p.1.form 0 p.2=1}

lemma isCompact_criticalFirstSupportPairs : IsCompact criticalFirstSupportPairs :=
  ((isCompact_criticalFamily ratioMinimizingBody_properties.1).prod
    ratioMinimizingBody_properties.1.2.1).inter_right
      (isClosed_eq (continuous_parameter_form 0) continuous_const)

lemma criticalFirstSupportPairs_frontier (p : criticalFirstSupportPairs) :
    p.val.2 ∈ frontier ratioMinimizingBody := by
  apply criticalContactSet_subset_frontier ratioMinimizingBody_properties.1
  apply critical_contact_of_sideNormal (H := p.val.1.toHex p.property.1.1.1) p.property.1.1.2.1
    (critical_parameter_area p.property.1.1) p.property.1.2 0
  exact p.property.2

lemma criticalFirstSupportPairs_support (p : criticalFirstSupportPairs) :
    NormalizedSupportAt ratioMinimizingBody p.val.2 (p.val.1.form 0) :=
  ⟨p.property.2,fun x hx => (le_abs_self _).trans (p.property.1.1.2.1 x hx).1⟩

noncomputable def criticalFirstSupportProjection
    (p : criticalFirstSupportPairs) : frontier ratioMinimizingBody :=
  ⟨p.val.2,criticalFirstSupportPairs_frontier p⟩

lemma continuous_criticalFirstSupportProjection : Continuous criticalFirstSupportProjection :=
  (continuous_snd.comp continuous_subtype_val).subtype_mk _

lemma criticalFirstSupportProjection_surjective : Function.Surjective criticalFirstSupportProjection := by
  intro p
  have hpK := frontier_subset_iff_isClosed.2 ratioMinimizingBody_properties.1.2.1.isClosed p.property
  obtain ⟨ψ,hψ⟩ := exists_normalized_support_at_frontier ratioMinimizingBody_properties.1 p.property
  obtain ⟨H,hH,ha,i,hi⟩ := minimizer_support_face_midpoint hpK hψ
  have he : ψ=H.sideNormal i := H.support_unique_at_midpoint
    (criticalHexagon_of_minimizer_strict H hH ha) hH
    (fun F hF => by rw [ha]; exact criticalHexArea_le F hF) i ψ
    (normalizedSupportAt_abs ratioMinimizingBody_properties.1.2.2.2 hψ) hi
  let G := H.sideRelabel i
  have hG : G.set=H.set := H.sideRelabel_set i
  have hd : ofHex G ∈ criticalFamily ratioMinimizingBody := by
    refine ⟨valid_ofHex G,encloses_ofHex (by rwa [hG]),?_⟩
    rw [covolume_ofHex,← ha,← hG,G.volume_eq_covolume,ENNReal.toReal_ofReal (abs_nonneg _)]
  have hform : (ofHex G).form 0 p.val=1 := by
    rw [form_ofHex]
    change (H.sideRelabel i).φ₁ p.val=1
    rw [H.sideRelabel_normal,← he]
    exact hψ.1
  exact ⟨⟨(ofHex G,p.val),⟨⟨hd,hpK⟩,hform⟩⟩,rfl⟩

noncomputable def minimizerBoundarySupportRepresentative
    (p : frontier ratioMinimizingBody) : criticalFirstSupportPairs :=
  Classical.choose (criticalFirstSupportProjection_surjective p)

lemma minimizerBoundarySupportRepresentative_point (p : frontier ratioMinimizingBody) :
    (minimizerBoundarySupportRepresentative p).val.2=p.val :=
  congrArg Subtype.val (Classical.choose_spec (criticalFirstSupportProjection_surjective p))

noncomputable def minimizerBoundaryNormal (p : frontier ratioMinimizingBody) : Fin 2 → ℝ :=
  (minimizerBoundarySupportRepresentative p).val.1.1 0

theorem minimizerBoundaryNormal_support (p : frontier ratioMinimizingBody) :
    NormalizedSupportAt ratioMinimizingBody p.val
      ((minimizerBoundaryNormal p 0) • coord 0+(minimizerBoundaryNormal p 1) • coord 1) := by
  have hs := criticalFirstSupportPairs_support (minimizerBoundarySupportRepresentative p)
  rw [minimizerBoundarySupportRepresentative_point] at hs
  exact hs

lemma minimizerBoundaryNormal_projection (p : criticalFirstSupportPairs) :
    minimizerBoundaryNormal (criticalFirstSupportProjection p)=p.val.1.1 0 := by
  have he := minimizer_normalized_support_unique p.property.1.2
    (minimizerBoundaryNormal_support (criticalFirstSupportProjection p))
    (criticalFirstSupportPairs_support p)
  ext i
  fin_cases i
  · have h := LinearMap.congr_fun he (point 1 0)
    simpa [HexParameters.form,point] using h
  · have h := LinearMap.congr_fun he (point 0 1)
    simpa [HexParameters.form,point] using h

/-- Compactness of critical edge-contact presentations and uniqueness of the
supporting form give continuity even at endpoints of flat supporting faces. -/
theorem continuous_minimizerBoundaryNormal : Continuous minimizerBoundaryNormal := by
  let : CompactSpace criticalFirstSupportPairs :=
    isCompact_iff_compactSpace.1 isCompact_criticalFirstSupportPairs
  have hq : IsQuotientMap criticalFirstSupportProjection :=
    continuous_criticalFirstSupportProjection.isClosedMap.isQuotientMap
      continuous_criticalFirstSupportProjection criticalFirstSupportProjection_surjective
  apply hq.continuous_iff.2
  have he : minimizerBoundaryNormal ∘ criticalFirstSupportProjection=
      fun p : criticalFirstSupportPairs => p.val.1.1 0 := by
    funext p; exact minimizerBoundaryNormal_projection p
  rw [he]
  fun_prop

theorem minimizerBoundaryNormal_eq_midpointNormal (p : criticalMidpointSet) :
    minimizerBoundaryNormal ⟨p.val,criticalMidpointSet_subset_frontier p.property⟩=
      criticalMidpointNormal p := by
  have hpK := frontier_subset_iff_isClosed.2 ratioMinimizingBody_properties.1.2.1.isClosed
    (criticalMidpointSet_subset_frontier p.property)
  have he := minimizer_normalized_support_unique hpK
    (minimizerBoundaryNormal_support ⟨p.val,criticalMidpointSet_subset_frontier p.property⟩)
    (criticalMidpointNormal_support p)
  ext i
  fin_cases i
  · have h := LinearMap.congr_fun he (point 1 0)
    simpa [point] using h
  · have h := LinearMap.congr_fun he (point 0 1)
    simpa [point] using h

/-- Rotate the outward support normal counterclockwise. This is a nonzero
tangent direction, normalized by det(p,tangent)=1 rather than unit length. -/
noncomputable def minimizerBoundaryTangent (p : frontier ratioMinimizingBody) : E :=
  point (-(minimizerBoundaryNormal p 1)) (minimizerBoundaryNormal p 0)

theorem continuous_minimizerBoundaryTangent : Continuous minimizerBoundaryTangent := by
  have h := continuous_minimizerBoundaryNormal
  unfold minimizerBoundaryTangent point
  fun_prop

theorem minimizerBoundaryTangent_det (p : frontier ratioMinimizingBody) :
    det2 p.val (minimizerBoundaryTangent p)=1 := by
  have h := (minimizerBoundaryNormal_support p).1
  simp only [LinearMap.add_apply,LinearMap.smul_apply,smul_eq_mul,coord_eval] at h
  simp [minimizerBoundaryTangent,det2,point]
  nlinarith

theorem minimizerBoundaryTangent_ne_zero (p : frontier ratioMinimizingBody) :
    minimizerBoundaryTangent p ≠ 0 := by
  intro he
  have h := minimizerBoundaryTangent_det p
  simp [he,det2] at h

theorem minimizerBoundaryTangent_support (p : frontier ratioMinimizingBody)
    {x : E} (hx : x ∈ ratioMinimizingBody) :
    0 ≤ det2 (minimizerBoundaryTangent p) (x-p.val) := by
  have hp := (minimizerBoundaryNormal_support p).1
  have hs := (minimizerBoundaryNormal_support p).2 x hx
  simp only [LinearMap.add_apply,LinearMap.smul_apply,smul_eq_mul,coord_eval] at hp hs
  simp [minimizerBoundaryTangent,det2,point]
  nlinarith

#print axioms criticalFirstSupportProjection_surjective
#print axioms minimizerBoundaryNormal_support
#print axioms continuous_minimizerBoundaryNormal
#print axioms minimizerBoundaryNormal_eq_midpointNormal
#print axioms continuous_minimizerBoundaryTangent
#print axioms minimizerBoundaryTangent_det
#print axioms minimizerBoundaryTangent_ne_zero
#print axioms minimizerBoundaryTangent_support
end Certificate.Packing
