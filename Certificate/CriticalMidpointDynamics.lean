import Certificate.MinimizerCriticalHexagonUniqueness
import Certificate.MinimizerSupportFaceMidpoint

/-! Continuous motion of the six critical midpoints on their actual compact
locus. This does not assume or assert that the locus is the whole boundary. -/
namespace Certificate.Packing
open Set MeasureTheory HexParameters Topology
set_option maxHeartbeats 0

noncomputable def parameterSignedArea (d : HexParameters) : ℝ :=
  det2 (d.vertex 0+d.vertex 1) (d.vertex 1+d.vertex 2)

lemma continuous_parameterSignedArea : Continuous parameterSignedArea := by
  unfold parameterSignedArea det2 HexParameters.vertex point
  fun_prop

noncomputable def positiveCriticalFamily : Set HexParameters :=
  criticalFamily ratioMinimizingBody ∩ {d | 0 ≤ parameterSignedArea d}

theorem isCompact_positiveCriticalFamily : IsCompact positiveCriticalFamily :=
  (isCompact_criticalFamily ratioMinimizingBody_properties.1).inter_right
    (isClosed_le continuous_const continuous_parameterSignedArea)

lemma positiveCriticalFamily_pos {d : HexParameters} (hd : d ∈ positiveCriticalFamily) :
    0 < parameterSignedArea d :=
  lt_of_le_of_ne hd.2 (Ne.symm (d.toHex hd.1.1).hdet)

lemma positiveCriticalFamily_area {d : HexParameters} (hd : d ∈ positiveCriticalFamily) :
    parameterSignedArea d=(criticalHexArea ratioMinimizingBody).toReal := by
  have he := hd.1.2.2
  change |parameterSignedArea d|=_ at he
  rwa [abs_of_nonneg hd.2] at he

lemma ofHex_mem_positiveCriticalFamily (H : Hex)
    (hH : ratioMinimizingBody ⊆ H.set)
    (he : volume H.set=criticalHexArea ratioMinimizingBody)
    (hp : 0 < det2 H.v H.w) : ofHex H ∈ positiveCriticalFamily := by
  refine ⟨⟨valid_ofHex H,encloses_ofHex hH,?_⟩,?_⟩
  · rw [covolume_ofHex,← he,H.volume_eq_covolume,ENNReal.toReal_ofReal (abs_nonneg _)]
  · simpa [parameterSignedArea,vertex_ofHex,Hex.v,Hex.w] using hp.le

lemma positiveCriticalFamily_same_midpoints {d e : HexParameters}
    (hd : d ∈ positiveCriticalFamily) (he : e ∈ positiveCriticalFamily)
    (hp : parameterMidpoint d=parameterMidpoint e) (i : Fin 6) :
    parameterSideMidpoint d i=parameterSideMidpoint e i := by
  let H := d.toHex hd.1.1
  let G := e.toHex he.1.1
  have hH := critical_parameter_area hd.1
  have hG := critical_parameter_area he.1
  have hmH : H.midpoint 1 ∈ ratioMinimizingBody :=
    frontier_subset_iff_isClosed.2 ratioMinimizingBody_properties.1.2.1.isClosed
      (criticalHexagon_of_minimizer_midpoint_frontier H hd.1.2.1 hH 1)
  have hmG : G.midpoint 1 ∈ ratioMinimizingBody :=
    frontier_subset_iff_isClosed.2 ratioMinimizingBody_properties.1.2.1.isClosed
      (criticalHexagon_of_minimizer_midpoint_frontier G he.1.2.1 hG 1)
  have hD : det2 H.v H.w=det2 G.v G.w :=
    (positiveCriticalFamily_area hd).trans (positiveCriticalFamily_area he).symm
  have h1 := H.second_midpoint_eq_of_first G
    (criticalHexagon_of_minimizer_strict H hd.1.2.1 hH)
    (criticalHexagon_of_minimizer_strict G he.1.2.1 hG)
    hd.1.2.1 he.1.2.1 hmH hmG hp hD
  exact H.midpoints_eq_of_first_two G hp h1 i

noncomputable def positiveCriticalProjection
    (d : positiveCriticalFamily) : criticalMidpointSet :=
  ⟨parameterMidpoint d.val,⟨d.val,d.property.1,rfl⟩⟩

lemma continuous_positiveCriticalProjection : Continuous positiveCriticalProjection :=
  (continuous_parameterMidpoint.comp continuous_subtype_val).subtype_mk _

lemma positiveCriticalProjection_surjective : Function.Surjective positiveCriticalProjection := by
  rintro ⟨p,d,hd,hp⟩
  let H := d.toHex hd.1
  obtain ⟨R,hR,hm,hpos⟩ := H.exists_positive_first_relabel
  have hrK : ratioMinimizingBody ⊆ R.set := by rw [hR]; exact hd.2.1
  have hra : volume R.set=criticalHexArea ratioMinimizingBody := by
    rw [hR]; exact critical_parameter_area hd
  refine ⟨⟨ofHex R,ofHex_mem_positiveCriticalFamily R hrK hra hpos⟩,?_⟩
  apply Subtype.ext
  change parameterSideMidpoint (ofHex R) 0=p
  rw [parameterSideMidpoint_ofHex,hm]
  exact hp

noncomputable def positiveCriticalRepresentative (p : criticalMidpointSet) : positiveCriticalFamily :=
  Classical.choose (positiveCriticalProjection_surjective p)

lemma positiveCriticalRepresentative_point (p : criticalMidpointSet) :
    parameterMidpoint (positiveCriticalRepresentative p).val=p.val :=
  congrArg Subtype.val (Classical.choose_spec (positiveCriticalProjection_surjective p))

/-- The next midpoint in the positive orientation of the unique critical hexagon. -/
noncomputable def criticalMidpointNext (p : criticalMidpointSet) : criticalMidpointSet :=
  let d := positiveCriticalRepresentative p
  ⟨parameterSideMidpoint d.val 1,
    critical_hexagon_midpoint_mem_set (d.val.toHex d.property.1.1) d.property.1.2.1
      (critical_parameter_area d.property.1) 1⟩

lemma criticalMidpointNext_projection (d : positiveCriticalFamily) :
    (criticalMidpointNext (positiveCriticalProjection d)).val=parameterSideMidpoint d.val 1 :=
  positiveCriticalFamily_same_midpoints
    (positiveCriticalRepresentative (positiveCriticalProjection d)).property d.property
    (positiveCriticalRepresentative_point (positiveCriticalProjection d)) 1

theorem continuous_criticalMidpointNext : Continuous criticalMidpointNext := by
  letI : CompactSpace positiveCriticalFamily :=
    isCompact_iff_compactSpace.1 isCompact_positiveCriticalFamily
  have hq : IsQuotientMap positiveCriticalProjection :=
    continuous_positiveCriticalProjection.isClosedMap.isQuotientMap
      continuous_positiveCriticalProjection positiveCriticalProjection_surjective
  apply hq.continuous_iff.2
  apply Continuous.subtype_mk
  have he : (fun d => (criticalMidpointNext (positiveCriticalProjection d)).val)=
      (fun d : positiveCriticalFamily => parameterSideMidpoint d.val 1) := by
    funext d; exact criticalMidpointNext_projection d
  change Continuous (fun d => (criticalMidpointNext (positiveCriticalProjection d)).val)
  rw [he]
  exact (continuous_parameterSideMidpoint 1).comp continuous_subtype_val

theorem criticalMidpointNext_of_hexagon (H : Hex)
    (hH : ratioMinimizingBody ⊆ H.set)
    (he : volume H.set=criticalHexArea ratioMinimizingBody)
    (hp : 0 < det2 H.v H.w) :
    (criticalMidpointNext ⟨H.midpoint 0,critical_hexagon_midpoint_mem_set H hH he 0⟩).val=
      H.midpoint 1 := by
  let d : positiveCriticalFamily := ⟨ofHex H,ofHex_mem_positiveCriticalFamily H hH he hp⟩
  have hd : positiveCriticalProjection d=
      ⟨H.midpoint 0,critical_hexagon_midpoint_mem_set H hH he 0⟩ := by
    apply Subtype.ext
    exact parameterSideMidpoint_ofHex H 0
  rw [← hd,criticalMidpointNext_projection]
  exact parameterSideMidpoint_ofHex H 1

#print axioms isCompact_positiveCriticalFamily
#print axioms positiveCriticalFamily_same_midpoints
#print axioms positiveCriticalProjection_surjective
#print axioms continuous_criticalMidpointNext
#print axioms criticalMidpointNext_of_hexagon
end Certificate.Packing
