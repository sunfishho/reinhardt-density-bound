import Certificate.MinimizerMidpointTangents
import Certificate.CriticalHexagonFamilyCompactness

/-! The critical midpoints form a compact subset of the boundary, and their
uniquely determined normalized support normals vary continuously on that set.
No equality with the entire boundary is assumed or asserted. -/
namespace Certificate.Packing
open Set MeasureTheory HexParameters Topology
set_option maxHeartbeats 0

noncomputable def parameterMidpoint (d : HexParameters) : E :=
  (1/2:ℝ) • (d.vertex 0+d.vertex 1)

lemma continuous_parameterMidpoint : Continuous parameterMidpoint := by
  unfold parameterMidpoint HexParameters.vertex point
  fun_prop

lemma critical_parameter_area {d : HexParameters} (hd : d ∈ criticalFamily ratioMinimizingBody) :
    volume (d.toHex hd.1).set=criticalHexArea ratioMinimizingBody := by
  rw [volume_toHex,hd.2.2,ENNReal.ofReal_toReal (criticalHexArea_finite ratioMinimizingBody_properties.1)]

lemma critical_parameter_support {d : HexParameters} (hd : d ∈ criticalFamily ratioMinimizingBody) :
    NormalizedSupportAt ratioMinimizingBody (parameterMidpoint d) (d.form 0) := by
  refine ⟨(d.toHex hd.1).sideNormal_midpoint 0,?_⟩
  intro x hx
  exact (le_abs_self _).trans (hd.2.1 x hx).1

lemma critical_parameter_normal_eq {d e : HexParameters}
    (hd : d ∈ criticalFamily ratioMinimizingBody) (he : e ∈ criticalFamily ratioMinimizingBody)
    (hp : parameterMidpoint d=parameterMidpoint e) : d.1 0=e.1 0 := by
  have hu := criticalHexagon_of_minimizer_unique_support (d.toHex hd.1) hd.2.1
    (critical_parameter_area hd) 0
  have hde : d.form 0=e.form 0 := hu.unique (critical_parameter_support hd)
    (by change NormalizedSupportAt _ (parameterMidpoint d) _; rw [hp]; exact critical_parameter_support he)
  ext i
  fin_cases i
  · have hh := LinearMap.congr_fun hde (point 1 0)
    simpa [HexParameters.form,point] using hh
  · have hh := LinearMap.congr_fun hde (point 0 1)
    simpa [HexParameters.form,point] using hh

noncomputable def criticalMidpointSet : Set E := parameterMidpoint '' criticalFamily ratioMinimizingBody

theorem isCompact_criticalMidpointSet : IsCompact criticalMidpointSet :=
  (isCompact_criticalFamily ratioMinimizingBody_properties.1).image continuous_parameterMidpoint

theorem criticalMidpointSet_subset_frontier : criticalMidpointSet ⊆ frontier ratioMinimizingBody := by
  rintro p ⟨d,hd,rfl⟩
  exact criticalHexagon_of_minimizer_midpoint_frontier (d.toHex hd.1) hd.2.1
    (critical_parameter_area hd) 0

/-- Relabeling shows that the set includes every side midpoint, not merely
the first midpoint of one chosen hexagon. -/
theorem critical_hexagon_midpoint_mem_set (H : Hex) (hs : ratioMinimizingBody ⊆ H.set)
    (he : volume H.set=criticalHexArea ratioMinimizingBody) (i : Fin 6) :
    H.midpoint i ∈ criticalMidpointSet := by
  let G := H.sideRelabel i
  have hG : G.set=H.set := H.sideRelabel_set i
  have hg : ofHex G ∈ criticalFamily ratioMinimizingBody := by
    refine ⟨valid_ofHex G,encloses_ofHex (by rwa [hG]),?_⟩
    rw [covolume_ofHex,← he,← hG,G.volume_eq_covolume,ENNReal.toReal_ofReal (abs_nonneg _)]
  refine ⟨ofHex G,hg,?_⟩
  simpa [parameterMidpoint,vertex_ofHex] using H.sideRelabel_midpoint i

noncomputable def criticalMidpointRepresentative (p : criticalMidpointSet) :
    {d : HexParameters // d ∈ criticalFamily ratioMinimizingBody} :=
  ⟨Classical.choose p.property,(Classical.choose_spec p.property).1⟩

lemma criticalMidpointRepresentative_point (p : criticalMidpointSet) :
    parameterMidpoint (criticalMidpointRepresentative p).val=p.val :=
  (Classical.choose_spec p.property).2

noncomputable def criticalMidpointNormal (p : criticalMidpointSet) : Fin 2 → ℝ :=
  (criticalMidpointRepresentative p).val.1 0

noncomputable def criticalMidpointProjection
    (d : {d : HexParameters // d ∈ criticalFamily ratioMinimizingBody}) : criticalMidpointSet :=
  ⟨parameterMidpoint d.val,⟨d.val,d.property,rfl⟩⟩

lemma continuous_criticalMidpointProjection : Continuous criticalMidpointProjection := by
  exact (continuous_parameterMidpoint.comp continuous_subtype_val).subtype_mk _

lemma criticalMidpointProjection_surjective : Function.Surjective criticalMidpointProjection := by
  intro p
  refine ⟨criticalMidpointRepresentative p,?_⟩
  apply Subtype.ext
  exact criticalMidpointRepresentative_point p

/-- Compactness plus uniqueness makes the normal a continuous function of
the midpoint, even when different critical-hexagon parameter records coincide
at that midpoint. -/
theorem continuous_criticalMidpointNormal : Continuous criticalMidpointNormal := by
  letI : CompactSpace {d : HexParameters // d ∈ criticalFamily ratioMinimizingBody} :=
    isCompact_iff_compactSpace.1 (isCompact_criticalFamily ratioMinimizingBody_properties.1)
  have hq : IsQuotientMap criticalMidpointProjection :=
    continuous_criticalMidpointProjection.isClosedMap.isQuotientMap
      continuous_criticalMidpointProjection criticalMidpointProjection_surjective
  apply hq.continuous_iff.2
  have he : criticalMidpointNormal ∘ criticalMidpointProjection =
      fun d : {d : HexParameters // d ∈ criticalFamily ratioMinimizingBody} => d.val.1 0 := by
    funext d
    exact critical_parameter_normal_eq (criticalMidpointRepresentative (criticalMidpointProjection d)).property
      d.property (criticalMidpointRepresentative_point (criticalMidpointProjection d))
  rw [he]
  fun_prop

theorem criticalMidpointNormal_support (p : criticalMidpointSet) :
    NormalizedSupportAt ratioMinimizingBody p.val
      ((criticalMidpointNormal p 0) • coord 0+(criticalMidpointNormal p 1) • coord 1) := by
  have hh := critical_parameter_support (criticalMidpointRepresentative p).property
  rw [criticalMidpointRepresentative_point] at hh
  exact hh

#print axioms isCompact_criticalMidpointSet
#print axioms criticalMidpointSet_subset_frontier
#print axioms critical_hexagon_midpoint_mem_set
#print axioms continuous_criticalMidpointNormal
#print axioms criticalMidpointNormal_support
end Certificate.Packing
