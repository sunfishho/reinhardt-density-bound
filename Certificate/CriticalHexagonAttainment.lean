import Certificate.HexagonParameterBounds
import Certificate.PackingFromHexagonInfimum

/-! The enclosing-hexagon area infimum is attained. The proof takes a minimum
on a compact set of bounded normal/vertex parameters, with nondegeneracy
proved from the closed incidence constraints. -/
namespace Certificate.Packing
open Set MeasureTheory HexParameters
set_option maxHeartbeats 0

/-- A minimum-area enclosing hexagon exists for every symmetric convex disc. -/
theorem exists_minimum_enclosing_hexagon (K : Set E) (hK : IsSymmetricConvexDisc K) :
    ∃ H : Hex, K ⊆ H.set ∧ ∀ G : Hex, K ⊆ G.set → volume H.set ≤ volume G.set := by
  obtain ⟨r,hr,h0,h1⟩ := exists_axis_points hK
  obtain ⟨H0,hH0⟩ := exists_enclosing_hexagon K hK
  let M := |det2 H0.v H0.w|
  have hne : (boundedEnclosers K M).Nonempty :=
    ⟨ofHex H0,valid_ofHex H0,encloses_ofHex hH0,(covolume_ofHex H0).le⟩
  obtain ⟨d,hd,hmin⟩ := (isCompact_boundedEnclosers hr h0 h1 M).exists_isMinOn hne
    continuous_covolume.continuousOn
  refine ⟨d.toHex hd.1,hd.2.1,?_⟩
  intro G hG
  have hc : d.covolume ≤ |det2 G.v G.w| := by
    by_cases hg : |det2 G.v G.w| ≤ M
    · have hh := hmin (show ofHex G ∈ boundedEnclosers K M from
        ⟨valid_ofHex G,encloses_ofHex hG,by rwa [covolume_ofHex]⟩)
      change d.covolume ≤ (ofHex G).covolume at hh
      rwa [covolume_ofHex] at hh
    · exact hd.2.2.trans (le_of_not_ge hg)
  rw [volume_toHex,G.volume_eq_covolume]
  exact ENNReal.ofReal_le_ofReal hc

/-- The previously defined infimum equals the area of an actual enclosing hexagon. -/
theorem criticalHexArea_attained (K : Set E) (hK : IsSymmetricConvexDisc K) :
    ∃ H : Hex, K ⊆ H.set ∧ volume H.set=criticalHexArea K := by
  obtain ⟨H,hH,hmin⟩ := exists_minimum_enclosing_hexagon K hK
  refine ⟨H,hH,le_antisymm ?_ (criticalHexArea_le H hH)⟩
  exact le_iInf (fun G => le_iInf (fun hG => hmin G hG))

#print axioms exists_minimum_enclosing_hexagon
#print axioms criticalHexArea_attained
end Certificate.Packing
