import Certificate.CriticalHexagonAttainment

/-! Compactness of the entire family of critical hexagons and closedness of
its contact locus. Coverage of the minimizer boundary by this locus is a
separate geometric statement, not built into these definitions. -/
namespace Certificate.Packing
open Set MeasureTheory HexParameters
set_option maxHeartbeats 0

namespace HexParameters
def criticalFamily (K : Set E) : Set HexParameters :=
  {d | d.Valid ∧ Encloses K d ∧ d.covolume=(criticalHexArea K).toReal}

lemma isCompact_criticalFamily {K : Set E} (hK : IsSymmetricConvexDisc K) :
    IsCompact (criticalFamily K) := by
  obtain ⟨r,hr,h0,h1⟩ := exists_axis_points hK
  apply (isCompact_boundedEnclosers hr h0 h1 (criticalHexArea K).toReal).of_isClosed_subset
  · exact isClosed_valid.inter ((isClosed_encloses K).inter
      (isClosed_eq continuous_covolume continuous_const))
  · intro d hd; exact ⟨hd.1,hd.2.1,hd.2.2.le⟩

lemma criticalFamily_nonempty {K : Set E} (hK : IsSymmetricConvexDisc K) :
    (criticalFamily K).Nonempty := by
  obtain ⟨H,hH,he⟩ := criticalHexArea_attained K hK
  refine ⟨ofHex H,valid_ofHex H,encloses_ofHex hH,?_⟩
  rw [covolume_ofHex,← he,H.volume_eq_covolume,ENNReal.toReal_ofReal (abs_nonneg _)]
end HexParameters

noncomputable def criticalContactPiece (K : Set E) (i : Fin 3) : Set E :=
  Prod.snd '' ((criticalFamily K ×ˢ K) ∩
    {p : HexParameters × E | |p.1.form i p.2|=1})
noncomputable def criticalContactSet (K : Set E) : Set E := ⋃ i : Fin 3, criticalContactPiece K i

lemma isCompact_criticalContactSet {K : Set E} (hK : IsSymmetricConvexDisc K) :
    IsCompact (criticalContactSet K) := by
  apply isCompact_iUnion
  intro i
  apply IsCompact.image _ continuous_snd
  apply (isCompact_criticalFamily hK |>.prod hK.2.1).inter_right
  apply isClosed_eq _ continuous_const
  unfold HexParameters.form
  simp only [LinearMap.add_apply,LinearMap.smul_apply,smul_eq_mul,coord_eval]
  fun_prop

/-- A point of the body on a supporting strip boundary cannot be an interior
point. This theorem asserts containment, not full boundary coverage. -/
lemma criticalContactSet_subset_frontier {K : Set E} (hK : IsSymmetricConvexDisc K) :
    criticalContactSet K ⊆ frontier K := by
  intro x hx
  obtain ⟨i,hi⟩ := mem_iUnion.1 hx
  obtain ⟨⟨d,y⟩,⟨⟨hd,hy⟩,he⟩,rfl⟩ := hi
  refine ⟨hK.2.1.isClosed.closure_eq.symm ▸ hy,?_⟩
  intro hiy
  have hs : K ⊆ (d.toHex hd.1).set := hd.2.1
  have hh := (d.toHex hd.1).interior_set_subset (interior_mono hs hiy)
  have hlt : |d.form i y| < 1 := by
    fin_cases i
    · exact hh.1
    · exact hh.2.1
    · exact hh.2.2
  exact hlt.ne he

#print axioms isCompact_criticalFamily
#print axioms isCompact_criticalContactSet
#print axioms criticalContactSet_subset_frontier
end Certificate.Packing
