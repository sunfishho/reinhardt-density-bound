import Certificate.CriticalHexagonMidpointUniqueness
import Certificate.CriticalMidpointNormalContinuity

/-! The geometric critical hexagon is unique at a shared midpoint. Labels
and orientation may differ, so the conclusion is equality of the actual sets. -/
namespace Certificate.Packing
open Set MeasureTheory
set_option maxHeartbeats 0

lemma Hex.exists_positive_first_relabel (H : Hex) :
    ∃ R : Hex, R.set=H.set ∧ R.midpoint 0=H.midpoint 0 ∧ 0 < det2 R.v R.w := by
  by_cases hp : 0 < det2 H.v H.w
  · exact ⟨H,rfl,rfl,hp⟩
  · have hn : det2 H.v H.w < 0 := lt_of_le_of_ne (le_of_not_gt hp) H.hdet
    refine ⟨H.flip,H.flip_set,?_,?_⟩
    · change (1/2:ℝ) • (H.flip.a+H.flip.b)=(1/2:ℝ) • (H.a+H.b)
      rw [H.flip_first]
    · rw [H.flip_det]; linarith

/-- Any two minimum-area enclosing hexagons of the minimizer that share a
side midpoint are the same geometric region, regardless of side labels or
orientation. No claim that every boundary point is such a midpoint is used. -/
theorem criticalHexagon_of_minimizer_unique_at_midpoint (H G : Hex)
    (hH : ratioMinimizingBody ⊆ H.set) (hG : ratioMinimizingBody ⊆ G.set)
    (heH : volume H.set=criticalHexArea ratioMinimizingBody)
    (heG : volume G.set=criticalHexArea ratioMinimizingBody)
    (i j : Fin 6) (hp : H.midpoint i=G.midpoint j) : H.set=G.set := by
  obtain ⟨R,hRH,hRp,hRpos⟩ := (H.sideRelabel i).exists_positive_first_relabel
  obtain ⟨S,hSG,hSp,hSpos⟩ := (G.sideRelabel j).exists_positive_first_relabel
  have hr : R.set=H.set := hRH.trans (H.sideRelabel_set i)
  have hs : S.set=G.set := hSG.trans (G.sideRelabel_set j)
  have hrp : R.midpoint 0=H.midpoint i := hRp.trans (H.sideRelabel_midpoint i)
  have hsp : S.midpoint 0=G.midpoint j := hSp.trans (G.sideRelabel_midpoint j)
  have hKR : ratioMinimizingBody ⊆ R.set := by rwa [hr]
  have hKS : ratioMinimizingBody ⊆ S.set := by rwa [hs]
  have heR : volume R.set=criticalHexArea ratioMinimizingBody := by rwa [hr]
  have heS : volume S.set=criticalHexArea ratioMinimizingBody := by rwa [hs]
  have hRstrict := criticalHexagon_of_minimizer_strict R hKR heR
  have hSstrict := criticalHexagon_of_minimizer_strict S hKS heS
  have hmR : R.midpoint 1 ∈ ratioMinimizingBody :=
    frontier_subset_iff_isClosed.2 ratioMinimizingBody_properties.1.2.1.isClosed
      (criticalHexagon_of_minimizer_midpoint_frontier R hKR heR 1)
  have hmS : S.midpoint 1 ∈ ratioMinimizingBody :=
    frontier_subset_iff_isClosed.2 ratioMinimizingBody_properties.1.2.1.isClosed
      (criticalHexagon_of_minimizer_midpoint_frontier S hKS heS 1)
  have hD : det2 R.v R.w=det2 S.v S.w := by
    have hh := congrArg ENNReal.toReal (heR.trans heS.symm)
    rw [R.volume_eq_covolume,S.volume_eq_covolume,
      ENNReal.toReal_ofReal (abs_nonneg _),ENNReal.toReal_ofReal (abs_nonneg _),
      abs_of_pos hRpos,abs_of_pos hSpos] at hh
    exact hh
  have heq := R.set_eq_of_critical_first_midpoint S hRstrict hSstrict hKR hKS
    (fun F hF => by rw [heR]; exact criticalHexArea_le F hF) hmR hmS
    (hrp.trans (hp.trans hsp.symm)) hD
  rwa [hr,hs] at heq

def IsCriticalHexagonAt (p : E) (H : Hex) : Prop :=
  ratioMinimizingBody ⊆ H.set ∧ volume H.set=criticalHexArea ratioMinimizingBody ∧
    ∃ i : Fin 6, H.midpoint i=p

theorem criticalHexagonAt_set_unique {p : E} {H G : Hex}
    (hH : IsCriticalHexagonAt p H) (hG : IsCriticalHexagonAt p G) : H.set=G.set := by
  obtain ⟨i,hi⟩ := hH.2.2
  obtain ⟨j,hj⟩ := hG.2.2
  exact criticalHexagon_of_minimizer_unique_at_midpoint H G hH.1 hG.1 hH.2.1 hG.2.1 i j
    (hi.trans hj.symm)

theorem exists_unique_critical_hexagon_region {p : E} (hp : p ∈ criticalMidpointSet) :
    ∃! S : Set E, ∃ H : Hex, IsCriticalHexagonAt p H ∧ H.set=S := by
  obtain ⟨d,hd,hp⟩ := hp
  let H := d.toHex hd.1
  have hH : IsCriticalHexagonAt p H := ⟨hd.2.1,critical_parameter_area hd,⟨0,hp⟩⟩
  refine ⟨H.set,⟨H,hH,rfl⟩,?_⟩
  rintro S ⟨G,hG,rfl⟩
  exact criticalHexagonAt_set_unique hG hH

#print axioms criticalHexagon_of_minimizer_unique_at_midpoint
#print axioms exists_unique_critical_hexagon_region
end Certificate.Packing
