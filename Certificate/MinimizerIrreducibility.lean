import Certificate.MinimizerConstruction

/-! A proper convex subdisc has strictly smaller area. Consequently the
constructed minimizing body cannot be shaved without decreasing its critical
hexagon area. This is the irreducibility step, not a boundary regularity axiom. -/
namespace Certificate.Packing
open Set MeasureTheory
set_option maxHeartbeats 0

lemma disc_area_strict_mono {K L : Set E} (hK : IsSymmetricConvexDisc K)
    (hL : IsSymmetricConvexDisc L) (hs : L ⊂ K) : (volume L).toReal < (volume K).toReal := by
  have hn : (interior K \ L).Nonempty := by
    by_contra hn
    have hi : interior K ⊆ L := by
      intro x hx
      by_contra hxL
      exact hn ⟨x,hx,hxL⟩
    have hh := closure_mono hi
    rw [hK.1.closure_interior_eq_closure_of_nonempty_interior hK.2.2.1,
      hK.2.1.isClosed.closure_eq,hL.2.1.isClosed.closure_eq] at hh
    exact hs.2 hh
  have hp : 0 < volume (K \ L) :=
    ((isOpen_interior.sdiff hL.2.1.isClosed).measure_pos volume hn).trans_le
      (measure_mono (sdiff_subset_sdiff_left interior_subset))
  rw [measure_sdiff hs.1 hL.2.1.measurableSet.nullMeasurableSet hL.2.1.measure_lt_top.ne] at hp
  exact (ENNReal.toReal_lt_toReal hL.2.1.measure_lt_top.ne hK.2.1.measure_lt_top.ne).2
    (tsub_pos_iff_lt.1 hp)

/-- Irreducibility: removing any nonempty convex portion strictly decreases
the minimum enclosing-hexagon area, provided the remainder is still a disc. -/
theorem ratioMinimizingBody_irreducible {L : Set E} (hL : IsSymmetricConvexDisc L)
    (hs : L ⊂ ratioMinimizingBody) : criticalHexArea L < criticalHexArea ratioMinimizingBody := by
  have hm := criticalHexArea_mono hs.1
  apply lt_of_le_of_ne hm
  intro he
  have hb : HexAreaLowerBound L (2*Real.sqrt 3) :=
    hexAreaLowerBound_iff_criticalHexArea.2 (by rw [he,ratioMinimizingBody_properties.2.1])
  have harea := ratioMinimizingBody_properties.2.2.2.2 L hL hb
  exact (not_le_of_gt (disc_area_strict_mono ratioMinimizingBody_properties.1 hL hs)) harea

#print axioms disc_area_strict_mono
#print axioms ratioMinimizingBody_irreducible
end Certificate.Packing
