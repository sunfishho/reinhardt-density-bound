import Certificate.MinimizerFundamentalAngle
import Certificate.MinimizerEndpointVelocities

/-! The constructed fundamental interval parametrizes exactly the open sector
between the initial midpoint and its successor, with no repetitions. -/
namespace Certificate.Packing
open Set Filter Topology MeasureTheory
set_option maxHeartbeats 300000

theorem minimizerAngularStart_det_pos_iff (x : E) :
    0 < det2 (minimizerAngularMidpoint 0).val x ↔ 0 < x 1 := by
  have hg : 0 < (gauge ratioMinimizingBody (point 1 0))⁻¹ :=
    inv_pos.2 (disc_gauge_pos ratioMinimizingBody_properties.1 (by
      intro h; have := congrArg (fun z : E => z 0) h; norm_num [point] at this))
  change 0 < det2 (minimizerRadialFoot (unitCirclePoint 0)) x ↔ _
  simp only [unitCirclePoint, Real.cos_zero,Real.sin_zero,one_smul,zero_smul,add_zero,
    minimizerRadialFoot,det2,PiLp.smul_apply,smul_eq_mul,point_zero,point_one,mul_one,mul_zero,zero_mul,sub_zero]
  exact mul_pos_iff_of_pos_left hg

theorem minimizerAngular_in_fundamental_sector {s : ℝ}
    (hs : s ∈ Ioo 0 minimizerFundamentalAngle) :
    InCriticalMidpointSector (minimizerAngularMidpoint 0) (minimizerAngularMidpoint s).val := by
  apply (inCriticalMidpointSector_iff_det_pos _ _).2
  have hθ := minimizerFundamentalAngle_mem
  constructor
  · exact (minimizerAngularBoundary_det_sign 0 s).2 (by
      rw [sub_zero]; exact Real.sin_pos_of_pos_of_lt_pi hs.1 (hs.2.trans hθ.2))
  · rw [← minimizerFundamentalAngle_endpoint]
    exact (minimizerAngularBoundary_det_sign s minimizerFundamentalAngle).2
      (Real.sin_pos_of_pos_of_lt_pi (sub_pos.2 hs.2) (by linarith [hs.1,hθ.2]))

theorem minimizerFundamentalSector_angular_range {p : criticalMidpointSet}
    (hp : InCriticalMidpointSector (minimizerAngularMidpoint 0) p.val) :
    ∃ s ∈ Ioo 0 minimizerFundamentalAngle, minimizerAngularMidpoint s=p := by
  obtain ⟨hl,hr⟩ := (inCriticalMidpointSector_iff_det_pos _ _).1 hp
  have hy := (minimizerAngularStart_det_pos_iff p.val).1 hl
  obtain ⟨s,hs,he⟩ := minimizerAngularBoundary_upper_surjective
    (criticalMidpointSet_subset_frontier p.property) hy
  have hep : minimizerAngularMidpoint s=p := Subtype.ext he
  have hsin : 0 < Real.sin (minimizerFundamentalAngle-s) := by
    rw [← hep,← minimizerFundamentalAngle_endpoint] at hr
    exact (minimizerAngularBoundary_det_sign s minimizerFundamentalAngle).1 hr
  have hlt : s < minimizerFundamentalAngle := by
    by_contra hn
    have hnon := Real.sin_nonpos_of_nonpos_of_neg_pi_le (by linarith : minimizerFundamentalAngle-s ≤ 0)
      (by linarith [hs.2,minimizerFundamentalAngle_mem.1])
    linarith
  exact ⟨s,⟨hs.1,hlt⟩,hep⟩

theorem minimizerAngularTime_duration :
    minimizerAngularTime minimizerFundamentalDuration=minimizerFundamentalAngle :=
  minimizerAngularTime_clock _

theorem minimizerAngularTime_mem_fundamental_iff (t : ℝ) :
    minimizerAngularTime t ∈ Ioo 0 minimizerFundamentalAngle ↔ t ∈ Ioo 0 minimizerFundamentalDuration := by
  change (0 < minimizerAngularTime t ∧ minimizerAngularTime t < minimizerFundamentalAngle) ↔ _
  apply and_congr
  · simpa only [minimizerAngularTime_zero] using
      (show minimizerAngularTime 0 < minimizerAngularTime t ↔ 0 < t from strictMono_minimizerAngularTime.lt_iff_lt)
  · simpa only [minimizerAngularTime_duration] using
      (show minimizerAngularTime t < minimizerAngularTime minimizerFundamentalDuration ↔ t < minimizerFundamentalDuration
        from strictMono_minimizerAngularTime.lt_iff_lt)

theorem minimizerAngularTime_mem_closed_fundamental_iff (t : ℝ) :
    minimizerAngularTime t ∈ Icc 0 minimizerFundamentalAngle ↔ t ∈ Icc 0 minimizerFundamentalDuration := by
  change (0 ≤ minimizerAngularTime t ∧ minimizerAngularTime t ≤ minimizerFundamentalAngle) ↔ _
  apply and_congr
  · simpa only [minimizerAngularTime_zero] using
      (show minimizerAngularTime 0 ≤ minimizerAngularTime t ↔ 0 ≤ t from strictMono_minimizerAngularTime.le_iff_le)
  · simpa only [minimizerAngularTime_duration] using
      (show minimizerAngularTime t ≤ minimizerAngularTime minimizerFundamentalDuration ↔ t ≤ minimizerFundamentalDuration
        from strictMono_minimizerAngularTime.le_iff_le)

theorem minimizerTimedMidpoint_in_fundamental_sector {t : ℝ}
    (ht : t ∈ Ioo 0 minimizerFundamentalDuration) :
    InCriticalMidpointSector (minimizerTimedMidpoint 0) (minimizerTimedMidpoint t).val := by
  have hh := minimizerAngular_in_fundamental_sector ((minimizerAngularTime_mem_fundamental_iff t).2 ht)
  simpa only [minimizerTimedMidpoint,minimizerAngularTime_zero] using hh

theorem minimizerFundamentalSector_timed_range {p : criticalMidpointSet}
    (hp : InCriticalMidpointSector (minimizerTimedMidpoint 0) p.val) :
    ∃ t ∈ Ioo 0 minimizerFundamentalDuration, minimizerTimedMidpoint t=p := by
  have hp' : InCriticalMidpointSector (minimizerAngularMidpoint 0) p.val := by
    simpa only [minimizerTimedMidpoint,minimizerAngularTime_zero] using hp
  obtain ⟨s,hs,he⟩ := minimizerFundamentalSector_angular_range hp'
  refine ⟨minimizerDeterminantClock s,?_,?_⟩
  · apply (minimizerAngularTime_mem_fundamental_iff _).1
    rwa [minimizerAngularTime_clock]
  · simpa only [minimizerTimedMidpoint,minimizerAngularTime_clock] using he

theorem minimizerTimedMidpoint_injOn_fundamental :
    InjOn minimizerTimedMidpoint (Icc 0 minimizerFundamentalDuration) := by
  intro s hs t ht he
  have hs' := (minimizerAngularTime_mem_closed_fundamental_iff s).2 hs
  have ht' := (minimizerAngularTime_mem_closed_fundamental_iff t).2 ht
  apply strictMono_minimizerAngularTime.injective
  apply minimizerAngularBoundary_injOn_half ⟨hs'.1,hs'.2.trans minimizerFundamentalAngle_mem.2.le⟩
    ⟨ht'.1,ht'.2.trans minimizerFundamentalAngle_mem.2.le⟩
  exact Subtype.ext (congrArg (fun p : criticalMidpointSet => p.val) he)

end Certificate.Packing
