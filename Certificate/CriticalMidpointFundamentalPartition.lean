import Certificate.CriticalMidpointOrder

/-! The six reference midpoints partition the boundary into their six open
sectors and the six separating points. This is a finite planar statement. -/
namespace Certificate.Packing
open Set Filter Topology
set_option maxHeartbeats 300000

noncomputable def criticalMidpointStep (p : criticalMidpointSet) (i : Fin 6) : criticalMidpointSet :=
  criticalMidpointNext^[i.val] p

theorem criticalMidpointStep_val (p : criticalMidpointSet) (i : Fin 6) :
    (criticalMidpointStep p i).val=criticalMidpointConfiguration p i := by
  fin_cases i
  · rfl
  · rfl
  · exact criticalMidpointNext_balance p
  · exact criticalMidpointNext_third p
  · exact criticalMidpointNext_third (criticalMidpointNext p)
  · change (criticalMidpointNext (criticalMidpointNext (criticalMidpointNext
      (criticalMidpointNext (criticalMidpointNext p))))).val=p.val-(criticalMidpointNext p).val
    rw [criticalMidpointNext_third,criticalMidpointNext_balance]
    abel

theorem criticalMidpointStep_next (p : criticalMidpointSet) (i : Fin 6) :
    criticalMidpointNext (criticalMidpointStep p i)=criticalMidpointStep p (i+1) := by
  fin_cases i
  all_goals first | rfl | exact criticalMidpointNext_sixth p

theorem criticalMidpointStep_surjective (i : Fin 6) : Function.Surjective (fun p => criticalMidpointStep p i) :=
  criticalMidpointHomeomorph.surjective.iterate i.val

theorem criticalMidpointStep_injective (i : Fin 6) : Function.Injective (fun p => criticalMidpointStep p i) :=
  criticalMidpointHomeomorph.injective.iterate i.val

theorem criticalMidpointStep_sector_iff (p r : criticalMidpointSet) (i : Fin 6) :
    InCriticalMidpointSector (criticalMidpointStep p i) (criticalMidpointStep r i).val ↔
      InCriticalMidpointSector p r.val := by
  have hd (n : ℕ) (x y : criticalMidpointSet) :
      0 < det2 (criticalMidpointNext^[n] x).val (criticalMidpointNext^[n] y).val ↔ 0 < det2 x.val y.val := by
    induction n with
    | zero => rfl
    | succ n ih =>
        rw [Function.iterate_succ_apply',Function.iterate_succ_apply',criticalMidpointNext_det_pos_iff,ih]
  rw [inCriticalMidpointSector_iff_det_pos,inCriticalMidpointSector_iff_det_pos]
  constructor
  · intro h
    refine ⟨(hd i.val p r).1 h.1,?_⟩
    apply (hd i.val r (criticalMidpointNext p)).1
    simpa only [criticalMidpointStep,Function.iterate_succ_apply',← Function.iterate_succ_apply] using h.2
  · intro h
    refine ⟨(hd i.val p r).2 h.1,?_⟩
    have hh := (hd i.val r (criticalMidpointNext p)).2 h.2
    simpa only [criticalMidpointStep,Function.iterate_succ_apply',← Function.iterate_succ_apply] using hh

theorem criticalMidpoint_partition (p r : criticalMidpointSet) :
    ∃ i : Fin 6, r=criticalMidpointStep p i ∨ InCriticalMidpointSector (criticalMidpointStep p i) r.val := by
  let L := pairFrame p.val (criticalMidpointNext p).val (criticalMidpointNext_det_pos p).ne'
  let a := L.symm r.val 0
  let b := L.symm r.val 1
  have he : r.val=a • p.val+b • (criticalMidpointNext p).val := (L.apply_symm_apply _).symm
  have ray (i : Fin 6) (c : ℝ) (hc : 0 < c) (h : r.val=c • criticalMidpointConfiguration p i) :
      r=criticalMidpointStep p i :=
    criticalMidpoint_eq_of_pos_smul _ _ hc (by rwa [criticalMidpointStep_val])
  have sector (i : Fin 6) (c d : ℝ) (hc : 0 < c) (hd : 0 < d)
      (h : r.val=c • criticalMidpointConfiguration p i+d • criticalMidpointConfiguration p (i+1)) :
      InCriticalMidpointSector (criticalMidpointStep p i) r.val := by
    refine ⟨c,d,hc,hd,?_⟩
    rwa [criticalMidpointStep_next,criticalMidpointStep_val,criticalMidpointStep_val]
  rcases lt_trichotomy 0 b with hb | hb | hb
  · rcases lt_trichotomy 0 a with ha | ha | ha
    · exact ⟨0,Or.inr (sector 0 a b ha hb he)⟩
    · exact ⟨1,Or.inl (ray 1 b hb (by simpa [← ha,criticalMidpointConfiguration] using he))⟩
    · rcases lt_trichotomy 0 (a+b) with hab | hab | hab
      · refine ⟨1,Or.inr (sector 1 (a+b) (-a) hab (by linarith) ?_)⟩
        change r.val=(a+b) • (criticalMidpointNext p).val+(-a) • ((criticalMidpointNext p).val-p.val)
        rw [he]; module
      · refine ⟨2,Or.inl (ray 2 b hb ?_)⟩
        have ha' : a= -b := by linarith
        change r.val=b • ((criticalMidpointNext p).val-p.val)
        rw [he,ha']; module
      · refine ⟨2,Or.inr (sector 2 b (-a-b) hb (by linarith) ?_)⟩
        change r.val=b • ((criticalMidpointNext p).val-p.val)+(-a-b) • (-p.val)
        rw [he]; module
  · have hb' : b=0 := hb.symm
    rcases lt_trichotomy 0 a with ha | ha | ha
    · exact ⟨0,Or.inl (ray 0 a ha (by simpa [hb',criticalMidpointConfiguration] using he))⟩
    · have hz : r.val=0 := by simpa [← ha,hb'] using he
      exact (criticalMidpoint_ne_zero r hz).elim
    · refine ⟨3,Or.inl (ray 3 (-a) (by linarith) ?_)⟩
      change r.val=(-a) • (-p.val)
      rw [he,hb']; module
  · rcases lt_trichotomy 0 a with ha | ha | ha
    · rcases lt_trichotomy 0 (a+b) with hab | hab | hab
      · refine ⟨5,Or.inr (sector 5 (-b) (a+b) (by linarith) hab ?_)⟩
        change r.val=(-b) • (p.val-(criticalMidpointNext p).val)+(a+b) • p.val
        rw [he]; module
      · refine ⟨5,Or.inl (ray 5 a ha ?_)⟩
        have hb' : b= -a := by linarith
        change r.val=a • (p.val-(criticalMidpointNext p).val)
        rw [he,hb']; module
      · refine ⟨4,Or.inr (sector 4 (-a-b) a (by linarith) ha ?_)⟩
        change r.val=(-a-b) • (-(criticalMidpointNext p).val)+a • (p.val-(criticalMidpointNext p).val)
        rw [he]; module
    · refine ⟨4,Or.inl (ray 4 (-b) (by linarith) ?_)⟩
      change r.val=(-b) • (-(criticalMidpointNext p).val)
      rw [he,← ha]; module
    · refine ⟨3,Or.inr (sector 3 (-a) (-b) (by linarith) (by linarith) ?_)⟩
      change r.val=(-a) • (-p.val)+(-b) • (-(criticalMidpointNext p).val)
      rw [he]; module

end Certificate.Packing
