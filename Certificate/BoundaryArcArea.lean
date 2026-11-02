import Certificate.RadialSectorArea

/-! Area assembly from a finite family of actual boundary arcs. The hypotheses
describe coverage and nonoverlap of the boundary, not an area formula. -/
namespace Certificate.Packing
open MeasureTheory Set
set_option maxHeartbeats 0

lemma radialSector_subset {K : Set E} (hc : Convex ℝ K) (hclosed : IsClosed K)
    (h0 : (0:E) ∈ K) {γ : ℝ → E} {a b : ℝ}
    (hb : ∀ t ∈ Ioo a b, γ t ∈ frontier K) : radialSector γ a b ⊆ K := by
  rintro z ⟨x,hx,rfl⟩
  have hb' : γ (x 1) ∈ K := hclosed.closure_eq ▸ frontier_subset_closure (hb _ hx.2)
  have hh := hc h0 hb' (sub_nonneg.2 hx.1.2.le) hx.1.1.le (sub_add_cancel 1 (x 0))
  simpa [radialMap] using hh

lemma radialSectors_disjoint {K : Set E} (hc : Convex ℝ K) (h0 : K ∈ nhds (0:E))
    {γ δ : ℝ → E} {a b : ℝ}
    (hγ : ∀ t ∈ Ioo a b, γ t ∈ frontier K)
    (hδ : ∀ t ∈ Ioo a b, δ t ∈ frontier K)
    (hne : ∀ s ∈ Ioo a b, ∀ t ∈ Ioo a b, γ s ≠ δ t) :
    Disjoint (radialSector γ a b) (radialSector δ a b) := by
  apply disjoint_left.2
  rintro z ⟨x,hx,hxz⟩ ⟨y,hy,hyz⟩
  have he : radialMap γ x = radialMap δ y := hxz.trans hyz.symm
  have hgx := (gauge_eq_one_iff_mem_frontier hc h0).2 (hγ _ hx.2)
  have hgy := (gauge_eq_one_iff_mem_frontier hc h0).2 (hδ _ hy.2)
  have hr := congrArg (gauge K) he
  simp only [radialMap,gauge_smul_of_nonneg hx.1.1.le,
    gauge_smul_of_nonneg hy.1.1.le,hgx,hgy,smul_eq_mul,mul_one] at hr
  apply hne _ hx.2 _ hy.2
  unfold radialMap at he
  rw [hr] at he
  exact (smul_right_injective E hy.1.1.ne') he

lemma radial_mem_segment (r : ℝ) (p : E) (hr : r ∈ Icc 0 1) :
    r • p ∈ segment ℝ (0:E) p := by
  refine ⟨1-r,r,sub_nonneg.2 hr.2,hr.1,by ring,?_⟩
  simp

/-- A finite arc decomposition of the boundary suffices for the measured-area
identity. Arc endpoints and the frontier have zero planar volume. -/
theorem area_eq_sum_boundary_integrals {ι : Type*} [Fintype ι]
    {K : Set E} (hcomp : IsCompact K) (hc : Convex ℝ K) (h0 : K ∈ nhds (0:E))
    (γ γ' : ι → ℝ → E) (T : ℝ)
    (hb : ∀ i t, t ∈ Icc 0 T → γ i t ∈ frontier K)
    (hcover : ∀ p ∈ frontier K, ∃ i t, t ∈ Icc 0 T ∧ γ i t = p)
    (hsimple : ∀ i j s t, s ∈ Ioo 0 T → t ∈ Ioo 0 T →
      γ i s = γ j t → i = j ∧ s = t)
    (hd : ∀ i t, t ∈ Ioo 0 T → HasDerivAt (γ i) (γ' i t) t) :
    (volume K).toReal = ∑ i, (1/2:ℝ) * ∫ t in Ioo 0 T, |det2 (γ i t) (γ' i t)| := by
  classical
  let S := fun i => radialSector (γ i) 0 T
  let N := frontier K ∪ {(0:E)} ∪
    (⋃ i, segment ℝ (0:E) (γ i 0)) ∪ (⋃ i, segment ℝ (0:E) (γ i T))
  have hN : volume N = 0 := by
    apply measure_union_null
    · apply measure_union_null
      · exact measure_union_null (hc.addHaar_frontier volume) (measure_singleton _)
      · exact measure_iUnion_null (fun i => volume_segment _ _)
    · exact measure_iUnion_null (fun i => volume_segment _ _)
  have hsub : ∀ i, S i ⊆ K := fun i => radialSector_subset hc hcomp.isClosed
    (mem_of_mem_nhds h0) (fun t ht => hb i t ⟨ht.1.le,ht.2.le⟩)
  have hfill : K ⊆ (⋃ i, S i) ∪ N := by
    intro x hx
    by_cases hx0 : x = 0
    · right; exact Or.inl (Or.inl (Or.inr hx0))
    let r := gauge K x
    have hr0 : 0 < r := (gauge_pos (absorbent_nhds_zero h0) (hcomp.isVonNBounded ℝ)).2 hx0
    have hr1 : r ≤ 1 := gauge_le_one_of_mem hx
    let p := r⁻¹ • x
    have hgp : gauge K p = 1 := by
      dsimp [p]
      rw [gauge_smul_of_nonneg (inv_nonneg.2 hr0.le),smul_eq_mul]
      exact inv_mul_cancel₀ hr0.ne'
    have hp : p ∈ frontier K := (gauge_eq_one_iff_mem_frontier hc h0).1 hgp
    have hxp : r • p = x := by dsimp [p]; rw [smul_inv_smul₀ hr0.ne']
    rcases hr1.eq_or_lt with hr | hr
    · right; left; left; left
      exact (gauge_eq_one_iff_mem_frontier hc h0).1 hr
    obtain ⟨i,t,ht,he⟩ := hcover p hp
    by_cases ht0 : t = 0
    · right; left; right
      apply mem_iUnion.2 ⟨i,?_⟩
      rw [← hxp,← he,ht0]
      exact radial_mem_segment _ _ ⟨hr0.le,hr1⟩
    by_cases htT : t = T
    · right; right
      apply mem_iUnion.2 ⟨i,?_⟩
      rw [← hxp,← he,htT]
      exact radial_mem_segment _ _ ⟨hr0.le,hr1⟩
    left
    apply mem_iUnion.2 ⟨i,?_⟩
    refine ⟨point r t,⟨⟨hr0,hr⟩,⟨lt_of_le_of_ne ht.1 (Ne.symm ht0),lt_of_le_of_ne ht.2 htT⟩⟩,?_⟩
    simpa [radialMap,point,he] using hxp
  have hvol : volume K = volume (⋃ i, S i) := by
    apply le_antisymm
    · calc
        volume K ≤ volume ((⋃ i, S i) ∪ N) := measure_mono hfill
        _ ≤ volume (⋃ i, S i) + volume N := measure_union_le _ _
        _ = volume (⋃ i, S i) := by rw [hN,add_zero]
    · exact measure_mono (iUnion_subset hsub)
  have hmeas : ∀ i, MeasurableSet (S i) := by
    intro i
    exact measurable_image_of_fderivWithin (measurableSet_radialDomain 0 T)
      (fun x hx => (radialMap_hasFDerivAt (hd i _ hx.2)).hasFDerivWithinAt)
      (radialMap_injOn hc h0 (fun t ht => hb i t ⟨ht.1.le,ht.2.le⟩)
        (fun s hs t ht he => (hsimple i i s t hs ht he).2))
  have hdis : Pairwise (fun i j => Disjoint (S i) (S j)) := by
    intro i j hij
    exact radialSectors_disjoint hc h0
      (fun t ht => hb i t ⟨ht.1.le,ht.2.le⟩)
      (fun t ht => hb j t ⟨ht.1.le,ht.2.le⟩)
      (fun s hs t ht he => hij (hsimple i j s t hs ht he).1)
  rw [hvol,measure_iUnion hdis hmeas,tsum_fintype,ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro i _
    exact radialSector_area hc h0 (fun t ht => hb i t ⟨ht.1.le,ht.2.le⟩)
      (fun s hs t ht he => (hsimple i i s t hs ht he).2) (hd i)
  · intro i _
    exact ((measure_mono (hsub i)).trans_lt hcomp.measure_lt_top).ne

#print axioms area_eq_sum_boundary_integrals
end Certificate.Packing
