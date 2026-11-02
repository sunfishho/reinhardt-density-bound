import Certificate.CriticalHexagonLimitTools

/-! Every normalized supporting face of the minimizer meets the critical
contact locus. Symmetric cuts approach the body; irreducibility forces their
smaller enclosing hexagons to converge to a critical contact on the cut face.
This is not yet coverage of every point on a nonsingleton supporting face. -/
namespace Certificate.Packing
open Set Filter Topology MeasureTheory HexParameters
set_option maxHeartbeats 0

/-- A smaller enclosing hexagon of a proper slab cut supplies an excluded
point of the original body. Both objects will be compactly controlled. -/
lemma cut_witness {K : Set E} (hK : IsSymmetricConvexDisc K)
    (hirr : ∀ L, IsSymmetricConvexDisc L → L ⊂ K → criticalHexArea L < criticalHexArea K)
    {u : E} (hu : u ∈ K) {ψ : E →ₗ[ℝ] ℝ} (hψ : NormalizedSupportAt K u ψ) (n : ℕ) :
    ∃ p : HexParameters × E,
      p.1.Valid ∧ Encloses (supportCut K ψ (shaveScale n)) p.1 ∧
      p.1.covolume ≤ (criticalHexArea K).toReal ∧ p.2 ∈ K ∧
      1 < maxStrip p.1 p.2 ∧ shaveScale n < |ψ p.2| := by
  have hc : 0 < shaveScale n := lt_of_lt_of_le (by norm_num) (shaveScale_bounds n).1
  have hcut := supportCut_isDisc hK ψ hc
  obtain ⟨H,hH,he⟩ := criticalHexArea_attained _ hcut
  have hlt : volume H.set < criticalHexArea K :=
    he.trans_lt (hirr _ hcut (supportCut_proper hu hψ.1 (shaveScale_bounds n).2))
  have hnot : ¬ K ⊆ H.set := fun h => (not_lt_of_ge (criticalHexArea_le H h)) hlt
  obtain ⟨x,hx,hxn⟩ := Set.not_subset.1 hnot
  have hm : 1 < maxStrip (ofHex H) x := by
    apply lt_of_not_ge
    intro hh
    apply hxn
    simpa [form_ofHex,Hex.set] using (maxStrip_le_iff _ _).1 hh
  have hcutx : shaveScale n < |ψ x| := by
    apply lt_of_not_ge
    intro hh
    exact hxn (hH ⟨hx,hh⟩)
  refine ⟨(ofHex H,x),valid_ofHex H,encloses_ofHex hH,?_,hx,hm,hcutx⟩
  have hb := ENNReal.toReal_mono (criticalHexArea_finite hK) hlt.le
  rw [H.volume_eq_covolume,ENNReal.toReal_ofReal (abs_nonneg _)] at hb
  simpa [covolume_ofHex] using hb

/-- Irreducibility forces every supporting face to contain a critical contact.
For a singleton supporting face this already gives contact at its exposed point. -/
theorem support_face_meets_criticalContactSet {K : Set E} (hK : IsSymmetricConvexDisc K)
    (hirr : ∀ L, IsSymmetricConvexDisc L → L ⊂ K → criticalHexArea L < criticalHexArea K)
    {u : E} (hu : u ∈ K) {ψ : E →ₗ[ℝ] ℝ} (hψ : NormalizedSupportAt K u ψ) :
    ∃ x ∈ criticalContactSet K, ψ x=1 := by
  have habs := normalizedSupportAt_abs hK.2.2.2 hψ
  have hc := supportCut_isDisc hK ψ (by norm_num : (0:ℝ)<1/2)
  obtain ⟨r,hr,h0,h1⟩ := exists_axis_points hc
  let p : ℕ → HexParameters × E := fun n => Classical.choose (cut_witness hK hirr hu hψ n)
  have hp (n : ℕ) := Classical.choose_spec (cut_witness hK hirr hu hψ n)
  change ∀ n, (p n).1.Valid ∧ Encloses (supportCut K ψ (shaveScale n)) (p n).1 ∧
    (p n).1.covolume ≤ (criticalHexArea K).toReal ∧ (p n).2 ∈ K ∧
    1 < maxStrip (p n).1 (p n).2 ∧ shaveScale n < |ψ (p n).2| at hp
  have hpc (n : ℕ) : p n ∈ boundedEnclosers (supportCut K ψ (1/2)) (criticalHexArea K).toReal ×ˢ K := by
    refine ⟨⟨(hp n).1,?_,(hp n).2.2.1⟩,(hp n).2.2.2.1⟩
    intro x hx
    exact (hp n).2.1 x (supportCut_mono (shaveScale_bounds n).1 hx)
  obtain ⟨q,hq,f,hf,ht⟩ :=
    ((isCompact_boundedEnclosers hr h0 h1 (criticalHexArea K).toReal).prod hK.2.1).isSeqCompact hpc
  have hd : Tendsto (fun n => (p (f n)).1) atTop (𝓝 q.1) := continuous_fst.tendsto q |>.comp ht
  have hx : Tendsto (fun n => (p (f n)).2) atTop (𝓝 q.2) := continuous_snd.tendsto q |>.comp ht
  have hs : Tendsto (fun n => shaveScale (f n)) atTop (𝓝 (1:ℝ)) :=
    tendsto_shaveScale.comp hf.tendsto_atTop
  have hen : Encloses K q.1 := encloses_of_limit_scaled hd hs (by
    intro n x hx
    apply (maxStrip_le_iff _ _).2
    exact (hp (f n)).2.1 _ (smul_mem_supportCut hK ψ habs
      ⟨by linarith [(shaveScale_bounds (f n)).1],(shaveScale_bounds (f n)).2.le⟩ hx))
  have hcrit : q.1 ∈ criticalFamily K := critical_of_bounded_encloses hK hq.1.1 hen hq.1.2.2
  have hmax : 1 ≤ maxStrip q.1 q.2 :=
    ge_of_tendsto' (continuous_maxStrip.tendsto q |>.comp ht) (fun n => (hp (f n)).2.2.2.2.1.le)
  have hcontact := mem_criticalContactSet_of_maxStrip hcrit hq.2 hmax
  have hψlim : Tendsto (fun n => |ψ (p (f n)).2|) atTop (𝓝 |ψ q.2|) :=
    ψ.continuous_of_finiteDimensional.abs.tendsto q.2 |>.comp hx
  have hge : 1 ≤ |ψ q.2| := le_of_tendsto_of_tendsto' hs hψlim
    (fun n => (hp (f n)).2.2.2.2.2.le)
  have heq : |ψ q.2|=1 := le_antisymm (habs _ hq.2) hge
  rcases (abs_eq (by norm_num : (0:ℝ)≤1)).1 heq with he | he
  · exact ⟨q.2,hcontact,he⟩
  · exact ⟨-q.2,criticalContactSet_neg hK.2.2.2 hcontact,by rw [map_neg,he]; norm_num⟩

theorem minimizer_support_face_contact {u : E} (hu : u ∈ ratioMinimizingBody)
    {ψ : E →ₗ[ℝ] ℝ} (hψ : NormalizedSupportAt ratioMinimizingBody u ψ) :
    ∃ x ∈ criticalContactSet ratioMinimizingBody, ψ x=1 :=
  support_face_meets_criticalContactSet ratioMinimizingBody_properties.1
    (fun _ hL hs => ratioMinimizingBody_irreducible hL hs) hu hψ

theorem minimizer_exposed_point_contact {u : E} (hu : u ∈ ratioMinimizingBody)
    {ψ : E →ₗ[ℝ] ℝ} (hψ : NormalizedSupportAt ratioMinimizingBody u ψ)
    (hunique : ∀ x ∈ ratioMinimizingBody, ψ x=1 → x=u) :
    u ∈ criticalContactSet ratioMinimizingBody := by
  obtain ⟨x,hx,he⟩ := minimizer_support_face_contact hu hψ
  have hxK := (criticalContactSet_subset_frontier ratioMinimizingBody_properties.1 hx).1
  rw [ratioMinimizingBody_properties.1.2.1.isClosed.closure_eq] at hxK
  exact hunique x hxK he ▸ hx

#print axioms support_face_meets_criticalContactSet
#print axioms minimizer_support_face_contact
#print axioms minimizer_exposed_point_contact
end Certificate.Packing
