import Certificate.CriticalHexagonFamilyCompactness
import Certificate.SymmetricSupportCuts

/-! Joint continuity and limit arguments for enclosing hexagons. -/
namespace Certificate.Packing
open Set Filter Topology MeasureTheory HexParameters
set_option maxHeartbeats 0

lemma continuous_parameter_form (i : Fin 3) :
    Continuous (fun p : HexParameters × E => p.1.form i p.2) := by
  simp only [HexParameters.form,LinearMap.add_apply,LinearMap.smul_apply,smul_eq_mul,coord_eval]
  fun_prop

noncomputable def maxStrip (d : HexParameters) (x : E) : ℝ :=
  max |d.form 0 x| (max |d.form 1 x| |d.form 2 x|)

lemma continuous_maxStrip : Continuous (fun p : HexParameters × E => maxStrip p.1 p.2) :=
  (continuous_parameter_form 0).abs.max
    ((continuous_parameter_form 1).abs.max (continuous_parameter_form 2).abs)

lemma maxStrip_le_iff (d : HexParameters) (x : E) :
    maxStrip d x ≤ 1 ↔ |d.form 0 x| ≤ 1 ∧ |d.form 1 x| ≤ 1 ∧ |d.form 2 x| ≤ 1 := by
  simp [maxStrip,max_le_iff]

lemma encloses_of_limit_scaled {K : Set E} {d : ℕ → HexParameters} {e : HexParameters}
    {s : ℕ → ℝ} (hd : Tendsto d atTop (𝓝 e)) (hs : Tendsto s atTop (𝓝 1))
    (hen : ∀ n x, x ∈ K → maxStrip (d n) (s n • x) ≤ 1) : Encloses K e := by
  intro x hx
  apply (maxStrip_le_iff e x).1
  have ht : Tendsto (fun n => (d n,s n • x)) atTop (𝓝 (e,x)) := by
    simpa using hd.prodMk_nhds (hs.smul_const x)
  exact le_of_tendsto' (continuous_maxStrip.tendsto (e,x) |>.comp ht) (fun n => hen n x hx)

lemma critical_of_bounded_encloses {K : Set E} (hK : IsSymmetricConvexDisc K)
    {d : HexParameters} (hv : d.Valid) (he : Encloses K d)
    (ha : d.covolume ≤ (criticalHexArea K).toReal) : d ∈ criticalFamily K := by
  refine ⟨hv,he,le_antisymm ha ?_⟩
  have hh := ENNReal.toReal_mono (d.toHex hv).isCompact_set.measure_lt_top.ne
    (criticalHexArea_le (d.toHex hv) he)
  rw [volume_toHex,ENNReal.toReal_ofReal (show 0 ≤ d.covolume from abs_nonneg _)] at hh
  exact hh

lemma mem_criticalContactSet_of_maxStrip {K : Set E} {d : HexParameters} {x : E}
    (hd : d ∈ criticalFamily K) (hx : x ∈ K) (he : 1 ≤ maxStrip d x) : x ∈ criticalContactSet K := by
  have hb := hd.2.1 x hx
  have hi : ∃ i : Fin 3, |d.form i x|=1 := by
    rcases le_max_iff.1 he with h0 | h12
    · exact ⟨0,le_antisymm hb.1 h0⟩
    · rcases le_max_iff.1 h12 with h1 | h2
      · exact ⟨1,le_antisymm hb.2.1 h1⟩
      · exact ⟨2,le_antisymm hb.2.2 h2⟩
  obtain ⟨i,hi⟩ := hi
  exact mem_iUnion.2 ⟨i,⟨(d,x),⟨⟨hd,hx⟩,hi⟩,rfl⟩⟩

lemma criticalContactSet_neg {K : Set E} (hsym : IsSymmetricSet K) {x : E}
    (hx : x ∈ criticalContactSet K) : -x ∈ criticalContactSet K := by
  obtain ⟨i,d,hd,rfl⟩ := mem_iUnion.1 hx
  refine mem_iUnion.2 ⟨i,⟨(d.1,-d.2),⟨⟨hd.1.1,(hsym d.2).1 hd.1.2⟩,?_⟩,rfl⟩⟩
  change |d.1.form i (-d.2)|=1
  simpa only [map_neg,abs_neg] using (show |d.1.form i d.2|=1 from hd.2)

#print axioms encloses_of_limit_scaled
#print axioms critical_of_bounded_encloses
end Certificate.Packing
