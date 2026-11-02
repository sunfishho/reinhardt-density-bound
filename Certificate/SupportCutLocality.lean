import Certificate.CriticalHexagonLimitTools
import Certificate.MinimizerMidpointTangents

/-! A support form at an uncut point of a slab cut supports the original
convex body. Applying this at all side midpoints recovers enclosure. -/
namespace Certificate.Packing
open Set Filter Topology MeasureTheory
set_option maxHeartbeats 0

lemma support_of_supportCut_at_strict_point {K : Set E} (hK : Convex ℝ K)
    (ψ φ : E →ₗ[ℝ] ℝ) {c : ℝ} {m : E} (hm : m ∈ K)
    (hstrict : |ψ m| < c) (hφm : φ m=1)
    (hφ : ∀ x ∈ supportCut K ψ c, φ x ≤ 1) : ∀ x ∈ K, φ x ≤ 1 := by
  intro x hx
  by_contra hn
  have hgt : 1 < φ x := lt_of_not_ge hn
  have ht : Tendsto (fun t : ℝ => (1-t) • m+t • x) (𝓝 0) (𝓝 m) := by
    simpa using (show Continuous (fun t : ℝ => (1-t) • m+t • x) from by fun_prop).tendsto 0
  have ev : ∀ᶠ t in 𝓝 (0:ℝ), |ψ ((1-t) • m+t • x)| < c :=
    (ψ.continuous_of_finiteDimensional.abs.tendsto m |>.comp ht).eventually (gt_mem_nhds hstrict)
  have ev1 : ∀ᶠ t in 𝓝 (0:ℝ), t < 1 :=
    continuousAt_id.eventually_lt continuousAt_const (by norm_num)
  obtain ⟨t,ht0,htc,ht1⟩ :=
    ((show ∀ᶠ t in 𝓝[>] (0:ℝ), 0<t from self_mem_nhdsWithin).and
      (nhdsWithin_le_nhds (ev.and ev1))).exists
  have hp : (1-t) • m+t • x ∈ supportCut K ψ c :=
    ⟨hK hm hx (by linarith) ht0.le (by ring),htc.le⟩
  have hb := hφ _ hp
  simp only [map_add,map_smul,smul_eq_mul,hφm] at hb
  nlinarith

lemma Hex.encloses_of_supportCut_midpoints (H : Hex) {K : Set E}
    (hK : IsSymmetricConvexDisc K) (ψ : E →ₗ[ℝ] ℝ) {c : ℝ}
    (he : supportCut K ψ c ⊆ H.set)
    (hm : ∀ i : Fin 6, H.midpoint i ∈ K)
    (hc : ∀ i : Fin 6, |ψ (H.midpoint i)| < c) : K ⊆ H.set := by
  have hb (i : Fin 6) : ∀ x ∈ K, H.sideNormal i x ≤ 1 :=
    support_of_supportCut_at_strict_point hK.1 ψ (H.sideNormal i) (hm i) (hc i)
      (H.sideNormal_midpoint i) (fun x hx => (le_abs_self _).trans (H.sideNormal_abs_le i (he hx)))
  have hab (i : Fin 6) (x : E) (hx : x ∈ K) : |H.sideNormal i x| ≤ 1 := by
    have hn := hb i (-x) ((hK.2.2.2 x).1 hx)
    rw [map_neg] at hn
    exact abs_le.2 ⟨by linarith,hb i x hx⟩
  intro x hx
  exact ⟨hab 0 x hx,hab 1 x hx,hab 2 x hx⟩

#print axioms support_of_supportCut_at_strict_point
#print axioms Hex.encloses_of_supportCut_midpoints
end Certificate.Packing
