import Certificate.HexagonSideVariation
import Certificate.CriticalHexagonAttainment
import Mathlib.Analysis.LocallyConvex.Separation

/-! A strict critical hexagon has a contact at the midpoint of its first side.
Separation of a missing midpoint produces an enclosing side variation whose
exact area formula is strictly decreasing for sufficiently small positive time. -/
namespace Certificate.Packing
open Set MeasureTheory Filter Topology
set_option maxHeartbeats 0

namespace Hex

lemma strict_first_det_pos (H : Hex) (hs : H.Strict) (hD : 0 < det2 H.v H.w) :
    0 < det2 H.a H.b := by
  have hn := (H.fan_determinants_nonneg hD.le).1
  have he : det2 (HVGeometry.pairLinear H.φ₁ H.φ₃ H.a)
      (HVGeometry.pairLinear H.φ₁ H.φ₃ H.b) = H.φ₃ H.b+1 := by
    simp [HVGeometry.pairLinear,det2,point,H.ha₁,H.hb₁,H.ha₃]
  have hne : det2 H.a H.b ≠ 0 := by
    intro hz
    rw [det2_linearMap,hz,mul_zero] at he
    have hb := (abs_lt.1 hs.2.1).1
    linarith
  exact lt_of_le_of_ne hn (Ne.symm hne)

/-- A separating functional permits a smaller enclosing hexagon. -/
theorem exists_smaller_of_separated_midpoint (H : Hex) (hs : H.Strict)
    (hD : 0 < det2 H.v H.w) {K : Set E} (hKH : K ⊆ H.set)
    (ψ : E →ₗ[ℝ] ℝ) (c : ℝ) (hc : 0 < c)
    (hψ : ∀ x ∈ K, |ψ x| ≤ c) (hm : c < ψ ((1/2:ℝ) • (H.a+H.b))) :
    ∃ G : Hex, K ⊆ G.set ∧ volume G.set < volume H.set := by
  let ζ := ψ-c • H.φ₁
  have hz : 0 < ζ H.a+ζ H.b := by
    dsimp [ζ]
    simp only [map_smul,map_add,smul_eq_mul] at hm
    simp only [LinearMap.sub_apply,LinearMap.smul_apply,smul_eq_mul,H.ha₁,H.hb₁]
    linarith
  let D : ℝ → ℝ := fun t => det2 (H.movedA ζ t+H.movedB ζ t) (H.movedB ζ t+H.c)
  let Q := det2 H.a H.b*(ζ H.a*ζ H.slideB+ζ H.b*ζ H.slideA)-
    ζ H.a*ζ H.b*det2 H.slideA H.slideB
  have hAc := H.movedA_continuousAt ζ
  have hBc := H.movedB_continuousAt ζ
  have hDc : ContinuousAt D 0 := by unfold D det2; fun_prop
  have hD0 : D 0=det2 H.v H.w := by simp [D,Hex.v,Hex.w]
  have eD : ∀ᶠ t in 𝓝 (0:ℝ), 0 < D t :=
    continuousAt_const.eventually_lt hDc (by rwa [hD0])
  have eA : ∀ᶠ t in 𝓝 (0:ℝ), 0 < 1+t*ζ H.slideA :=
    continuousAt_const.eventually_lt (by fun_prop) (by norm_num)
  have eB : ∀ᶠ t in 𝓝 (0:ℝ), 0 < 1+t*ζ H.slideB :=
    continuousAt_const.eventually_lt (by fun_prop) (by norm_num)
  have eQ : ∀ᶠ t in 𝓝 (0:ℝ), 0 < det2 H.a H.b*(ζ H.a+ζ H.b)+t*Q :=
    continuousAt_const.eventually_lt (by fun_prop)
      (by simpa using mul_pos (H.strict_first_det_pos hs hD) hz)
  have ea : ∀ᶠ t in 𝓝 (0:ℝ), |H.φ₂ (H.movedA ζ t)| < 1 :=
    ((H.φ₂.continuous_of_finiteDimensional.continuousAt.comp hAc).abs).eventually_lt
      continuousAt_const (by simpa using hs.1)
  have eb : ∀ᶠ t in 𝓝 (0:ℝ), |H.φ₃ (H.movedB ζ t)| < 1 :=
    ((H.φ₃.continuous_of_finiteDimensional.continuousAt.comp hBc).abs).eventually_lt
      continuousAt_const (by simpa using hs.2.1)
  have ec : ∀ᶠ t in 𝓝 (0:ℝ), |(H.φ₁+t • ζ) H.c| < 1 := by
    have hcc : ContinuousAt (fun t : ℝ => |(H.φ₁+t • ζ) H.c|) 0 := by
      simp only [LinearMap.add_apply,LinearMap.smul_apply,smul_eq_mul]; fun_prop
    exact hcc.eventually_lt continuousAt_const (by simpa using hs.2.2)
  have et : ∀ᶠ t in 𝓝 (0:ℝ), t*c < 1 :=
    (show ContinuousAt (fun t : ℝ => t*c) 0 from by fun_prop).eventually_lt
      continuousAt_const (by norm_num)
  have hall : ∀ᶠ t in 𝓝 (0:ℝ), 0 < D t ∧ 0 < 1+t*ζ H.slideA ∧
      0 < 1+t*ζ H.slideB ∧ 0 < det2 H.a H.b*(ζ H.a+ζ H.b)+t*Q ∧
      |H.φ₂ (H.movedA ζ t)| < 1 ∧ |H.φ₃ (H.movedB ζ t)| < 1 ∧
      |(H.φ₁+t • ζ) H.c| < 1 ∧ t*c < 1 := by
    filter_upwards [eD,eA,eB,eQ,ea,eb,ec,et] with t h1 h2 h3 h4 h5 h6 h7 h8
    exact ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩
  obtain ⟨t,ht,hd,hA,hB,hQ,ha,hb,hc',htc⟩ :=
    ((show ∀ᶠ t in 𝓝[>] (0:ℝ), 0 < t from self_mem_nhdsWithin).and
      (nhdsWithin_le_nhds hall)).exists
  obtain ⟨ha1,ha3,hb1,hb2⟩ := H.moved_incidence hs ζ t hA.ne' hB.ne'
  let G : Hex := {
    φ₁ := H.φ₁+t • ζ, φ₂ := H.φ₂, φ₃ := H.φ₃
    a := H.movedA ζ t, b := H.movedB ζ t, c := H.c
    ha₁ := ha1, ha₃ := ha3, hb₁ := hb1, hb₂ := hb2
    hc₂ := H.hc₂, hc₃ := H.hc₃
    hin_a := ha.le, hin_b := hb.le, hin_c := hc'.le, hdet := hd.ne' }
  refine ⟨G,?_,?_⟩
  · intro x hx
    obtain ⟨hx1,hx2,hx3⟩ := hKH hx
    refine ⟨?_,hx2,hx3⟩
    change |(H.φ₁+t • ζ) x| ≤ 1
    have he : (H.φ₁+t • ζ) x=(1-t*c)*H.φ₁ x+t*ψ x := by simp [ζ]; ring
    rw [he]
    calc
      |(1-t*c)*H.φ₁ x+t*ψ x| ≤ |(1-t*c)*H.φ₁ x|+|t*ψ x| := abs_add_le _ _
      _ = (1-t*c)*|H.φ₁ x|+t*|ψ x| := by
        rw [abs_mul,abs_mul,abs_of_pos ht,abs_of_pos (by linarith : 0 < 1-t*c)]
      _ ≤ (1-t*c)*1+t*c := add_le_add
        (mul_le_mul_of_nonneg_left hx1 (by linarith)) (mul_le_mul_of_nonneg_left (hψ x hx) ht.le)
      _ = 1 := by ring
  · rw [G.volume_eq_covolume,H.volume_eq_covolume]
    have hdec : D t < det2 H.v H.w := by
      have hh := H.moved_det_difference hs ζ t hA.ne' hB.ne'
      have hn : -t*(det2 H.a H.b*(ζ H.a+ζ H.b)+t*Q)/
          ((1+t*ζ H.slideA)*(1+t*ζ H.slideB)) < 0 :=
        div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (neg_neg_of_pos ht) hQ) (mul_pos hA hB)
      change D t-det2 H.v H.w = _ at hh
      change -t*(det2 H.a H.b*(ζ H.a+ζ H.b)+t*Q)/_ < 0 at hn
      linarith
    change ENNReal.ofReal |D t| < ENNReal.ofReal |det2 H.v H.w|
    rw [abs_of_pos hd,abs_of_pos hD]
    exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg hd.le |>.2 hdec

theorem first_midpoint_mem_of_strict_minimum (H : Hex) (hs : H.Strict)
    (hD : 0 < det2 H.v H.w) {K : Set E} (hK : IsSymmetricConvexDisc K)
    (hKH : K ⊆ H.set) (hmin : ∀ G : Hex, K ⊆ G.set → volume H.set ≤ volume G.set) :
    (1/2:ℝ) • (H.a+H.b) ∈ K := by
  by_contra hm
  obtain ⟨ψ,c,hψ,hc⟩ := geometric_hahn_banach_closed_point hK.1 hK.2.1.isClosed hm
  have hc0 : 0 < c := by
    simpa using hψ 0 (interior_subset (symmetricConvexDisc_zero_interior hK))
  have habs : ∀ x ∈ K, |ψ x| ≤ c := by
    intro x hx
    have hn := hψ (-x) ((hK.2.2.2 x).1 hx)
    rw [map_neg] at hn
    exact abs_le.2 ⟨by linarith, (hψ x hx).le⟩
  obtain ⟨G,hG,hlt⟩ := H.exists_smaller_of_separated_midpoint hs hD hKH ψ.toLinearMap c hc0 habs hc
  exact (not_lt_of_ge (hmin G hG)) hlt

#print axioms exists_smaller_of_separated_midpoint
#print axioms first_midpoint_mem_of_strict_minimum
end Hex
end Certificate.Packing
