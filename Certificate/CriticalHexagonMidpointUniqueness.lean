import Certificate.MinimizerMidpointTangents

/-! Two critical hexagons with a common first midpoint and the same oriented
area have the same midpoint configuration. Positivity of the neighboring
support form rules out displacement along the common midpoint direction. -/
namespace Certificate.Packing
open Set MeasureTheory
set_option maxHeartbeats 0
namespace Hex

lemma second_normal_first_midpoint_pos (H : Hex) (hs : H.Strict) :
    0 < H.φ₂ (H.midpoint 0) := by
  have ha := (abs_lt.1 hs.1).1
  simp [midpoint,map_add,map_smul,H.hb₂]
  linarith

lemma midpoint_two_eq (H : Hex) : H.midpoint 2=H.midpoint 1-H.midpoint 0 := by
  simp [midpoint]; module

theorem second_midpoint_eq_of_first (H G : Hex) (hs : H.Strict) (gs : G.Strict)
    {K : Set E} (hH : K ⊆ H.set) (hG : K ⊆ G.set)
    (hmH : H.midpoint 1 ∈ K) (hmG : G.midpoint 1 ∈ K)
    (hp : H.midpoint 0=G.midpoint 0) (hD : det2 H.v H.w=det2 G.v G.w) :
    H.midpoint 1=G.midpoint 1 := by
  let P := H.midpoint 0
  let Q := H.midpoint 1
  let R := G.midpoint 1
  have hn : det2 P Q ≠ 0 := H.midpoint_det_ne_zero
  let z := (pairFrame P Q hn).symm R
  have hr : R=z 0 • P+z 1 • Q := ((pairFrame P Q hn).apply_symm_apply R).symm
  have he : det2 P R=det2 P Q := by
    change det2 (H.midpoint 0) (G.midpoint 1)=det2 (H.midpoint 0) (H.midpoint 1)
    rw [hp,G.midpoint_det,← hp,H.midpoint_det,hD]
  have he' : det2 P R=z 1*det2 P Q := by rw [hr]; simp [det2]; ring
  have hz1 : z 1=1 := by
    have hh : (z 1-1)*det2 P Q=0 := by nlinarith [he,he']
    exact sub_eq_zero.1 ((mul_eq_zero.1 hh).resolve_right hn)
  have hr' : R=z 0 • P+Q := by simpa [hz1] using hr
  have hHP : 0 < H.φ₂ P := H.second_normal_first_midpoint_pos hs
  have hGP : 0 < G.φ₂ P := by
    change 0 < G.φ₂ (H.midpoint 0)
    rw [hp]
    exact G.second_normal_first_midpoint_pos gs
  have hHQ : H.φ₂ Q=1 := H.sideNormal_midpoint 1
  have hGR : G.φ₂ R=1 := G.sideNormal_midpoint 1
  have hHR : H.φ₂ R ≤ 1 := (le_abs_self _).trans (hH hmG).2.1
  have hGQ : G.φ₂ Q ≤ 1 := (le_abs_self _).trans (hG hmH).2.1
  have hrelH := congrArg H.φ₂ hr'
  have hrelG := congrArg G.φ₂ hr'
  simp only [map_add,map_smul,smul_eq_mul,hHQ] at hrelH
  simp only [map_add,map_smul,smul_eq_mul,hGR] at hrelG
  have hz0 : z 0=0 := by nlinarith
  simpa [hz0] using hr'.symm

lemma midpoints_eq_of_first_two (H G : Hex)
    (h0 : H.midpoint 0=G.midpoint 0) (h1 : H.midpoint 1=G.midpoint 1) :
    ∀ i : Fin 6, H.midpoint i=G.midpoint i := by
  have h2 : H.midpoint 2=G.midpoint 2 := by rw [midpoint_two_eq,midpoint_two_eq,h0,h1]
  intro i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · change -(1/2:ℝ) • (H.a+H.b)= -(1/2:ℝ) • (G.a+G.b)
    rw [neg_smul,neg_smul]
    exact congrArg Neg.neg h0
  · change -(1/2:ℝ) • (H.b+H.c)= -(1/2:ℝ) • (G.b+G.c)
    rw [neg_smul,neg_smul]
    exact congrArg Neg.neg h1
  · change -(1/2:ℝ) • (H.c-H.a)= -(1/2:ℝ) • (G.c-G.a)
    rw [neg_smul,neg_smul]
    exact congrArg Neg.neg h2

theorem set_eq_of_critical_first_midpoint (H G : Hex) (hs : H.Strict) (gs : G.Strict)
    {K : Set E} (hH : K ⊆ H.set) (hG : K ⊆ G.set)
    (hmin : ∀ F : Hex, K ⊆ F.set → volume H.set ≤ volume F.set)
    (hmH : H.midpoint 1 ∈ K) (hmG : G.midpoint 1 ∈ K)
    (hp : H.midpoint 0=G.midpoint 0) (hD : det2 H.v H.w=det2 G.v G.w) : H.set=G.set := by
  have h1 := H.second_midpoint_eq_of_first G hs gs hH hG hmH hmG hp hD
  have hm := H.midpoints_eq_of_first_two G hp h1
  have hn (i : Fin 6) : G.sideNormal i=H.sideNormal i :=
    H.support_unique_at_midpoint hs hH hmin i (G.sideNormal i)
      (fun x hx => G.sideNormal_abs_le i (hG hx)) (by rw [hm]; exact G.sideNormal_midpoint i)
  have hφ1 : G.φ₁=H.φ₁ := hn 0
  have hφ2 : G.φ₂=H.φ₂ := hn 1
  have hφ3 : G.φ₃=H.φ₃ := hn 2
  ext x
  simp [Hex.set,hφ1,hφ2,hφ3]

#print axioms second_midpoint_eq_of_first
#print axioms set_eq_of_critical_first_midpoint
end Hex
end Certificate.Packing
