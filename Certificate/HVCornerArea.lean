import Certificate.CutHexagonArea
import Certificate.ParallelCutArea

/-! The single-corner contact and area contribution used in HV Theorem 5.0.6.
The hypothesis now minimizes actual geometric area, not lattice covolume.
This module does not assert existence of a critical hexagon or a balanced body. -/
namespace Certificate.Packing
open MeasureTheory Set Pointwise
set_option maxHeartbeats 0

/-- A lower bound on the actual area of every circumscribed symmetric hexagon. -/
def HexAreaLowerBound (K : Set E) (A : ℝ) : Prop :=
  ∀ H : Hex, K ⊆ H.set → ENNReal.ofReal A ≤ volume H.set

theorem exists_cornerDistance_le_of_area_minimal {K : Set E} {d e t : ℝ}
    (hcomp : IsCompact K) (hne : K.Nonempty) (hsym : IsSymmetricSet K)
    (hsq : ∀ x ∈ K, |x 0| ≤ 1 ∧ |x 1| ≤ 1)
    (hd : 0 < d) (he : 0 < e) (hd1 : d ≤ 1) (he1 : e ≤ 1)
    (ht : 0 ≤ t) (ht1 : t < 1)
    (hmin : HexAreaLowerBound K (4-t^2*d*e)) :
    ∃ x ∈ K, cornerDistance d e x ≤ t := by
  obtain ⟨z,hz,hm⟩ := hcomp.exists_isMinOn hne
    (show ContinuousOn (cornerDistance d e) K from (by unfold cornerDistance; fun_prop))
  by_contra h
  push Not at h
  have htz := h z hz
  obtain ⟨k, htk, hk⟩ := exists_between (lt_min ht1 htz)
  have hk1 : k ≤ 1 := (lt_of_lt_of_le hk (min_le_left _ _)).le
  have hkz : k ≤ cornerDistance d e z := (lt_of_lt_of_le hk (min_le_right _ _)).le
  have hk0 : 0 < k := lt_of_le_of_lt ht htk
  let H := cutHex (k*d) (k*e) (mul_pos hk0 hd) (mul_pos hk0 he)
    (mul_le_one₀ hk1 hd.le hd1) (mul_le_one₀ hk1 he.le he1)
  have hKH : K ⊆ H.set := subset_cutHex_of_cornerDistance hd he hd1 he1 hk0 hk1 hsq hsym
    (fun x hx => hkz.trans (hm hx))
  have hHsq : H.set ⊆ square := fun x hx => ⟨hx.1,hx.2.1⟩
  have hHfin : volume H.set ≠ ⊤ := ((measure_mono hHsq).trans_lt
    isCompact_square.measure_lt_top).ne
  have hb := (ENNReal.ofReal_le_iff_le_toReal hHfin).1 (hmin H hKH)
  rw [volume_cutHex] at hb
  have hsqk : t^2 < k^2 := sq_lt_sq₀ ht hk0.le |>.2 htk
  have hprod := mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_right hsqk hd) he
  nlinarith

theorem exists_cornerDistance_eq_of_area_minimal {K : Set E} {d e t : ℝ}
    (hcomp : IsCompact K) (hconv : Convex ℝ K) (hsym : IsSymmetricSet K)
    (hsq : ∀ x ∈ K, |x 0| ≤ 1 ∧ |x 1| ≤ 1)
    (hd : 0 < d) (he : 0 < e) (hd1 : d ≤ 1) (he1 : e ≤ 1)
    (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hside : point 1 (-1+e) ∈ K)
    (hmin : HexAreaLowerBound K (4-t^2*d*e)) :
    ∃ x ∈ K, cornerDistance d e x = t := by
  have hs : cornerDistance d e (point 1 (-1+e)) = 1 := by
    simp [cornerDistance, he.ne']
  rcases ht1.eq_or_lt with h | h
  · exact ⟨_,hside,hs.trans h.symm⟩
  obtain ⟨z,hz,hzt⟩ := exists_cornerDistance_le_of_area_minimal hcomp ⟨_,hside⟩ hsym hsq
    hd he hd1 he1 ht h hmin
  let a := (1-t)/(1-cornerDistance d e z)
  have hz1 : 0 < 1-cornerDistance d e z := by linarith
  have ha0 : 0 ≤ a := div_nonneg (by linarith) hz1.le
  have ha1 : a ≤ 1 := (div_le_one hz1).2 (by linarith)
  refine ⟨a • z+(1-a) • point 1 (-1+e), hconv hz hside ha0 (by linarith) (by ring), ?_⟩
  rw [cornerDistance_combination hd.ne' he.ne' (by ring), hs]
  dsimp [a]
  field_simp
  ring

lemma corner_triangle_area_of_level {d e t : ℝ} (hd : 0 < d) (he : 0 < e)
    (ht1 : t ≤ 1) {x : E} (hx : cornerDistance d e x = t) :
    triangleArea (point (1-d) (-1)) (point 1 (-1+e)) x = (1-t)*d*e/2 := by
  have hp : e*x 0-d*x 1 = d+e-t*d*e := by
    unfold cornerDistance at hx
    rw [div_add_div _ _ hd.ne' he.ne', div_eq_iff (mul_pos hd he).ne'] at hx
    nlinarith
  have hdet : det2 (point 1 (-1+e)-point (1-d) (-1)) (x-point (1-d) (-1)) =
      -(1-t)*d*e := by
    simp only [det2, PiLp.sub_apply, point_zero, point_one]
    nlinarith
  rw [triangleArea_eq_det, hdet]
  have hh : 0 ≤ (1-t)*d*e := mul_nonneg (mul_nonneg (sub_nonneg.mpr ht1) hd.le) he.le
  rw [show -(1-t)*d*e = -((1-t)*d*e) by ring, abs_neg, abs_of_nonneg hh]

/-- The extra triangle in one corner, derived from geometric minimality.
The two fixed vertices are the adjacent side midpoints; the third belongs to K.
Its area is the interior-corner area minus the square-root penalty appearing
in the published lower bound. Both areas in the square root are geometric. -/
theorem hales_vajjha_corner_contribution {K : Set E} {d e t : ℝ}
    (hcomp : IsCompact K) (hconv : Convex ℝ K) (hsym : IsSymmetricSet K)
    (hsq : ∀ x ∈ K, |x 0| ≤ 1 ∧ |x 1| ≤ 1)
    (hd : 0 < d) (he : 0 < e) (hd1 : d ≤ 1) (he1 : e ≤ 1)
    (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hp : point (1-d) (-1) ∈ K) (hq : point 1 (-1+e) ∈ K)
    (hmin : HexAreaLowerBound K (4-t^2*d*e)) :
    ∃ x ∈ K, x ∈ cornerTriangle d e ∧ cornerDistance d e x = t ∧
      point (1-d) (-1) +ᵥ Tri (point 1 (-1+e)-point (1-d) (-1))
        (x-point (1-d) (-1)) ⊆ K ∧
      triangleArea (point (1-d) (-1)) (point 1 (-1+e)) x =
        d*e/2-Real.sqrt ((t^2*d*e/2)*(d*e/2)) := by
  obtain ⟨x,hx,hlevel⟩ := exists_cornerDistance_eq_of_area_minimal hcomp hconv hsym hsq
    hd he hd1 he1 ht ht1 hq hmin
  have hcorner : x ∈ cornerTriangle d e := (mem_cornerTriangle_iff hd he x).2
    ⟨(abs_le.1 (hsq x hx).1).2,(abs_le.1 (hsq x hx).2).1,hlevel.le.trans ht1⟩
  refine ⟨x,hx,hcorner,hlevel,Tri_subset_of_mem K hconv hp hq hx,?_⟩
  rw [corner_triangle_area_of_level hd he ht1 hlevel]
  rw [show (t^2*d*e/2)*(d*e/2) = (t*(d*e/2))^2 by ring,
    Real.sqrt_sq (mul_nonneg ht (by positivity))]
  ring

#print axioms exists_cornerDistance_eq_of_area_minimal
#print axioms hales_vajjha_corner_contribution
end Certificate.Packing
