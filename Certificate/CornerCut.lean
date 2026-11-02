import Certificate.PackingHexagon

/-! The hexagon replacement in Hales–Vajjha, Theorem 5.0.6.
A corner cut of the square gives an actual `Hex`, with explicitly computed
lattice covolume. Minimality among circumscribed hexagons then forces contact.
No minimality or contact statement is added as an axiom. -/
namespace Certificate.Packing
open Set Pointwise
set_option maxHeartbeats 0

noncomputable def point (x y : ℝ) : E := WithLp.toLp 2 ![x,y]
@[simp] lemma point_zero (x y : ℝ) : point x y 0 = x := rfl
@[simp] lemma point_one (x y : ℝ) : point x y 1 = y := rfl

def coord (i : Fin 2) : E →ₗ[ℝ] ℝ where
  toFun x := x i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def cutForm (d e : ℝ) : E →ₗ[ℝ] ℝ :=
  (d + e - d*e)⁻¹ • (d • coord 1 - e • coord 0)

@[simp] lemma cutForm_apply (d e : ℝ) (x : E) :
    cutForm d e x = (d*x 1 - e*x 0)/(d+e-d*e) := by
  change (d+e-d*e)⁻¹ * (d*x 1-e*x 0) = _
  ring

lemma cut_denom_pos {d e : ℝ} (hd : 0 < d) (he : 0 < e) (he1 : e ≤ 1) :
    0 < d+e-d*e := by nlinarith [mul_nonneg hd.le (sub_nonneg.mpr he1)]

/-- The square with the opposite corners `(1,-1)` and `(-1,1)` cut off.
The removed triangles have leg lengths `d,e`. -/
noncomputable def cutHex (d e : ℝ) (hd : 0 < d) (he : 0 < e)
    (hd1 : d ≤ 1) (he1 : e ≤ 1) : Hex where
  φ₁ := coord 0
  φ₂ := coord 1
  φ₃ := cutForm d e
  a := point 1 (-1+e)
  b := point 1 1
  c := point (-1+d) 1
  ha₁ := rfl
  hb₁ := rfl
  hb₂ := rfl
  hc₂ := rfl
  ha₃ := by
    simp only [cutForm_apply, point_zero, point_one]
    apply (div_eq_iff (ne_of_gt (cut_denom_pos hd he he1))).2
    ring
  hc₃ := by
    simp only [cutForm_apply, point_zero, point_one]
    apply (div_eq_iff (ne_of_gt (cut_denom_pos hd he he1))).2
    ring
  hin_a := by change |-1+e| ≤ 1; rw [abs_le]; constructor <;> linarith
  hin_c := by change |-1+d| ≤ 1; rw [abs_le]; constructor <;> linarith
  hin_b := by
    simp only [cutForm_apply, point_zero, point_one, mul_one]
    rw [abs_le, le_div_iff₀ (cut_denom_pos hd he he1), div_le_iff₀ (cut_denom_pos hd he he1)]
    constructor
    · nlinarith [mul_nonneg hd.le (sub_nonneg.mpr he1)]
    · nlinarith [mul_nonneg he.le (sub_nonneg.mpr hd1)]
  hdet := by
    change det2 (point 1 (-1+e) + point 1 1) (point 1 1 + point (-1+d) 1) ≠ 0
    simp only [det2, PiLp.add_apply, point_zero, point_one]
    have : d*e ≤ 1 := mul_le_one₀ hd1 he.le he1
    nlinarith

lemma cutHex_covolume {d e : ℝ} (hd : 0 < d) (he : 0 < e)
    (hd1 : d ≤ 1) (he1 : e ≤ 1) :
    |det2 (cutHex d e hd he hd1 he1).v (cutHex d e hd he hd1 he1).w| = 4-d*e := by
  have h : det2 (cutHex d e hd he hd1 he1).v (cutHex d e hd he hd1 he1).w = 4-d*e := by
    simp [Hex.v, Hex.w, cutHex, det2, point]; ring
  rw [h, abs_of_pos]
  have : d*e ≤ 1 := mul_le_one₀ hd1 he.le he1
  linarith

/-- The value `A` is a lower bound on the covolume of every enclosing hexagon.
This is the geometric minimality hypothesis, independent of any density bound. -/
def HexCovolumeLowerBound (K : Set E) (A : ℝ) : Prop :=
  ∀ H : Hex, K ⊆ H.set → A ≤ |det2 H.v H.w|

noncomputable def cornerDistance (d e : ℝ) (x : E) : ℝ :=
  (1-x 0)/d + (x 1+1)/e

lemma cornerDistance_ge_iff {d e k : ℝ} (hd : 0 < d) (he : 0 < e) (x : E) :
    k ≤ cornerDistance d e x ↔ e*x 0-d*x 1 ≤ d+e-k*d*e := by
  unfold cornerDistance
  rw [div_add_div _ _ hd.ne' he.ne', le_div_iff₀ (mul_pos hd he)]
  constructor <;> intro h <;> nlinarith

lemma subset_cutHex_of_cornerDistance {K : Set E} {d e k : ℝ}
    (hd : 0 < d) (he : 0 < e) (hd1 : d ≤ 1) (he1 : e ≤ 1)
    (hk : 0 < k) (hk1 : k ≤ 1)
    (hsq : ∀ x ∈ K, |x 0| ≤ 1 ∧ |x 1| ≤ 1)
    (hsym : IsSymmetricSet K)
    (hcut : ∀ x ∈ K, k ≤ cornerDistance d e x) :
    K ⊆ (cutHex (k*d) (k*e) (mul_pos hk hd) (mul_pos hk he)
      (mul_le_one₀ hk1 hd.le hd1) (mul_le_one₀ hk1 he.le he1)).set := by
  intro x hx
  refine ⟨(hsq x hx).1, (hsq x hx).2, ?_⟩
  change |cutForm (k*d) (k*e) x| ≤ 1
  have hplus := (cornerDistance_ge_iff hd he x).1 (hcut x hx)
  have hminus := (cornerDistance_ge_iff hd he (-x)).1 (hcut (-x) ((hsym x).1 hx))
  simp only [PiLp.neg_apply] at hminus
  have hp := mul_le_mul_of_nonneg_left hplus hk.le
  have hn := mul_le_mul_of_nonneg_left hminus hk.le
  rw [cutForm_apply, abs_le,
    le_div_iff₀ (cut_denom_pos (mul_pos hk hd) (mul_pos hk he) (mul_le_one₀ hk1 he.le he1)),
    div_le_iff₀ (cut_denom_pos (mul_pos hk hd) (mul_pos hk he) (mul_le_one₀ hk1 he.le he1))]
  constructor <;> nlinarith

/-- A minimal enclosing hexagon cannot leave an entire corner cut outside the body.
This is the compactness/competitor step of HV 5.0.6, in square coordinates.
`d,e` are the distances from the corner to the two adjacent side midpoints. -/
theorem exists_cornerDistance_le {K : Set E} {d e t : ℝ}
    (hcomp : IsCompact K) (hne : K.Nonempty) (hsym : IsSymmetricSet K)
    (hsq : ∀ x ∈ K, |x 0| ≤ 1 ∧ |x 1| ≤ 1)
    (hd : 0 < d) (he : 0 < e) (hd1 : d ≤ 1) (he1 : e ≤ 1)
    (ht : 0 ≤ t) (ht1 : t < 1)
    (hmin : HexCovolumeLowerBound K (4-t^2*d*e)) :
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
  have hb := hmin H hKH
  rw [cutHex_covolume] at hb
  have hsqk : t^2 < k^2 := sq_lt_sq₀ ht hk0.le |>.2 htk
  have hprod := mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_right hsqk hd) he
  nlinarith

lemma cornerDistance_combination {d e a b : ℝ} (hd : d ≠ 0) (he : e ≠ 0)
    (hab : a+b=1) (x y : E) :
    cornerDistance d e (a • x+b • y) = a*cornerDistance d e x+b*cornerDistance d e y := by
  unfold cornerDistance
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  field_simp
  linear_combination -(d+e)*hab

/-- Convexity turns the forced point into contact with the precise parallel cut. -/
theorem exists_cornerDistance_eq {K : Set E} {d e t : ℝ}
    (hcomp : IsCompact K) (hconv : Convex ℝ K) (hsym : IsSymmetricSet K)
    (hsq : ∀ x ∈ K, |x 0| ≤ 1 ∧ |x 1| ≤ 1)
    (hd : 0 < d) (he : 0 < e) (hd1 : d ≤ 1) (he1 : e ≤ 1)
    (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hside : point 1 (-1+e) ∈ K)
    (hmin : HexCovolumeLowerBound K (4-t^2*d*e)) :
    ∃ x ∈ K, cornerDistance d e x = t := by
  have hs : cornerDistance d e (point 1 (-1+e)) = 1 := by
    simp [cornerDistance, he.ne']
  rcases ht1.eq_or_lt with h | h
  · exact ⟨_,hside,hs.trans h.symm⟩
  obtain ⟨z,hz,hzt⟩ := exists_cornerDistance_le hcomp ⟨_,hside⟩ hsym hsq
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

end Certificate.Packing
