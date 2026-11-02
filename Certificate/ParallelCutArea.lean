import Certificate.TriangleArea

/-! Hales–Vajjha, Lemma 5.0.5: the area supplied by a point on a cut parallel
to the base of a triangle. Areas below are actual Lebesgue measures in the
Euclidean plane, not a separate axiomatized notion of polygon area. -/
namespace Certificate.Packing
open MeasureTheory Set Pointwise
set_option maxHeartbeats 0

noncomputable def triangleArea (p q r : E) : ℝ :=
  (volume (p +ᵥ Tri (q-p) (r-p))).toReal

lemma triangleArea_eq_det (p q r : E) :
    triangleArea p q r = |det2 (q-p) (r-p)|/2 := volume_triangle p q r

lemma triangleArea_nonneg (p q r : E) : 0 ≤ triangleArea p q r := ENNReal.toReal_nonneg

/-- Scaling both sides of a triangle from its corner scales area by the square. -/
theorem triangleArea_homothety (p q c : E) (t : ℝ) :
    triangleArea c ((1-t) • c+t • p) ((1-t) • c+t • q) =
      t^2 * triangleArea c p q := by
  have hdet : det2 ((1-t) • c+t • p-c) ((1-t) • c+t • q-c) =
      t^2 * det2 (p-c) (q-c) := by
    simp only [det2, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  rw [triangleArea_eq_det, triangleArea_eq_det, hdet, abs_mul, abs_of_nonneg (sq_nonneg t)]
  ring

/-- A point anywhere on the parallel cut contributes the same base-triangle area. -/
theorem triangleArea_parallel_cut (p q c : E) (a t : ℝ) (ht : t ≤ 1) :
    triangleArea p q ((1-t) • c+t • (a • p+(1-a) • q)) =
      (1-t)*triangleArea c p q := by
  have hdet : det2 (q-p) ((1-t) • c+t • (a • p+(1-a) • q)-p) =
      (1-t)*det2 (p-c) (q-c) := by
    simp only [det2, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  rw [triangleArea_eq_det, triangleArea_eq_det, hdet, abs_mul,
    abs_of_nonneg (sub_nonneg.mpr ht)]
  ring

/-- The square-root formula in the published parallel-cut lemma, proved with
Lebesgue areas. Here `t` is the fraction of each side retained near the corner. -/
theorem hales_vajjha_parallel_cut_area (p q c : E) (a t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    triangleArea p q ((1-t) • c+t • (a • p+(1-a) • q)) =
      triangleArea c p q - Real.sqrt
        (triangleArea c ((1-t) • c+t • p) ((1-t) • c+t • q) * triangleArea c p q) := by
  rw [triangleArea_parallel_cut p q c a t ht1, triangleArea_homothety]
  have hs : t^2*triangleArea c p q*triangleArea c p q = (t*triangleArea c p q)^2 := by ring
  rw [hs, Real.sqrt_sq (mul_nonneg ht0 (triangleArea_nonneg c p q))]
  ring

#print axioms hales_vajjha_parallel_cut_area
end Certificate.Packing
