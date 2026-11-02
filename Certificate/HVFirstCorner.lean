import Certificate.HVCornerCoordinates
import Certificate.HVAreaExpression

/-! The first actual HV corner contribution, obtained from minimum
circumscribed-hexagon area via an explicit invertible linear map. -/
namespace Certificate.Packing.HVGeometry
open MeasureTheory Set Pointwise
open Certificate.Confinement
set_option maxHeartbeats 0

lemma symmetric_linear_image {K : Set E} (hs : IsSymmetricSet K) (L : E →ₗ[ℝ] E) :
    IsSymmetricSet (L '' K) := by
  have h : ∀ x ∈ L '' K, -x ∈ L '' K := by
    rintro x ⟨y,hy,rfl⟩
    exact ⟨-y,(hs y).1 hy,by simp⟩
  intro x
  exact ⟨h x,fun hx => by simpa using h (-x) hx⟩

/-- A contact triangle in the first corner, including the case where the
published maximum contributes zero. This uses genuine area minimality. -/
theorem first_corner_contact (K : Set E) (hcomp : IsCompact K) (hconv : Convex ℝ K)
    (hsym : IsSymmetricSet K) (u v w : ℝ)
    (hu : 0 < u) (hv : 0 < v) (hw : 0 < w) (he2 : u*v+v*w+w*u=1)
    (hside : ∀ x ∈ K, |sideA u v w x| ≤ 1 ∧ |sideC u v w x| ≤ 1)
    (h0 : s0 ∈ K) (h1 : s1 ∈ K) (hmin : HexAreaLowerBound K (2*Real.sqrt 3)) :
    ∃ r ∈ K, r ∈ triangle s0 (p0 u v w) s1 ∧
      triangleArea s0 r s1 = Real.sqrt 3/4*areaTerm v u w := by
  have hprod : 0 < u*w := mul_pos hu hw
  have hsqrt : 0 < Real.sqrt (u*w) := Real.sqrt_pos.2 hprod
  have hsqrt2 : (Real.sqrt (u*w))^2 = u*w := Real.sq_sqrt hprod.le
  by_cases hactive : 4*v^2 ≤ u*w
  · let L := cornerEquiv u v w hu hv hw he2
    let d := w/(v+w)
    let e := u/(u+v)
    let t := 2*v/Real.sqrt (u*w)
    have hd : 0 < d := div_pos hw (add_pos hv hw)
    have he : 0 < e := div_pos hu (add_pos hu hv)
    have hd1 : d ≤ 1 := (div_le_one (add_pos hv hw)).2 (by linarith)
    have he1 : e ≤ 1 := (div_le_one (add_pos hu hv)).2 (by linarith)
    have ht : 0 ≤ t := by dsimp [t]; positivity
    have ht1 : t ≤ 1 := by
      apply (div_le_one hsqrt).2
      nlinarith
    have hL0 : L s0 = point (1-d) (-1) := (cornerMap_midpoints u v w hu hv hw).1
    have hL1 : L s1 = point 1 (-1+e) := (cornerMap_midpoints u v w hu hv hw).2
    have hLp : L (p0 u v w) = point 1 (-1) := cornerMap_vertex u v w hu hv hw he2
    have hvol : |LinearMap.det (L : E →ₗ[ℝ] E)| *(2*Real.sqrt 3) = 4-t^2*d*e := by
      change |LinearMap.det (cornerMap u v w)| *(2*Real.sqrt 3) = _
      rw [cornerMap_area_normalization u v w hu hv hw he2]
      dsimp [t,d,e]
      have hα : u+v ≠ 0 := ne_of_gt (add_pos hu hv)
      have hβ : v+w ≠ 0 := ne_of_gt (add_pos hv hw)
      field_simp
      nlinarith
    have hminL : HexAreaLowerBound (L '' K) (4-t^2*d*e) := by
      rw [← hvol]
      exact hmin.linear_image L
    have hsqL : ∀ x ∈ L '' K, |x 0| ≤ 1 ∧ |x 1| ≤ 1 := by
      rintro x ⟨y,hy,rfl⟩
      exact hside y hy
    obtain ⟨x,hx,hcorner,hlevel,htri,harea⟩ := hales_vajjha_corner_contribution
      (hcomp.image L.toContinuousLinearEquiv.continuous) (hconv.linear_image (L : E →ₗ[ℝ] E))
      (symmetric_linear_image hsym (L : E →ₗ[ℝ] E)) hsqL hd he hd1 he1 ht ht1
      (by rw [← hL0]; exact ⟨_,h0,rfl⟩) (by rw [← hL1]; exact ⟨_,h1,rfl⟩) hminL
    obtain ⟨r,hrK,hr⟩ := hx
    change L r = x at hr
    refine ⟨r,hrK,?_,?_⟩
    · rw [cornerTriangle_eq_triangle,← hL0,← hLp,← hL1] at hcorner
      have himg : L '' triangle s0 (p0 u v w) s1 = triangle (L s0) (L (p0 u v w)) (L s1) :=
        triangle_linearMap_image (L : E →ₗ[ℝ] E) s0 (p0 u v w) s1
      rw [← himg] at hcorner
      obtain ⟨y,hy,hyx⟩ := hcorner
      have hyr : y=r := L.injective (hyx.trans hr.symm)
      simpa [hyr] using hy
    · have hmax : areaTerm v u w = u*w-2*v*Real.sqrt (u*w) := by
        unfold areaTerm
        apply max_eq_right
        have hvroot : 2*v ≤ Real.sqrt (u*w) := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_right hvroot hsqrt.le]
      rw [hmax]
      apply (mul_right_inj' (abs_ne_zero.2 (linearEquiv_det_ne_zero L))).1
      rw [← triangleArea_linearMap (L : E →ₗ[ℝ] E) s0 r s1]
      change triangleArea (L s0) (L r) (L s1) = _
      rw [hL0,hL1,hr,triangleArea_swap]
      rw [corner_triangle_area_of_level hd he ht1 hlevel]
      change (1-t)*d*e/2 = |LinearMap.det (cornerMap u v w)| * _
      rw [abs_of_pos (cornerMap_det_pos u v w hu hv hw he2),cornerMap_det u v w hu hv hw he2]
      dsimp [t,d,e]
      have hs : Real.sqrt (3:ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
      have hα : u+v ≠ 0 := ne_of_gt (add_pos hu hv)
      have hβ : v+w ≠ 0 := ne_of_gt (add_pos hv hw)
      field_simp
      nlinarith
  · refine ⟨s0,h0,mem_triangle_first _ _ _,?_⟩
    have hmax : areaTerm v u w = 0 := by
      unfold areaTerm
      apply max_eq_left
      have hvroot : Real.sqrt (u*w) ≤ 2*v := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hvroot hsqrt.le]
    rw [hmax,mul_zero,triangleArea_eq_det]
    simp [det2]

#print axioms first_corner_contact
end Certificate.Packing.HVGeometry
