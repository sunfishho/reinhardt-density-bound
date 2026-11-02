import Certificate.HexagonLinearTransport

/-! Explicit square coordinates at the first corner of a normalized
midpoint hexagon. No optimization is performed in these proofs. -/
namespace Certificate.Packing.HVGeometry
open MeasureTheory Set Pointwise
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false

noncomputable def sideA (u v w : ℝ) : E →ₗ[ℝ] ℝ :=
  (v/(v+w)) • coord 0 + ((v+2*w)/(Real.sqrt 3*(v+w))) • coord 1
noncomputable def sideB (u v w : ℝ) : E →ₗ[ℝ] ℝ :=
  (-u/(u+w)) • coord 0 + ((u+2*w)/(Real.sqrt 3*(u+w))) • coord 1
noncomputable def sideC (u v w : ℝ) : E →ₗ[ℝ] ℝ :=
  -coord 0 + ((u-v)/(Real.sqrt 3*(u+v))) • coord 1

noncomputable def pairLinear (f g : E →ₗ[ℝ] ℝ) : E →ₗ[ℝ] E where
  toFun x := point (f x) (g x)
  map_add' x y := by ext i; fin_cases i <;> simp [point]
  map_smul' c x := by ext i; fin_cases i <;> simp [point]

noncomputable def cornerMap (u v w : ℝ) : E →ₗ[ℝ] E :=
  pairLinear (sideA u v w) (sideC u v w)

lemma cornerMap_det (u v w : ℝ) (hu : 0 < u) (hv : 0 < v) (hw : 0 < w)
    (he2 : u*v+v*w+w*u=1) :
    LinearMap.det (cornerMap u v w) = 2/(Real.sqrt 3*(u+v)*(v+w)) := by
  have hs : Real.sqrt (3:ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hα : u+v ≠ 0 := ne_of_gt (add_pos hu hv)
  have hβ : v+w ≠ 0 := ne_of_gt (add_pos hv hw)
  rw [det_eq_det2]
  simp [cornerMap,pairLinear,sideA,sideC,point,det2]
  field_simp
  nlinarith

lemma cornerMap_det_pos (u v w : ℝ) (hu : 0 < u) (hv : 0 < v) (hw : 0 < w)
    (he2 : u*v+v*w+w*u=1) : 0 < LinearMap.det (cornerMap u v w) := by
  rw [cornerMap_det u v w hu hv hw he2]
  positivity

noncomputable def cornerEquiv (u v w : ℝ) (hu : 0 < u) (hv : 0 < v) (hw : 0 < w)
    (he2 : u*v+v*w+w*u=1) : E ≃ₗ[ℝ] E :=
  (cornerMap u v w).equivOfDetNeZero (cornerMap_det_pos u v w hu hv hw he2).ne'

@[simp] lemma cornerEquiv_apply (u v w : ℝ) (hu : 0 < u) (hv : 0 < v) (hw : 0 < w)
    (he2 : u*v+v*w+w*u=1) (x : E) :
    cornerEquiv u v w hu hv hw he2 x = cornerMap u v w x := rfl

lemma cornerMap_midpoints (u v w : ℝ) (hu : 0 < u) (hv : 0 < v) (hw : 0 < w) :
    cornerMap u v w s0 = point (1-w/(v+w)) (-1) ∧
    cornerMap u v w s1 = point 1 (-1+u/(u+v)) := by
  have hs : Real.sqrt (3:ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hα : u+v ≠ 0 := ne_of_gt (add_pos hu hv)
  have hβ : v+w ≠ 0 := ne_of_gt (add_pos hv hw)
  constructor <;> ext i <;> fin_cases i <;>
    simp [cornerMap,pairLinear,sideA,sideC,s0,s1,pt,point] <;>
    field_simp <;> ring

lemma cornerMap_vertex (u v w : ℝ) (hu : 0 < u) (hv : 0 < v) (hw : 0 < w)
    (he2 : u*v+v*w+w*u=1) : cornerMap u v w (p0 u v w) = point 1 (-1) := by
  have hs : Real.sqrt (3:ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hα : u+v ≠ 0 := ne_of_gt (add_pos hu hv)
  have hβ : v+w ≠ 0 := ne_of_gt (add_pos hv hw)
  ext i; fin_cases i <;> simp [cornerMap,pairLinear,sideA,sideC,p0,pt,point]
  · field_simp
    linear_combination 2*w*he2
  · field_simp
    ring

lemma cornerMap_area_normalization (u v w : ℝ) (hu : 0 < u) (hv : 0 < v) (hw : 0 < w)
    (he2 : u*v+v*w+w*u=1) :
    |LinearMap.det (cornerMap u v w)| *(2*Real.sqrt 3) =
      4-4*v^2/((u+v)*(v+w)) := by
  have hs : Real.sqrt (3:ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hα : u+v ≠ 0 := ne_of_gt (add_pos hu hv)
  have hβ : v+w ≠ 0 := ne_of_gt (add_pos hv hw)
  rw [abs_of_pos (cornerMap_det_pos u v w hu hv hw he2),cornerMap_det u v w hu hv hw he2]
  field_simp
  nlinarith

#print axioms cornerMap_det
#print axioms cornerMap_vertex
#print axioms cornerMap_area_normalization
end Certificate.Packing.HVGeometry
