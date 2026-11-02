import Certificate.HVCornerArea
import Certificate.AreaAssemblyHelpers

/-! Linear-coordinate transport of circumscribed hexagons, area minimality,
and corner contributions. This does not posit any minimizing body. -/
namespace Certificate.Packing
open MeasureTheory Set Pointwise
set_option maxHeartbeats 0

lemma det_eq_det2 (f : E →ₗ[ℝ] E) :
    LinearMap.det f = det2 (f (point 1 0)) (f (point 0 1)) := by
  rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis,Matrix.det_fin_two]
  have h0 : (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis 0 = point 1 0 := by
    ext i; fin_cases i <;> simp [EuclideanSpace.basisFun_apply,point]
  have h1 : (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis 1 = point 0 1 := by
    ext i; fin_cases i <;> simp [EuclideanSpace.basisFun_apply,point]
  simp only [LinearMap.toMatrix_apply,OrthonormalBasis.coe_toBasis_repr_apply,
    EuclideanSpace.basisFun_repr,h0,h1,det2]
  ring

lemma linearMap_coordinates (f : E →ₗ[ℝ] E) (x : E) :
    f x = x 0 • f (point 1 0) + x 1 • f (point 0 1) := by
  have hx : x = x 0 • point 1 0 + x 1 • point 0 1 := by
    ext i; fin_cases i <;> simp [point]
  conv_lhs => rw [hx,map_add,map_smul,map_smul]

lemma det2_linearMap (f : E →ₗ[ℝ] E) (v w : E) :
    det2 (f v) (f w) = LinearMap.det f * det2 v w := by
  rw [det_eq_det2,linearMap_coordinates f v,linearMap_coordinates f w]
  simp only [det2,PiLp.add_apply,PiLp.smul_apply,smul_eq_mul]
  ring

lemma linearEquiv_det_ne_zero (L : E ≃ₗ[ℝ] E) : LinearMap.det (L : E →ₗ[ℝ] E) ≠ 0 := by
  have hh := LinearMap.det_comp (L.symm : E →ₗ[ℝ] E) (L : E →ₗ[ℝ] E)
  have he : (L.symm : E →ₗ[ℝ] E).comp (L : E →ₗ[ℝ] E) = LinearMap.id := by
    apply LinearMap.ext; intro x; exact L.symm_apply_apply x
  rw [he,LinearMap.det_id] at hh
  intro h
  rw [h,mul_zero] at hh
  exact one_ne_zero hh

noncomputable def Hex.map (H : Hex) (L : E ≃ₗ[ℝ] E) : Hex where
  φ₁ := H.φ₁.comp (L.symm : E →ₗ[ℝ] E)
  φ₂ := H.φ₂.comp (L.symm : E →ₗ[ℝ] E)
  φ₃ := H.φ₃.comp (L.symm : E →ₗ[ℝ] E)
  a := L H.a
  b := L H.b
  c := L H.c
  ha₁ := by simpa using H.ha₁
  ha₃ := by simpa using H.ha₃
  hb₁ := by simpa using H.hb₁
  hb₂ := by simpa using H.hb₂
  hc₂ := by simpa using H.hc₂
  hc₃ := by simpa using H.hc₃
  hin_a := by simpa using H.hin_a
  hin_b := by simpa using H.hin_b
  hin_c := by simpa using H.hin_c
  hdet := by
    rw [← map_add,← map_add]
    change det2 ((L : E →ₗ[ℝ] E) (H.a+H.b)) ((L : E →ₗ[ℝ] E) (H.b+H.c)) ≠ 0
    rw [det2_linearMap]
    exact mul_ne_zero (linearEquiv_det_ne_zero L) H.hdet

lemma Hex.map_set (H : Hex) (L : E ≃ₗ[ℝ] E) : (H.map L).set = L '' H.set := by
  ext x
  change (|H.φ₁ (L.symm x)| ≤ 1 ∧ |H.φ₂ (L.symm x)| ≤ 1 ∧ |H.φ₃ (L.symm x)| ≤ 1) ↔ _
  constructor
  · intro hx; exact ⟨L.symm x,hx,L.apply_symm_apply x⟩
  · rintro ⟨y,hy,rfl⟩; simpa [Hex.set] using hy

lemma Hex.volume_map (H : Hex) (L : E ≃ₗ[ℝ] E) :
    volume (H.map L).set = ENNReal.ofReal |LinearMap.det (L : E →ₗ[ℝ] E)| * volume H.set := by
  rw [Hex.map_set]
  exact Measure.addHaar_image_linearMap volume (L : E →ₗ[ℝ] E) H.set

/-- Geometric area-minimality is preserved with its Jacobian under an
invertible linear change of coordinates. -/
theorem HexAreaLowerBound.linear_image {K : Set E} {A : ℝ}
    (hmin : HexAreaLowerBound K A) (L : E ≃ₗ[ℝ] E) :
    HexAreaLowerBound (L '' K) (|LinearMap.det (L : E →ₗ[ℝ] E)| * A) := by
  intro H hH
  have hsub : K ⊆ (H.map L.symm).set := by
    intro x hx
    rw [Hex.map_set]
    exact ⟨L x,hH ⟨x,hx,rfl⟩,L.symm_apply_apply x⟩
  have hm := mul_le_mul' (le_refl (ENNReal.ofReal |LinearMap.det (L : E →ₗ[ℝ] E)|))
    (hmin (H.map L.symm) hsub)
  rw [Hex.volume_map] at hm
  have he : (L : E →ₗ[ℝ] E).comp (L.symm : E →ₗ[ℝ] E) = LinearMap.id := by
    apply LinearMap.ext; intro x; exact L.apply_symm_apply x
  have hdet := LinearMap.det_comp (L : E →ₗ[ℝ] E) (L.symm : E →ₗ[ℝ] E)
  rw [he,LinearMap.det_id] at hdet
  rw [← ENNReal.ofReal_mul (abs_nonneg _),← mul_assoc,
    ← ENNReal.ofReal_mul (abs_nonneg _),← abs_mul,← hdet] at hm
  norm_num at hm
  simpa only [ENNReal.ofReal_mul (abs_nonneg _)] using hm

lemma triangle_linearMap_image (f : E →ₗ[ℝ] E) (p q r : E) :
    f '' triangle p q r = triangle (f p) (f q) (f r) := by
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    obtain ⟨z,⟨⟨a,b⟩,hab,rfl⟩,rfl⟩ := Set.mem_vadd_set.1 hy
    apply Set.mem_vadd_set.2
    refine ⟨a • (f q-f p)+b • (f r-f p),⟨(a,b),hab,rfl⟩,?_⟩
    simp only [vadd_eq_add,map_add,map_smul,map_sub]
  · intro hx
    obtain ⟨z,⟨⟨a,b⟩,hab,rfl⟩,rfl⟩ := Set.mem_vadd_set.1 hx
    refine ⟨p+(a • (q-p)+b • (r-p)),?_,?_⟩
    · exact Set.mem_vadd_set.2 ⟨_,⟨(a,b),hab,rfl⟩,rfl⟩
    · simp only [vadd_eq_add,map_add,map_smul,map_sub]

lemma triangleArea_linearMap (f : E →ₗ[ℝ] E) (p q r : E) :
    triangleArea (f p) (f q) (f r) = |LinearMap.det f| * triangleArea p q r := by
  rw [triangleArea_eq_det,triangleArea_eq_det,← map_sub,← map_sub,det2_linearMap,abs_mul]
  ring

lemma triangle_swap_first (p q r : E) : triangle p q r = triangle q p r := by
  ext x
  constructor <;> intro hx
  all_goals
    obtain ⟨z,⟨⟨a,b⟩,⟨ha,hb,hab⟩,rfl⟩,rfl⟩ := Set.mem_vadd_set.1 hx
    apply Set.mem_vadd_set.2
    refine ⟨_,⟨(1-a-b,b),⟨by linarith,hb,by linarith⟩,rfl⟩,?_⟩
    simp only [vadd_eq_add]
    module

lemma mem_triangle_first (p q r : E) : p ∈ triangle p q r := by
  exact Set.mem_vadd_set.2 ⟨(0:E),⟨(0,0),by norm_num,by simp⟩,by simp⟩

lemma mem_triangle_second (p q r : E) : q ∈ triangle p q r := by
  rw [triangle_swap_first]
  exact mem_triangle_first _ _ _

lemma cornerTriangle_eq_triangle (d e : ℝ) :
    cornerTriangle d e = triangle (point (1-d) (-1)) (point 1 (-1)) (point 1 (-1+e)) := by
  rw [triangle_swap_first]
  unfold cornerTriangle triangle
  congr 2 <;> ext i <;> fin_cases i <;> simp [point] <;> ring

#print axioms HexAreaLowerBound.linear_image
#print axioms triangleArea_linearMap
end Certificate.Packing
