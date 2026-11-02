import Certificate.HVFirstCorner
import Certificate.HVRotation
import Certificate.HVAreaAssembly

/-! HV Theorem 5.0.6 for a nondegenerate normalized critical hexagon.
The body is inside its three opposite-side strips, contains the six
side midpoints, and every circumscribed symmetric hexagon has area at
least `2*sqrt(3)`. All corner contacts and all area overlaps are proved. -/
namespace Certificate.Packing.HVGeometry
open MeasureTheory Set Pointwise
open Certificate.Confinement
set_option maxHeartbeats 0

lemma contact_linear_pullback (K : Set E) (L : E ≃ₗ[ℝ] E)
    (hdet : |LinearMap.det (L : E →ₗ[ℝ] E)| = 1)
    (p q a : E) (A : ℝ)
    (hc : ∃ x ∈ L '' K, x ∈ triangle (L p) (L a) (L q) ∧
      triangleArea (L p) x (L q) = A) :
    ∃ r ∈ K, r ∈ triangle p a q ∧ triangleArea p r q = A := by
  obtain ⟨x,⟨r,hr,hrx⟩,htri,harea⟩ := hc
  refine ⟨r,hr,?_,?_⟩
  · have himg : L '' triangle p a q = triangle (L p) (L a) (L q) :=
      triangle_linearMap_image (L : E →ₗ[ℝ] E) p a q
    rw [← himg] at htri
    obtain ⟨y,hy,hyx⟩ := htri
    have hyr : y=r := L.injective (hyx.trans hrx.symm)
    simpa [hyr] using hy
  · rw [← hrx] at harea
    have he := triangleArea_linearMap (L : E →ₗ[ℝ] E) p r q
    rw [hdet,one_mul] at he
    exact he.symm.trans harea

lemma rotate_abs_det : |LinearMap.det (rotate : E →ₗ[ℝ] E)| = 1 := by
  change |LinearMap.det rotateMap| = 1
  rw [rotateMap_det,abs_one]

lemma second_corner_contact (K : Set E) (hcomp : IsCompact K) (hconv : Convex ℝ K)
    (hsym : IsSymmetricSet K) (u v w : ℝ)
    (hu : 0 < u) (hv : 0 < v) (hw : 0 < w) (he2 : u*v+v*w+w*u=1)
    (hside : InHexagon K u v w) (h1 : s1 ∈ K) (h2 : s2 ∈ K)
    (hmin : HexAreaLowerBound K (2*Real.sqrt 3)) :
    ∃ r ∈ K, r ∈ triangle s1 (p1 u v w) s2 ∧
      triangleArea s1 r s2 = Real.sqrt 3/4*areaTerm w u v := by
  have hsides := hside.rotate hu hv hw
  have hroot0 : s0 ∈ rotate '' K := by
    rw [← rotate_midpoints.1]; exact ⟨s1,h1,rfl⟩
  have hroot1 : s1 ∈ rotate '' K := by
    rw [← rotate_midpoints.2.1]; exact ⟨s2,h2,rfl⟩
  have hc := first_corner_contact (rotate '' K)
    (hcomp.image rotate.toContinuousLinearEquiv.continuous)
    (hconv.linear_image (rotate : E →ₗ[ℝ] E))
    (symmetric_linear_image hsym (rotate : E →ₗ[ℝ] E)) v w u hv hw hu
    (by linarith [he2]) (fun x hx => ⟨(hsides x hx).1,(hsides x hx).2.2⟩)
    hroot0 hroot1 (HexAreaLowerBound_rotate hmin)
  apply contact_linear_pullback K rotate rotate_abs_det s1 s2 (p1 u v w) _
  simpa only [rotate_midpoints.1,rotate_midpoints.2.1,(rotate_vertex u v w he2).1,
    areaTerm, mul_comm u v] using hc

lemma third_corner_contact (K : Set E) (hcomp : IsCompact K) (hconv : Convex ℝ K)
    (hsym : IsSymmetricSet K) (u v w : ℝ)
    (hu : 0 < u) (hv : 0 < v) (hw : 0 < w) (he2 : u*v+v*w+w*u=1)
    (hside : InHexagon K u v w) (h0 : s0 ∈ K) (h2 : s2 ∈ K)
    (hmin : HexAreaLowerBound K (2*Real.sqrt 3)) :
    ∃ r ∈ K, r ∈ triangle s2 (p2 u v w) (-s0) ∧
      triangleArea s2 r (-s0) = Real.sqrt 3/4*areaTerm u v w := by
  have hroot1 : s1 ∈ rotate '' K := by
    rw [← rotate_midpoints.2.1]; exact ⟨s2,h2,rfl⟩
  have hroot2 : s2 ∈ rotate '' K := by
    rw [← rotate_midpoints.2.2]; exact ⟨-s0,(hsym s0).1 h0,rfl⟩
  have hc := second_corner_contact (rotate '' K)
    (hcomp.image rotate.toContinuousLinearEquiv.continuous)
    (hconv.linear_image (rotate : E →ₗ[ℝ] E))
    (symmetric_linear_image hsym (rotate : E →ₗ[ℝ] E)) v w u hv hw hu
    (by linarith [he2]) (hside.rotate hu hv hw)
    hroot1 hroot2 (HexAreaLowerBound_rotate hmin)
  apply contact_linear_pullback K rotate rotate_abs_det s2 (-s0) (p2 u v w) _
  simpa only [rotate_midpoints.2.1,rotate_midpoints.2.2,(rotate_vertex u v w he2).2] using hc

lemma neg_mem_triangle {p q r x : E} (hx : x ∈ triangle p q r) :
    -x ∈ triangle (-p) (-q) (-r) := by
  have h := mem_image_of_mem (-LinearMap.id : E →ₗ[ℝ] E) hx
  rw [triangle_linearMap_image] at h
  simpa using h

lemma triangleArea_neg (p q r : E) : triangleArea (-p) (-q) (-r) = triangleArea p q r := by
  rw [triangleArea_eq_det,triangleArea_eq_det]
  congr 2
  simp only [det2,PiLp.sub_apply,PiLp.neg_apply]
  ring

/-- The complete normalized geometric area estimate in the strict star domain.
No contact-point, triangle-area, nonoverlap, or areaScore bound is assumed. -/
theorem hales_vajjha_area_bound (K : Set E) (hcomp : IsCompact K) (hconv : Convex ℝ K)
    (hsym : IsSymmetricSet K) (u v w : ℝ)
    (hu : 0 < u) (hv : 0 < v) (hw : 0 < w) (he2 : u*v+v*w+w*u=1)
    (hside : InHexagon K u v w) (h0 : s0 ∈ K) (h1 : s1 ∈ K) (h2 : s2 ∈ K)
    (hmin : HexAreaLowerBound K (2*Real.sqrt 3)) :
    areaScore u v w ≤ (volume K).toReal/(2*Real.sqrt 3) := by
  obtain ⟨r0,hr0,htri0,harea0⟩ := first_corner_contact K hcomp hconv hsym u v w hu hv hw he2
    (fun x hx => ⟨(hside x hx).1,(hside x hx).2.2⟩) h0 h1 hmin
  obtain ⟨r1,hr1,htri1,harea1⟩ := second_corner_contact K hcomp hconv hsym u v w hu hv hw he2
    hside h1 h2 hmin
  obtain ⟨r2,hr2,htri2,harea2⟩ := third_corner_contact K hcomp hconv hsym u v w hu hv hw he2
    hside h0 h2 hmin
  let r : Fin 6 → E := ![r0,r1,r2,-r0,-r1,-r2]
  have hroot : ∀ i : Fin 6, root i ∈ K := by
    intro i; fin_cases i
    · exact h0
    · exact h1
    · exact h2
    · exact (hsym s0).1 h0
    · exact (hsym s1).1 h1
    · exact (hsym s2).1 h2
  have hrK : ∀ i, r i ∈ K := by
    intro i; fin_cases i
    · exact hr0
    · exact hr1
    · exact hr2
    · exact (hsym r0).1 hr0
    · exact (hsym r1).1 hr1
    · exact (hsym r2).1 hr2
  have htri : ∀ i, r i ∈ triangle (root i) (vertex u v w i) (root (next i)) := by
    intro i; fin_cases i
    · exact htri0
    · exact htri1
    · exact htri2
    · exact neg_mem_triangle htri0
    · exact neg_mem_triangle htri1
    · change -r2 ∈ triangle (-s2) (-p2 u v w) s0
      simpa only [neg_neg] using neg_mem_triangle htri2
  have hh := six_corner_area_lower_bound_of_triangle_contacts K hcomp hconv hroot
    u v w hu.le hv.le hw.le he2 r hrK htri
  have hneg : triangleArea (-s2) (-r2) s0 = triangleArea s2 r2 (-s0) := by
    simpa only [neg_neg] using triangleArea_neg s2 r2 (-s0)
  simp only [Fin.sum_univ_succ] at hh
  dsimp [r,root,next] at hh
  rw [triangleArea_neg,triangleArea_neg,hneg,harea0,harea1,harea2] at hh
  apply (le_div_iff₀ (by positivity : (0:ℝ)<2*Real.sqrt 3)).2
  unfold areaScore
  nlinarith

#print axioms second_corner_contact
#print axioms third_corner_contact
#print axioms hales_vajjha_area_bound
end Certificate.Packing.HVGeometry
