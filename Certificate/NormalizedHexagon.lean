import Certificate.HVAreaBound
import Certificate.PackingGeometry

/-! The normalized critical hexagon as an actual Hex object, with its
packing lattice. Its existence is explicit once the star parameters are given. -/
namespace Certificate.Packing.HVGeometry
open MeasureTheory Set Pointwise
set_option maxHeartbeats 0

lemma side_evaluations (u v w : ℝ) (hu : 0 < u) (hv : 0 < v) (hw : 0 < w)
    (he2 : u*v+v*w+w*u=1) :
    (sideA u v w (p0 u v w)=1 ∧ sideA u v w (p1 u v w)=1 ∧
      sideA u v w (p2 u v w)=(w-v)/(v+w)) ∧
    (sideB u v w (p0 u v w)=(w-u)/(u+w) ∧ sideB u v w (p1 u v w)=1 ∧
      sideB u v w (p2 u v w)=1) ∧
    (sideC u v w (p0 u v w)= -1 ∧ sideC u v w (p1 u v w)=(u-v)/(u+v) ∧
      sideC u v w (p2 u v w)=1) := by
  have hs : Real.sqrt (3:ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have huv : u+v ≠ 0 := ne_of_gt (add_pos hu hv)
  have hvw : v+w ≠ 0 := ne_of_gt (add_pos hv hw)
  have huw : u+w ≠ 0 := ne_of_gt (add_pos hu hw)
  have he (c : ℝ) : c*(u*v+v*w+w*u)=c := by rw [he2]; ring
  refine ⟨⟨?_,?_,?_⟩,⟨?_,?_,?_⟩,⟨?_,?_,?_⟩⟩ <;>
    simp [sideA,sideB,sideC,p0,p1,p2,s0,s1,s2,pt] <;> field_simp <;>
    nlinarith [he u,he v,he w]

lemma vertex_midpoint_det (u v w : ℝ) :
    det2 (p0 u v w+p1 u v w) (p1 u v w+p2 u v w) = 2*Real.sqrt 3 := by
  simp [p1,p2,p0,s1,s2,pt,det2]
  ring

lemma abs_sub_div_add_le_one (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    |(a-b)/(a+b)| ≤ 1 := by
  rw [abs_div,abs_of_pos (add_pos ha hb),div_le_one (add_pos ha hb),abs_le]
  constructor <;> linarith

noncomputable def normalizedHex (u v w : ℝ) (hu : 0 < u) (hv : 0 < v) (hw : 0 < w)
    (he2 : u*v+v*w+w*u=1) : Hex where
  φ₁ := sideA u v w
  φ₂ := sideB u v w
  φ₃ := sideC u v w
  a := p0 u v w
  b := p1 u v w
  c := p2 u v w
  ha₁ := (side_evaluations u v w hu hv hw he2).1.1
  ha₃ := (side_evaluations u v w hu hv hw he2).2.2.1
  hb₁ := (side_evaluations u v w hu hv hw he2).1.2.1
  hb₂ := (side_evaluations u v w hu hv hw he2).2.1.2.1
  hc₂ := (side_evaluations u v w hu hv hw he2).2.1.2.2
  hc₃ := (side_evaluations u v w hu hv hw he2).2.2.2.2
  hin_a := by
    rw [(side_evaluations u v w hu hv hw he2).2.1.1,add_comm u w]
    exact abs_sub_div_add_le_one w u hw hu
  hin_b := by
    rw [(side_evaluations u v w hu hv hw he2).2.2.2.1]
    exact abs_sub_div_add_le_one u v hu hv
  hin_c := by
    rw [(side_evaluations u v w hu hv hw he2).1.2.2,add_comm v w]
    exact abs_sub_div_add_le_one w v hw hv
  hdet := by rw [vertex_midpoint_det]; positivity

lemma normalizedHex_covolume (u v w : ℝ) (hu : 0 < u) (hv : 0 < v) (hw : 0 < w)
    (he2 : u*v+v*w+w*u=1) :
    |det2 (normalizedHex u v w hu hv hw he2).v (normalizedHex u v w hu hv hw he2).w| =
      2*Real.sqrt 3 := by
  change |det2 (p0 u v w+p1 u v w) (p1 u v w+p2 u v w)| = _
  rw [vertex_midpoint_det,abs_of_nonneg (by positivity)]

lemma Hex_covolume_map (H : Hex) (L : E ≃ₗ[ℝ] E) :
    |det2 (H.map L).v (H.map L).w| =
      |LinearMap.det (L : E →ₗ[ℝ] E)| * |det2 H.v H.w| := by
  change |det2 (L H.a+L H.b) (L H.b+L H.c)| = _
  rw [← map_add,← map_add]
  change |det2 ((L : E →ₗ[ℝ] E) H.v) ((L : E →ₗ[ℝ] E) H.w)| = _
  rw [det2_linearMap,abs_mul]

/-- Pulling the explicit normalized hexagon back to the original body gives
an actual packing, without assuming affine invariance of packing density. -/
theorem packingDensity_ge_area_of_normalized_frame (K : Set E) (hK : IsSymmetricConvexDisc K)
    (L : E ≃ₗ[ℝ] E) (hdet : |LinearMap.det (L : E →ₗ[ℝ] E)|=1)
    (u v w : ℝ) (hu : 0 < u) (hv : 0 < v) (hw : 0 < w) (he2 : u*v+v*w+w*u=1)
    (hside : InHexagon (L '' K) u v w) :
    (volume K).toReal/(2*Real.sqrt 3) ≤ packingDensity K := by
  let H := normalizedHex u v w hu hv hw he2
  have hsub : K ⊆ (H.map L.symm).set := by
    intro x hx
    rw [Hex.map_set]
    exact ⟨L x,hside (L x) ⟨x,hx,rfl⟩,L.symm_apply_apply x⟩
  have hi : |LinearMap.det (L.symm : E →ₗ[ℝ] E)|=1 := by
    rw [LinearEquiv.det_coe_symm,abs_inv,hdet,inv_one]
  have hh := packingDensity_ge_hexagon K hK (H.map L.symm) hsub
  rw [Hex_covolume_map,hi,one_mul,normalizedHex_covolume] at hh
  exact hh

#print axioms normalizedHex_covolume
#print axioms packingDensity_ge_area_of_normalized_frame
end Certificate.Packing.HVGeometry
