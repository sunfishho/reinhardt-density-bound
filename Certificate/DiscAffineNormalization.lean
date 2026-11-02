import Certificate.FrameBoundaryArea
import Certificate.HexagonLinearTransport

/-! Compactness normalization by a largest inscribed parallelogram.
Every symmetric convex disc has an invertible linear image containing the
coordinate diamond and contained in the coordinate square. -/
namespace Certificate.Packing
open Set Filter Topology MeasureTheory
set_option maxHeartbeats 0

def coordinateDiamond : Set E :=
  convexHull ℝ {point 1 0,point (-1) 0,point 0 1,point 0 (-1)}

theorem exists_nondegenerate_pair {K : Set E} (hK : IsSymmetricConvexDisc K) :
    ∃ u ∈ K, ∃ v ∈ K, det2 u v ≠ 0 := by
  have h0 := mem_interior_iff_mem_nhds.1 (symmetricConvexDisc_zero_interior hK)
  have hz : point 0 0 = (0:E) := by ext i; fin_cases i <;> simp [point]
  have h1 : Tendsto (fun r : ℝ => point r 0) (𝓝 0) (𝓝 (0:E)) := by
    simpa only [hz] using
      (show Continuous (fun r : ℝ => point r 0) from by unfold point; fun_prop).tendsto 0
  have h2 : Tendsto (fun r : ℝ => point 0 r) (𝓝 0) (𝓝 (0:E)) := by
    simpa only [hz] using
      (show Continuous (fun r : ℝ => point 0 r) from by unfold point; fun_prop).tendsto 0
  have hx0 : ∀ᶠ r in 𝓝 (0:ℝ), point r 0 ∈ K := h1 h0
  have hy0 : ∀ᶠ r in 𝓝 (0:ℝ), point 0 r ∈ K := h2 h0
  have hm : ∀ᶠ r in 𝓝[>] (0:ℝ), point r 0 ∈ K ∧ point 0 r ∈ K :=
    nhdsWithin_le_nhds (hx0.and hy0)
  obtain ⟨r,hr,hx,hy⟩ := ((show ∀ᶠ r in 𝓝[>] (0:ℝ), 0 < r from self_mem_nhdsWithin).and hm).exists
  refine ⟨point r 0,hx,point 0 r,hy,?_⟩
  simpa [det2,point] using mul_ne_zero (ne_of_gt hr) (ne_of_gt hr)

theorem exists_maximal_determinant_pair {K : Set E} (hK : IsSymmetricConvexDisc K) :
    ∃ u ∈ K, ∃ v ∈ K, det2 u v ≠ 0 ∧
      ∀ x ∈ K, ∀ y ∈ K, |det2 x y| ≤ |det2 u v| := by
  obtain ⟨x,hx,y,hy,hxy⟩ := exists_nondegenerate_pair hK
  obtain ⟨p,hp,hmax⟩ := (hK.2.1.prod hK.2.1).exists_isMaxOn
    ⟨(x,y),hx,hy⟩ (show ContinuousOn (fun p : E × E => |det2 p.1 p.2|) (K ×ˢ K) from by
      unfold det2; fun_prop)
  refine ⟨p.1,hp.1,p.2,hp.2,?_,fun x hx y hy => hmax (show (x,y) ∈ K ×ˢ K from ⟨hx,hy⟩)⟩
  exact abs_pos.mp ((abs_pos.mpr hxy).trans_le (hmax (show (x,y) ∈ K ×ˢ K from ⟨hx,hy⟩)))

noncomputable def pairFrameLinear (u v : E) : E →ₗ[ℝ] E where
  toFun z := z 0 • u+z 1 • v
  map_add' x y := by simp; module
  map_smul' r x := by simp; module

lemma pairFrameLinear_det (u v : E) : LinearMap.det (pairFrameLinear u v)=det2 u v := by
  rw [det_eq_det2]
  simp [pairFrameLinear,point]

noncomputable def pairFrame (u v : E) (hd : det2 u v ≠ 0) : E ≃ₗ[ℝ] E :=
  (pairFrameLinear u v).equivOfDetNeZero (by rwa [pairFrameLinear_det])

@[simp] lemma pairFrame_apply (u v : E) (hd : det2 u v ≠ 0) (z : E) :
    pairFrame u v hd z = z 0 • u+z 1 • v := rfl

lemma pairFrame_coordinates (u v : E) (hd : det2 u v ≠ 0) (x : E) :
    (pairFrame u v hd).symm x 0 = det2 x v/det2 u v ∧
    (pairFrame u v hd).symm x 1 = det2 u x/det2 u v := by
  have he := (pairFrame u v hd).apply_symm_apply x
  have h0 := congrArg (fun z : E => z 0) he
  have h1 := congrArg (fun z : E => z 1) he
  simp only [pairFrame_apply,PiLp.add_apply,PiLp.smul_apply,smul_eq_mul] at h0 h1
  constructor <;> apply (eq_div_iff hd).2 <;> dsimp [det2]
  · rw [← h0,← h1]; ring
  · rw [← h0,← h1]; ring

/-- This is the compactness normalization, not yet the critical-hexagon
circle representation used by the optimal-control path. -/
theorem exists_affine_normalized_disc (K : Set E) (hK : IsSymmetricConvexDisc K) :
    ∃ L : E ≃ₗ[ℝ] E, IsSymmetricConvexDisc (L '' K) ∧
      coordinateDiamond ⊆ L '' K ∧ L '' K ⊆ square := by
  obtain ⟨u,hu,v,hv,hd,hmax⟩ := exists_maximal_determinant_pair hK
  let L := (pairFrame u v hd).symm
  have hconv : Convex ℝ (L '' K) := hK.1.linear_image (L : E →ₗ[ℝ] E)
  have hsym : IsSymmetricSet (L '' K) := by
    intro z
    constructor <;> rintro ⟨x,hx,he⟩
    · exact ⟨-x,(hK.2.2.2 x).1 hx,by rw [map_neg,he]⟩
    · exact ⟨-x,(hK.2.2.2 x).1 hx,by rw [map_neg,he,neg_neg]⟩
  have he0 : point 1 0 ∈ L '' K := by
    refine ⟨u,hu,?_⟩
    apply (pairFrame u v hd).injective
    simp [L,point]
  have he1 : point 0 1 ∈ L '' K := by
    refine ⟨v,hv,?_⟩
    apply (pairFrame u v hd).injective
    simp [L,point]
  refine ⟨L,⟨hconv,hK.2.1.image L.toContinuousLinearEquiv.continuous,?_,hsym⟩,?_,?_⟩
  · have hn := hK.2.2.1.image L.toContinuousLinearEquiv.toHomeomorph
    rw [L.toContinuousLinearEquiv.toHomeomorph.image_interior K] at hn
    convert! hn
  · apply convexHull_min ?_ hconv
    intro z hz
    simp only [mem_insert_iff,mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact he0
    · have he : point (-1) 0 = -point 1 0 := by ext i; fin_cases i <;> simp [point]
      rw [he]; exact (hsym _).1 he0
    · exact he1
    · have he : point 0 (-1) = -point 0 1 := by ext i; fin_cases i <;> simp [point]
      rw [he]; exact (hsym _).1 he1
  · rintro z ⟨x,hx,rfl⟩
    obtain ⟨h0,h1⟩ := pairFrame_coordinates u v hd x
    change |L x 0| ≤ 1 ∧ |L x 1| ≤ 1
    rw [h0,h1,abs_div,abs_div]
    exact ⟨(div_le_one (abs_pos.mpr hd)).2 (hmax x hx v hv),
      (div_le_one (abs_pos.mpr hd)).2 (hmax u hu x hx)⟩

#print axioms exists_affine_normalized_disc
end Certificate.Packing
