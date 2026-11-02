import Certificate.HVCornerCoordinates

/-! Rotation by minus sixty degrees and cyclic permutation of the
normalized hexagon parameters. -/
namespace Certificate.Packing.HVGeometry
open MeasureTheory Set Pointwise
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false

noncomputable def rotateMap : E →ₗ[ℝ] E :=
  pairLinear ((1/2:ℝ) • coord 0 + (Real.sqrt 3/2) • coord 1)
    ((-Real.sqrt 3/2) • coord 0 + (1/2:ℝ) • coord 1)

lemma rotateMap_det : LinearMap.det rotateMap = 1 := by
  rw [det_eq_det2]
  simp [rotateMap,pairLinear,point,det2]
  nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤3)]

noncomputable def rotate : E ≃ₗ[ℝ] E :=
  rotateMap.equivOfDetNeZero (by rw [rotateMap_det]; norm_num)

@[simp] lemma rotate_apply (x : E) : rotate x = rotateMap x := rfl

lemma rotate_midpoints : rotate s1 = s0 ∧ rotate s2 = s1 ∧ rotate (-s0) = s2 := by
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ)≤3)
  refine ⟨?_,?_,?_⟩ <;> ext i <;> fin_cases i <;>
    simp [rotate_apply,rotateMap,pairLinear,s0,s1,s2,pt,point] <;> nlinarith

lemma rotate_vertex (u v w : ℝ) (he2 : u*v+v*w+w*u=1) :
    rotate (p1 u v w) = p0 v w u ∧ rotate (p2 u v w) = p1 v w u := by
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ)≤3)
  have he : Real.sqrt 3*(u*v+v*w+w*u)=Real.sqrt 3 := by rw [he2]; ring
  constructor <;> ext i <;> fin_cases i <;>
    simp [rotate_apply,rotateMap,pairLinear,p0,p1,p2,s0,s1,s2,pt,point] <;>
    ring_nf <;> (try simp only [hs]) <;> nlinarith

lemma rotate_sides (u v w : ℝ) (hu : 0 < u) (hv : 0 < v) (hw : 0 < w) (x : E) :
    sideA v w u (rotate x) = sideB u v w x ∧
    sideB v w u (rotate x) = sideC u v w x ∧
    sideC v w u (rotate x) = -sideA u v w x := by
  have hs0 : Real.sqrt (3:ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ)≤3)
  have huv : u+v ≠ 0 := ne_of_gt (add_pos hu hv)
  have hvw : v+w ≠ 0 := ne_of_gt (add_pos hv hw)
  have hwu : w+u ≠ 0 := ne_of_gt (add_pos hw hu)
  have huw : u+w ≠ 0 := ne_of_gt (add_pos hu hw)
  have hvu : v+u ≠ 0 := ne_of_gt (add_pos hv hu)
  refine ⟨?_,?_,?_⟩ <;>
    simp [sideA,sideB,sideC,rotate_apply,rotateMap,pairLinear,point] <;> field_simp
  all_goals ring_nf <;> (try simp only [hs]) <;> ring

/-- All three opposite-side strips of the normalized midpoint hexagon. -/
def InHexagon (K : Set E) (u v w : ℝ) : Prop :=
  ∀ x ∈ K, |sideA u v w x| ≤ 1 ∧ |sideB u v w x| ≤ 1 ∧ |sideC u v w x| ≤ 1

lemma InHexagon.rotate {K : Set E} {u v w : ℝ} (h : InHexagon K u v w)
    (hu : 0 < u) (hv : 0 < v) (hw : 0 < w) : InHexagon (rotate '' K) v w u := by
  rintro x ⟨y,hy,rfl⟩
  obtain ⟨ha,hb,hc⟩ := rotate_sides u v w hu hv hw y
  rw [ha,hb,hc,abs_neg]
  exact ⟨(h y hy).2.1,(h y hy).2.2,(h y hy).1⟩

lemma volume_rotate (K : Set E) : volume (rotate '' K) = volume K := by
  change volume (rotateMap '' K) = volume K
  have h := Measure.addHaar_image_linearMap volume rotateMap K
  simpa only [rotateMap_det,abs_one,ENNReal.ofReal_one,one_mul] using h

lemma HexAreaLowerBound_rotate {K : Set E} {A : ℝ} (h : HexAreaLowerBound K A) :
    HexAreaLowerBound (rotate '' K) A := by
  have hh := h.linear_image rotate
  change HexAreaLowerBound (rotate '' K) (|LinearMap.det rotateMap| * A) at hh
  simpa only [rotateMap_det,abs_one,one_mul] using hh

#print axioms rotate_midpoints
#print axioms rotate_vertex
#print axioms rotate_sides
end Certificate.Packing.HVGeometry
