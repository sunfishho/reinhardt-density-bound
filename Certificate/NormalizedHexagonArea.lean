import Certificate.NormalizedHexagon

/-! Actual Lebesgue area of the normalized critical hexagon. This closes
the area/covolume normalization explicitly, without a generic polygon formula. -/
namespace Certificate.Packing.HVGeometry
open MeasureTheory Set Pointwise
set_option maxHeartbeats 0

noncomputable def cutFrameMap (u v w : ℝ) : E →ₗ[ℝ] E :=
  pairLinear (sideA u v w) (-sideC u v w)

lemma cutFrameMap_det (u v w : ℝ) :
    LinearMap.det (cutFrameMap u v w) = -LinearMap.det (cornerMap u v w) := by
  rw [det_eq_det2,det_eq_det2]
  simp [cutFrameMap,cornerMap,pairLinear,point,det2]
  ring

noncomputable def cutFrame (u v w : ℝ) (hu : 0 < u) (hv : 0 < v) (hw : 0 < w)
    (he2 : u*v+v*w+w*u=1) : E ≃ₗ[ℝ] E :=
  (cutFrameMap u v w).equivOfDetNeZero (by
    rw [cutFrameMap_det]; exact neg_ne_zero.mpr (cornerMap_det_pos u v w hu hv hw he2).ne')

lemma full_cut_denom (u v w : ℝ) (hu : 0 < u) (hv : 0 < v) (hw : 0 < w) :
    2*v/(v+w)+2*v/(u+v)-(2*v/(v+w))*(2*v/(u+v)) =
      2*v*(u+w)/((u+v)*(v+w)) := by
  have hα := ne_of_gt (add_pos hu hv)
  have hβ := ne_of_gt (add_pos hv hw)
  field_simp; ring

lemma cutForm_cutFrame (u v w : ℝ) (hu : 0 < u) (hv : 0 < v) (hw : 0 < w) (x : E) :
    cutForm (2*v/(v+w)) (2*v/(u+v)) (cutFrameMap u v w x) = -sideB u v w x := by
  have hs : Real.sqrt (3:ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hα := ne_of_gt (add_pos hu hv)
  have hβ := ne_of_gt (add_pos hv hw)
  have hγ := ne_of_gt (add_pos hu hw)
  rw [cutForm_apply,full_cut_denom u v w hu hv hw]
  simp [cutFrameMap,pairLinear,sideA,sideB,sideC,point]
  field_simp
  ring

lemma volume_normalizedHex_of_middle_min (u v w : ℝ)
    (hu : 0 < u) (hv : 0 < v) (hw : 0 < w) (he2 : u*v+v*w+w*u=1)
    (hvu : v ≤ u) (hvw : v ≤ w) :
    volume (normalizedHex u v w hu hv hw he2).set = ENNReal.ofReal (2*Real.sqrt 3) := by
  let d := 2*v/(v+w)
  let e := 2*v/(u+v)
  have hd : 0 < d := by dsimp [d]; positivity
  have he : 0 < e := by dsimp [e]; positivity
  have hd1 : d ≤ 1 := (div_le_one (add_pos hv hw)).2 (by linarith)
  have he1 : e ≤ 1 := (div_le_one (add_pos hu hv)).2 (by linarith)
  let H := normalizedHex u v w hu hv hw he2
  let C := cutHex d e hd he hd1 he1
  let L := cutFrame u v w hu hv hw he2
  have hmem (x : E) : L x ∈ C.set ↔ x ∈ H.set := by
    change (|sideA u v w x| ≤ 1 ∧ |-sideC u v w x| ≤ 1 ∧
      |cutForm d e (cutFrameMap u v w x)| ≤ 1) ↔
      (|sideA u v w x| ≤ 1 ∧ |sideB u v w x| ≤ 1 ∧ |sideC u v w x| ≤ 1)
    rw [cutForm_cutFrame u v w hu hv hw x,abs_neg,abs_neg]
    tauto
  have himg : L '' H.set = C.set := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩; exact (hmem y).2 hy
    · intro hx
      refine ⟨L.symm x,?_,L.apply_symm_apply x⟩
      apply (hmem (L.symm x)).1
      simpa using hx
  have hJ : |LinearMap.det (L : E →ₗ[ℝ] E)| = LinearMap.det (cornerMap u v w) := by
    change |LinearMap.det (cutFrameMap u v w)| = _
    rw [cutFrameMap_det,abs_neg,abs_of_pos (cornerMap_det_pos u v w hu hv hw he2)]
  have hJpos : 0 < |LinearMap.det (L : E →ₗ[ℝ] E)| := by
    rw [hJ]; exact cornerMap_det_pos u v w hu hv hw he2
  have hJarea : |LinearMap.det (L : E →ₗ[ℝ] E)| *(2*Real.sqrt 3)=4-d*e := by
    rw [hJ,← abs_of_pos (cornerMap_det_pos u v w hu hv hw he2),
      cornerMap_area_normalization u v w hu hv hw he2]
    dsimp [d,e]
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  have hCfin : volume C.set ≠ ⊤ :=
    ((measure_mono (μ:=volume) (show C.set ⊆ square from fun x hx => ⟨hx.1,hx.2.1⟩)).trans_lt
      isCompact_square.measure_lt_top).ne
  have hC : volume C.set = ENNReal.ofReal (4-d*e) := by
    rw [← volume_cutHex hd he hd1 he1]
    exact (ENNReal.ofReal_toReal hCfin).symm
  have hm : volume C.set = ENNReal.ofReal |LinearMap.det (L : E →ₗ[ℝ] E)| * volume H.set := by
    rw [← himg]
    exact Measure.addHaar_image_linearMap volume (L : E →ₗ[ℝ] E) H.set
  apply (ENNReal.mul_right_inj (ENNReal.ofReal_ne_zero_iff.2 hJpos) ENNReal.ofReal_ne_top).1
  rw [← hm,hC,← ENNReal.ofReal_mul hJpos.le,hJarea]

lemma normalizedHex_rotate_set (u v w : ℝ)
    (hu : 0 < u) (hv : 0 < v) (hw : 0 < w) (he2 : u*v+v*w+w*u=1) :
    rotate '' (normalizedHex u v w hu hv hw he2).set =
      (normalizedHex v w u hv hw hu (by linarith [he2])).set := by
  have hmem (x : E) : rotate x ∈ (normalizedHex v w u hv hw hu (by linarith [he2])).set ↔
      x ∈ (normalizedHex u v w hu hv hw he2).set := by
    change (|sideA v w u (rotate x)| ≤ 1 ∧ |sideB v w u (rotate x)| ≤ 1 ∧
      |sideC v w u (rotate x)| ≤ 1) ↔
      (|sideA u v w x| ≤ 1 ∧ |sideB u v w x| ≤ 1 ∧ |sideC u v w x| ≤ 1)
    obtain ⟨ha,hb,hc⟩ := rotate_sides u v w hu hv hw x
    rw [ha,hb,hc,abs_neg]
    tauto
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩; exact (hmem y).2 hy
  · intro hx
    refine ⟨rotate.symm x,?_,rotate.apply_symm_apply x⟩
    apply (hmem (rotate.symm x)).1
    simpa using hx

lemma volume_normalizedHex_cyclic (u v w : ℝ)
    (hu : 0 < u) (hv : 0 < v) (hw : 0 < w) (he2 : u*v+v*w+w*u=1) :
    volume (normalizedHex u v w hu hv hw he2).set =
      volume (normalizedHex v w u hv hw hu (by linarith [he2])).set := by
  rw [← normalizedHex_rotate_set u v w hu hv hw he2,volume_rotate]

/-- Exact geometric area, not merely the lattice determinant. -/
theorem volume_normalizedHex (u v w : ℝ)
    (hu : 0 < u) (hv : 0 < v) (hw : 0 < w) (he2 : u*v+v*w+w*u=1) :
    volume (normalizedHex u v w hu hv hw he2).set = ENNReal.ofReal (2*Real.sqrt 3) := by
  rcases le_total v u with hvu | huv
  · rcases le_total v w with hvw | hwv
    · exact volume_normalizedHex_of_middle_min u v w hu hv hw he2 hvu hvw
    · rw [volume_normalizedHex_cyclic u v w hu hv hw he2]
      exact volume_normalizedHex_of_middle_min v w u hv hw hu (by linarith [he2]) hwv (hwv.trans hvu)
  · rcases le_total u w with huw | hwu
    · rw [volume_normalizedHex_cyclic u v w hu hv hw he2,
        volume_normalizedHex_cyclic v w u hv hw hu (by linarith [he2])]
      exact volume_normalizedHex_of_middle_min w u v hw hu hv (by linarith [he2]) huw huv
    · rw [volume_normalizedHex_cyclic u v w hu hv hw he2]
      exact volume_normalizedHex_of_middle_min v w u hv hw hu (by linarith [he2]) (hwu.trans huv) hwu

/-- Ordinary area minimality of this explicit hexagon supplies exactly the
minimum-area premise used in the published geometric area bound. -/
theorem hexAreaLowerBound_of_normalized_minimum (K : Set E) (u v w : ℝ)
    (hu : 0 < u) (hv : 0 < v) (hw : 0 < w) (he2 : u*v+v*w+w*u=1)
    (hmin : ∀ H : Hex, K ⊆ H.set →
      volume (normalizedHex u v w hu hv hw he2).set ≤ volume H.set) :
    HexAreaLowerBound K (2*Real.sqrt 3) := by
  intro H hKH
  simpa only [volume_normalizedHex] using hmin H hKH

/-- HV 5.0.6 with area minimality of the explicit critical hexagon as its
premise; its area normalization is now proved rather than supplied. -/
theorem hales_vajjha_area_bound_of_minimal_hexagon (K : Set E)
    (hcomp : IsCompact K) (hconv : Convex ℝ K) (hsym : IsSymmetricSet K)
    (u v w : ℝ) (hu : 0 < u) (hv : 0 < v) (hw : 0 < w) (he2 : u*v+v*w+w*u=1)
    (hside : InHexagon K u v w) (h0 : s0 ∈ K) (h1 : s1 ∈ K) (h2 : s2 ∈ K)
    (hmin : ∀ H : Hex, K ⊆ H.set →
      volume (normalizedHex u v w hu hv hw he2).set ≤ volume H.set) :
    Certificate.Confinement.areaScore u v w ≤ (volume K).toReal/(2*Real.sqrt 3) :=
  hales_vajjha_area_bound K hcomp hconv hsym u v w hu hv hw he2 hside h0 h1 h2
    (hexAreaLowerBound_of_normalized_minimum K u v w hu hv hw he2 hmin)

#print axioms hales_vajjha_area_bound_of_minimal_hexagon
#print axioms volume_normalizedHex
#print axioms hexAreaLowerBound_of_normalized_minimum
end Certificate.Packing.HVGeometry
