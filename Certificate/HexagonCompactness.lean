import Certificate.HexagonCovolumeArea
import Certificate.HVCornerCoordinates

/-! Every hexagon in the geometric representation is a genuine symmetric
convex disc. Redundant strips are allowed. -/
namespace Certificate.Packing
open Set MeasureTheory Filter Topology Pointwise
set_option maxHeartbeats 0

noncomputable def Hex.stripFrameMap (H : Hex) : E →ₗ[ℝ] E :=
  HVGeometry.pairLinear (H.φ₁+H.φ₂) H.φ₃

lemma Hex.stripFrame_image_det_pos (H : Hex) :
    0 < det2 (H.stripFrameMap H.v) (H.stripFrameMap H.w) := by
  have he : det2 (H.stripFrameMap H.v) (H.stripFrameMap H.w) =
      4+(1-H.φ₃ H.b)*(1+H.φ₁ H.c)+(1+H.φ₃ H.b)*(1+H.φ₂ H.a) := by
    simp [Hex.stripFrameMap,HVGeometry.pairLinear,Hex.v,Hex.w,det2,point,
      H.ha₁,H.hb₁,H.hb₂,H.hc₂,H.ha₃,H.hc₃]
    ring
  rw [he]
  have hs := abs_le.1 H.hin_a
  have ht := abs_le.1 H.hin_c
  have hu := abs_le.1 H.hin_b
  nlinarith [mul_nonneg (show 0≤1-H.φ₃ H.b by linarith) (show 0≤1+H.φ₁ H.c by linarith),
    mul_nonneg (show 0≤1+H.φ₃ H.b by linarith) (show 0≤1+H.φ₂ H.a by linarith)]

lemma Hex.stripFrame_det_ne_zero (H : Hex) : LinearMap.det H.stripFrameMap ≠ 0 := by
  intro h
  have hh := H.stripFrame_image_det_pos
  rw [det2_linearMap,h,zero_mul] at hh
  exact lt_irrefl _ hh

noncomputable def Hex.stripFrame (H : Hex) : E ≃ₗ[ℝ] E :=
  H.stripFrameMap.equivOfDetNeZero H.stripFrame_det_ne_zero

lemma Hex.isClosed_set (H : Hex) : IsClosed H.set := by
  change IsClosed ({x | |H.φ₁ x| ≤ 1} ∩ ({x | |H.φ₂ x| ≤ 1} ∩ {x | |H.φ₃ x| ≤ 1}))
  exact (isClosed_le (by fun_prop) continuous_const).inter
    ((isClosed_le (by fun_prop) continuous_const).inter (isClosed_le (by fun_prop) continuous_const))

lemma Hex.zero_interior (H : Hex) : (0:E) ∈ interior H.set := by
  rw [mem_interior_iff_mem_nhds]
  have h1 : ∀ᶠ x in 𝓝 (0:E), |H.φ₁ x| < 1 :=
    (show Continuous (fun x => |H.φ₁ x|) from by fun_prop).continuousAt.eventually
      (gt_mem_nhds (by simp))
  have h2 : ∀ᶠ x in 𝓝 (0:E), |H.φ₂ x| < 1 :=
    (show Continuous (fun x => |H.φ₂ x|) from by fun_prop).continuousAt.eventually
      (gt_mem_nhds (by simp))
  have h3 : ∀ᶠ x in 𝓝 (0:E), |H.φ₃ x| < 1 :=
    (show Continuous (fun x => |H.φ₃ x|) from by fun_prop).continuousAt.eventually
      (gt_mem_nhds (by simp))
  filter_upwards [h1,h2,h3] with x hx1 hx2 hx3
  exact ⟨hx1.le,hx2.le,hx3.le⟩

lemma Hex.isCompact_set (H : Hex) : IsCompact H.set := by
  have hc : IsCompact (H.stripFrame.symm '' ((2:ℝ) • square)) :=
    (isCompact_square.smul (2:ℝ)).image H.stripFrame.symm.toContinuousLinearEquiv.continuous
  apply hc.of_isClosed_subset H.isClosed_set
  intro x hx
  refine ⟨H.stripFrame x,?_,H.stripFrame.symm_apply_apply x⟩
  refine ⟨(1/2:ℝ) • H.stripFrame x,?_,by simp [smul_smul]⟩
  change |(1/2)*(H.φ₁ x+H.φ₂ x)| ≤ 1 ∧ |(1/2)*H.φ₃ x| ≤ 1
  obtain ⟨h1,h2,h3⟩ := hx
  obtain ⟨h1l,h1u⟩ := abs_le.1 h1
  obtain ⟨h2l,h2u⟩ := abs_le.1 h2
  obtain ⟨h3l,h3u⟩ := abs_le.1 h3
  constructor <;> rw [abs_le] <;> constructor <;> linarith

/-- No compactness or interior hypotheses on H are supplied by the caller. -/
theorem Hex.isSymmetricConvexDisc (H : Hex) : IsSymmetricConvexDisc H.set := by
  refine ⟨H.convex_set,H.isCompact_set,⟨0,H.zero_interior⟩,?_⟩
  intro x; simp [Hex.set]

/-- Exact area follows from the inscribed fan lower bound and the already
proved density bound for the hexagon's own lattice packing. -/
theorem Hex.volume_eq_covolume (H : Hex) :
    volume H.set = ENNReal.ofReal |det2 H.v H.w| := by
  apply le_antisymm _ H.volume_ge_covolume
  have hh := (density_lat H.set H.isSymmetricConvexDisc H.v H.w H.hdet
    (fun p hp => H.disjoint_of_subset H.set Subset.rfl p hp)).trans (density_le_one _ _)
  have hreal : (volume H.set).toReal ≤ |det2 H.v H.w| :=
    (div_le_one (abs_pos.2 H.hdet)).1 hh
  rw [← ENNReal.ofReal_toReal H.isCompact_set.measure_lt_top.ne]
  exact ENNReal.ofReal_le_ofReal hreal

#print axioms Hex.isSymmetricConvexDisc
#print axioms Hex.volume_eq_covolume
end Certificate.Packing
