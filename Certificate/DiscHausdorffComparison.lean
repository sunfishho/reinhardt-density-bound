import Certificate.NormalizedDiscCompactness
import Certificate.NormalizedDiscInterior
import Mathlib.Topology.MetricSpace.Closeds
import Mathlib.Topology.Semicontinuity.Basic

/-! Quantitative comparison of nearby normalized convex discs and lower
semicontinuity of their actual Lebesgue area. -/
namespace Certificate.Packing
open Set Metric EMetric MeasureTheory Filter Topology TopologicalSpace Pointwise
set_option maxHeartbeats 0

theorem subset_dilation_of_nearby {S K : Set E} (hc : Convex ℝ K)
    (hb : Metric.closedBall (0:E) (1/2) ⊆ K) {r : ℝ} (hr : 1 < r)
    (hnear : ∀ x ∈ S, ∃ y ∈ K, dist x y < (r-1)/2) : S ⊆ r • K := by
  have hr0 : 0 < r := by linarith
  have hε : 0 < r-1 := by linarith
  intro x hx
  obtain ⟨y,hy,hxy⟩ := hnear x hx
  let z := (r-1)⁻¹ • (x-y)
  have hz : z ∈ K := by
    apply hb
    rw [Metric.mem_closedBall,dist_zero_right]
    dsimp [z]
    rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos hε,← div_eq_inv_mul]
    apply (div_le_iff₀ hε).2
    rw [dist_eq_norm] at hxy
    linarith
  have he : (1/r) • y+((r-1)/r) • z = r⁻¹ • x := by
    dsimp [z]
    rw [smul_smul]
    have hcoef : ((r-1)/r)*(r-1)⁻¹ = r⁻¹ := by field_simp
    rw [hcoef,one_div]
    module
  have hm : r⁻¹ • x ∈ K := he ▸ hc hy hz (by positivity) (by positivity) (by field_simp; ring)
  exact ⟨r⁻¹ • x,hm,by simp [smul_smul,hr0.ne']⟩

theorem normalized_near_dilation {K L : Compacts E}
    (hL : L ∈ normalizedDiscs) {r : ℝ} (hr : 1 < r)
    (hd : edist K L < ENNReal.ofReal ((r-1)/2)) : (K : Set E) ⊆ r • (L : Set E) := by
  apply subset_dilation_of_nearby hL.1 (closedBall_half_subset_diamond.trans hL.2.2.1) hr
  intro x hx
  obtain ⟨y,hy,hdxy⟩ := Metric.exists_edist_lt_of_hausdorffEDist_lt hx hd
  refine ⟨y,hy,?_⟩
  exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).1 (by simpa [edist_dist] using hdxy)

theorem area_le_of_subset_dilation {K L : Compacts E} {r : ℝ} (hr : 0 < r)
    (hsub : (K : Set E) ⊆ r • (L : Set E)) :
    (volume (K : Set E)).toReal ≤ r^2*(volume (L : Set E)).toReal := by
  have hh := measure_mono (μ:=volume) hsub
  rw [Measure.addHaar_smul,finrank_euclideanSpace_fin,abs_of_nonneg (sq_nonneg r)] at hh
  have hf : ENNReal.ofReal (r^2)*volume (L : Set E) ≠ ⊤ :=
    ENNReal.mul_ne_top (by finiteness) L.isCompact.measure_lt_top.ne
  have ht := ENNReal.toReal_mono hf hh
  simpa [ENNReal.toReal_mul,ENNReal.toReal_pow,ENNReal.toReal_ofReal (sq_nonneg r)] using ht

theorem lowerSemicontinuousOn_normalized_area :
    LowerSemicontinuousOn (fun K : Compacts E => (volume (K : Set E)).toReal) normalizedDiscs := by
  intro K hK b hb
  have he : ∀ᶠ r in 𝓝 (1:ℝ), r^2*b < (volume (K : Set E)).toReal := by
    exact (show Continuous (fun r : ℝ => r^2*b) from by fun_prop).continuousAt.eventually
      (gt_mem_nhds (by simpa using hb))
  obtain ⟨r,hr,hbr⟩ := ((show ∀ᶠ r in 𝓝[>] (1:ℝ), 1 < r from self_mem_nhdsWithin).and
    (nhdsWithin_le_nhds he)).exists
  have heps : 0 < ENNReal.ofReal ((r-1)/2) := ENNReal.ofReal_pos.2 (by linarith)
  filter_upwards [nhdsWithin_le_nhds (EMetric.ball_mem_nhds K heps),self_mem_nhdsWithin] with L hL hLn
  have hcomp := area_le_of_subset_dilation (by linarith : 0<r)
    (normalized_near_dilation (K:=K) (L:=L) hLn hr (by simpa [EMetric.mem_ball,edist_comm] using hL))
  by_contra h
  have hh : r^2*(volume (L : Set E)).toReal ≤ r^2*b :=
    mul_le_mul_of_nonneg_left (le_of_not_gt h) (sq_nonneg r)
  linarith

#print axioms normalized_near_dilation
#print axioms lowerSemicontinuousOn_normalized_area
end Certificate.Packing
