import Certificate.DiscAffineNormalization

/-! A uniform inner ball for normalized discs. It prevents degenerate limits. -/
namespace Certificate.Packing
open Set Metric
set_option maxHeartbeats 0

lemma convex_combo_le_one {K : Set E} (hc : Convex ℝ K) (hz : (0:E) ∈ K)
    {x y : E} (hx : x ∈ K) (hy : y ∈ K) {r s : ℝ}
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hrs : r+s ≤ 1) : r • x+s • y ∈ K := by
  apply Tri_subset_of_mem K hc hz hx hy
  apply Set.mem_vadd_set.2
  refine ⟨r • x+s • y,⟨(r,s),⟨hr,hs,hrs⟩,by simp⟩,?_⟩
  simp

theorem coordinateDiamond_contains_core {z : E} (hz : |z 0|+|z 1| ≤ 1) :
    z ∈ coordinateDiamond := by
  have hc : Convex ℝ coordinateDiamond := convex_convexHull ℝ _
  have h0 : point 1 0 ∈ coordinateDiamond := subset_convexHull ℝ _ (by simp)
  have h1 : point (-1) 0 ∈ coordinateDiamond := subset_convexHull ℝ _ (by simp)
  have h2 : point 0 1 ∈ coordinateDiamond := subset_convexHull ℝ _ (by simp)
  have h3 : point 0 (-1) ∈ coordinateDiamond := subset_convexHull ℝ _ (by simp)
  have he : (1/2:ℝ) • point 1 0+(1/2:ℝ) • point (-1) 0=(0:E) := by
    ext i; fin_cases i <;> norm_num [point]
  have hzero : (0:E) ∈ coordinateDiamond := he ▸ hc h0 h1 (by norm_num) (by norm_num) (by norm_num)
  rcases le_total 0 (z 0) with hx | hx <;> rcases le_total 0 (z 1) with hy | hy
  · have h := convex_combo_le_one hc hzero h0 h2 hx hy (by simpa [abs_of_nonneg hx,abs_of_nonneg hy] using hz)
    convert h using 1
    ext i; fin_cases i <;> simp [point]
  · have h := convex_combo_le_one hc hzero h0 h3 hx (neg_nonneg.mpr hy)
      (by simpa [abs_of_nonneg hx,abs_of_nonpos hy] using hz)
    convert h using 1
    ext i; fin_cases i <;> simp [point]
  · have h := convex_combo_le_one hc hzero h1 h2 (neg_nonneg.mpr hx) hy
      (by simpa [abs_of_nonpos hx,abs_of_nonneg hy] using hz)
    convert h using 1
    ext i; fin_cases i <;> simp [point]
  · have h := convex_combo_le_one hc hzero h1 h3 (neg_nonneg.mpr hx) (neg_nonneg.mpr hy)
      (by simpa [abs_of_nonpos hx,abs_of_nonpos hy] using hz)
    convert h using 1
    ext i; fin_cases i <;> simp [point]

theorem closedBall_half_subset_diamond : closedBall (0:E) (1/2) ⊆ coordinateDiamond := by
  intro z hz
  have hn : ‖z‖ ≤ 1/2 := by simpa [mem_closedBall,dist_zero_right] using hz
  have h0 : |z 0| ≤ ‖z‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le z 0
  have h1 : |z 1| ≤ ‖z‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le z 1
  exact coordinateDiamond_contains_core (by linarith)

theorem zero_interior_of_diamond_subset {K : Set E} (h : coordinateDiamond ⊆ K) :
    (0:E) ∈ interior K := by
  apply mem_interior_iff_mem_nhds.2
  apply Filter.mem_of_superset (ball_mem_nhds (0:E) (by norm_num : (0:ℝ)<1/2))
  exact ball_subset_closedBall.trans (closedBall_half_subset_diamond.trans h)

#print axioms closedBall_half_subset_diamond
#print axioms zero_interior_of_diamond_subset
end Certificate.Packing
