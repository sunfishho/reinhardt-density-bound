import Certificate.PackingLattice

/-! An explicit packing from a circumscribed centrally symmetric hexagon.
Adapted and rechecked from the same recovered Fable source as PackingLattice.
No assertion that this hexagon is area-minimizing or that a minimizer exists. -/
namespace Certificate.Packing
open MeasureTheory Filter Set Pointwise
set_option maxHeartbeats 0

/-- A (possibly degenerate) centrally symmetric hexagon, described by three linear functionals
(the three pairs of parallel edge lines `|φᵢ| = 1`) together with its three vertices `a, b, c`
(the intersections of consecutive edge lines); `-a, -b, -c` are the other three vertices.
The conditions `hin_*` say that each vertex lies inside the third strip, i.e. the region
`{|φ₁| ≤ 1} ∩ {|φ₂| ≤ 1} ∩ {|φ₃| ≤ 1}` really is the hexagon `a b c (-a) (-b) (-c)`
(parallelograms occur as the degenerate case). The hexagon tiles the plane by the lattice
`ℤ(a+b) + ℤ(b+c)`, whose determinant `det2 (a+b) (b+c)` equals the area of the hexagon. -/
structure Hex where
  φ₁ : E →ₗ[ℝ] ℝ
  φ₂ : E →ₗ[ℝ] ℝ
  φ₃ : E →ₗ[ℝ] ℝ
  a : E
  b : E
  c : E
  ha₁ : φ₁ a = 1
  ha₃ : φ₃ a = -1
  hb₁ : φ₁ b = 1
  hb₂ : φ₂ b = 1
  hc₂ : φ₂ c = 1
  hc₃ : φ₃ c = 1
  hin_a : |φ₂ a| ≤ 1
  hin_b : |φ₃ b| ≤ 1
  hin_c : |φ₁ c| ≤ 1
  hdet : det2 (a + b) (b + c) ≠ 0

namespace Hex

def set (H : Hex) : Set E := {x | |H.φ₁ x| ≤ 1 ∧ |H.φ₂ x| ≤ 1 ∧ |H.φ₃ x| ≤ 1}

/-- the two generators of the tiling lattice -/
noncomputable def v (H : Hex) : E := H.a + H.b
noncomputable def w (H : Hex) : E := H.b + H.c

lemma abs_lt_one_of_mem_interior (φ : E →ₗ[ℝ] ℝ) {x : E}
    (hx : x ∈ interior {y : E | |φ y| ≤ 1}) : |φ x| < 1 := by
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at hx
  obtain ⟨ε, hε, hball⟩ := hx
  set δ : ℝ := ε / (2 * (‖x‖ + 1)) with hδ
  have hδpos : 0 < δ := by positivity
  have hmem : (1 + δ) • x ∈ Metric.ball x ε := by
    rw [Metric.mem_ball, dist_eq_norm, add_smul, one_smul, add_sub_cancel_left, norm_smul,
      Real.norm_eq_abs, abs_of_pos hδpos]
    calc δ * ‖x‖ ≤ δ * (‖x‖ + 1) := by gcongr; linarith
      _ = ε / 2 := by rw [hδ]; field_simp
      _ < ε := by linarith
  have h1 : |φ ((1 + δ) • x)| ≤ 1 := hball hmem
  rw [map_smul, smul_eq_mul, abs_mul, abs_of_pos (by linarith)] at h1
  by_contra h
  push Not at h
  nlinarith [abs_nonneg (φ x)]

lemma interior_set_subset (H : Hex) {x : E} (hx : x ∈ interior H.set) :
    |H.φ₁ x| < 1 ∧ |H.φ₂ x| < 1 ∧ |H.φ₃ x| < 1 := by
  have e : H.set = {y : E | |H.φ₁ y| ≤ 1} ∩ ({y : E | |H.φ₂ y| ≤ 1} ∩ {y : E | |H.φ₃ y| ≤ 1}) := by
    ext y; simp [Hex.set]
  rw [e, interior_inter, interior_inter] at hx
  exact ⟨abs_lt_one_of_mem_interior _ hx.1, abs_lt_one_of_mem_interior _ hx.2.1,
    abs_lt_one_of_mem_interior _ hx.2.2⟩

/-- every nonzero lattice vector has some strip functional of absolute value at least `2` -/
lemma two_le_abs_functional (H : Hex) (p : ℤ × ℤ) (hp : p ≠ 0) :
    2 ≤ |H.φ₁ (lat H.v H.w p)| ∨ 2 ≤ |H.φ₂ (lat H.v H.w p)| ∨ 2 ≤ |H.φ₃ (lat H.v H.w p)| := by
  obtain ⟨m, n⟩ := p
  have hφ₁ : H.φ₁ (lat H.v H.w (m, n)) = 2 * m + n * (1 + H.φ₁ H.c) := by
    simp only [lat, Hex.v, Hex.w, map_add, map_smul, smul_eq_mul, H.ha₁, H.hb₁]; ring
  have hφ₂ : H.φ₂ (lat H.v H.w (m, n)) = m * (H.φ₂ H.a + 1) + 2 * n := by
    simp only [lat, Hex.v, Hex.w, map_add, map_smul, smul_eq_mul, H.hb₂, H.hc₂]; ring
  have hφ₃ : H.φ₃ (lat H.v H.w (m, n)) = m * (H.φ₃ H.b - 1) + n * (H.φ₃ H.b + 1) := by
    simp only [lat, Hex.v, Hex.w, map_add, map_smul, smul_eq_mul, H.ha₃, H.hc₃]; ring
  have ht := abs_le.1 H.hin_c
  have hs := abs_le.1 H.hin_a
  have hu := abs_le.1 H.hin_b
  rw [hφ₁, hφ₂, hφ₃]
  -- case analysis on the signs of m and n
  rcases lt_trichotomy m 0 with hm | hm | hm <;> rcases lt_trichotomy n 0 with hn | hn | hn
  · -- m < 0, n < 0
    have hm' : (m : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_iff.mpr hm
    have hn' : (n : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_iff.mpr hn
    left; rw [le_abs]; right; nlinarith
  · -- m < 0, n = 0
    subst hn
    have hm' : (m : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_iff.mpr hm
    left; rw [le_abs]; right; push_cast; nlinarith
  · -- m < 0, n > 0
    have hm' : (m : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_iff.mpr hm
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    right; right; rw [le_abs]; left; nlinarith
  · -- m = 0, n < 0
    subst hm
    have hn' : (n : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_iff.mpr hn
    right; left; rw [le_abs]; right; push_cast; nlinarith
  · exact absurd (Prod.ext hm hn) hp
  · subst hm
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    right; left; rw [le_abs]; left; push_cast; nlinarith
  · -- m > 0, n < 0
    have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have hn' : (n : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_iff.mpr hn
    right; right; rw [le_abs]; right; nlinarith
  · subst hn
    have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
    left; rw [le_abs]; left; push_cast; nlinarith
  · -- m > 0, n > 0
    have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    left; rw [le_abs]; left; nlinarith

/-- translates of a set contained in the hexagon by nonzero lattice vectors have interiors
disjoint from the interior of the set -/
theorem disjoint_of_subset (H : Hex) (K : Set E) (hK : K ⊆ H.set) (p : ℤ × ℤ) (hp : p ≠ 0) :
    Disjoint (interior K) (interior (lat H.v H.w p +ᵥ K)) := by
  rw [Set.disjoint_left]
  intro x hx hx'
  rw [interior_vadd, Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, neg_add_eq_sub] at hx'
  have h1 := H.interior_set_subset (interior_mono hK hx)
  have h2 := H.interior_set_subset (interior_mono hK hx')
  have key := H.two_le_abs_functional p hp
  have e1 : H.φ₁ (lat H.v H.w p) = H.φ₁ x - H.φ₁ (x - lat H.v H.w p) := by rw [map_sub]; ring
  have e2 : H.φ₂ (lat H.v H.w p) = H.φ₂ x - H.φ₂ (x - lat H.v H.w p) := by rw [map_sub]; ring
  have e3 : H.φ₃ (lat H.v H.w p) = H.φ₃ x - H.φ₃ (x - lat H.v H.w p) := by rw [map_sub]; ring
  rcases key with k | k | k
  · rw [e1] at k; linarith [abs_sub (H.φ₁ x) (H.φ₁ (x - lat H.v H.w p)), h1.1, h2.1]
  · rw [e2] at k; linarith [abs_sub (H.φ₂ x) (H.φ₂ (x - lat H.v H.w p)), h1.2.1, h2.2.1]
  · rw [e3] at k; linarith [abs_sub (H.φ₃ x) (H.φ₃ (x - lat H.v H.w p)), h1.2.2, h2.2.2]

end Hex


/-- Circumscription alone supplies the required lattice packing. -/
theorem packingDensity_ge_hexagon (K : Set E) (hK : IsSymmetricConvexDisc K)
    (H : Hex) (hKH : K ⊆ H.set) :
    (volume K).toReal / |det2 H.v H.w| ≤ packingDensity K :=
  packingDensity_ge_lattice K hK H.v H.w H.hdet
    (fun p hp => H.disjoint_of_subset K hKH p hp)

#print axioms Hex.disjoint_of_subset
#print axioms packingDensity_ge_hexagon
end Certificate.Packing
