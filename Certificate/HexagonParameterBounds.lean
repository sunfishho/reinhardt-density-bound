import Certificate.HexagonParameters

/-! A fixed inner diamond and an upper area bound bound every normal and
vertex coordinate of an enclosing hexagon. -/
namespace Certificate.Packing
open Set MeasureTheory Filter Topology
set_option maxHeartbeats 0

lemma exists_axis_points {K : Set E} (hK : IsSymmetricConvexDisc K) :
    ∃ r : ℝ, 0 < r ∧ point r 0 ∈ K ∧ point 0 r ∈ K := by
  have h0 := mem_interior_iff_mem_nhds.1 (symmetricConvexDisc_zero_interior hK)
  have hz : point 0 0 = (0:E) := by ext i; fin_cases i <;> simp [point]
  have h1 : Tendsto (fun r : ℝ => point r 0) (𝓝 0) (𝓝 (0:E)) := by
    simpa only [hz] using
      (show Continuous (fun r : ℝ => point r 0) from by unfold point; fun_prop).tendsto 0
  have h2 : Tendsto (fun r : ℝ => point 0 r) (𝓝 0) (𝓝 (0:E)) := by
    simpa only [hz] using
      (show Continuous (fun r : ℝ => point 0 r) from by unfold point; fun_prop).tendsto 0
  have hx : ∀ᶠ r in 𝓝 (0:ℝ), point r 0 ∈ K := h1 h0
  have hy : ∀ᶠ r in 𝓝 (0:ℝ), point 0 r ∈ K := h2 h0
  obtain ⟨r,hr,hx,hy⟩ := ((show ∀ᶠ r in 𝓝[>] (0:ℝ), 0 < r from self_mem_nhdsWithin).and
    (nhdsWithin_le_nhds (hx.and hy))).exists
  exact ⟨r,hr,hx,hy⟩

lemma Hex.coordinate_bound (H : Hex) {r M : ℝ} (hr : 0 < r)
    (h0 : point r 0 ∈ H.set) (h1 : point 0 r ∈ H.set)
    (hM : |det2 H.v H.w| ≤ M) {x : E} (hx : x ∈ H.set) (j : Fin 2) : |x j| ≤ M/r := by
  have harea (p : E) (hp : p ∈ H.set) : |det2 (p-x) (-p-x)|/2 ≤ M := by
    have hn : -p ∈ H.set := (H.isSymmetricConvexDisc.2.2.2 p).1 hp
    have hh := ENNReal.toReal_mono H.isCompact_set.measure_lt_top.ne
      (measure_mono (μ:=volume) (Tri_subset_of_mem H.set H.convex_set hx hp hn))
    rw [volume_triangle,H.volume_eq_covolume,ENNReal.toReal_ofReal (abs_nonneg _)] at hh
    exact hh.trans hM
  apply (le_div_iff₀ hr).2
  fin_cases j
  · have hh := harea (point 0 r) h1
    have he : det2 (point 0 r-x) (-point 0 r-x)=2*r*x 0 := by simp [det2,point]; ring
    rw [he,abs_mul,abs_mul,abs_of_pos hr] at hh
    norm_num at hh
    change |x 0| * r ≤ M
    nlinarith
  · have hh := harea (point r 0) h0
    have he : det2 (point r 0-x) (-point r 0-x)= -(2*r*x 1) := by simp [det2,point]; ring
    rw [he,abs_neg,abs_mul,abs_mul,abs_of_pos hr] at hh
    norm_num at hh
    change |x 1| * r ≤ M
    nlinarith

namespace HexParameters
lemma coefficient_bound {K : Set E} {d : HexParameters} {r : ℝ} (hr : 0 < r)
    (h0 : point r 0 ∈ K) (h1 : point 0 r ∈ K) (he : Encloses K d)
    (i : Fin 3) (j : Fin 2) : |d.1 i j| ≤ 1/r := by
  have hzero : |d.form i (point r 0)| ≤ 1 := by
    have hh := he _ h0
    fin_cases i
    · exact hh.1
    · exact hh.2.1
    · exact hh.2.2
  have hone : |d.form i (point 0 r)| ≤ 1 := by
    have hh := he _ h1
    fin_cases i
    · exact hh.1
    · exact hh.2.1
    · exact hh.2.2
  simp only [form,LinearMap.add_apply,LinearMap.smul_apply,smul_eq_mul,coord_eval,
    point_zero,point_one,mul_zero,zero_add,add_zero,abs_mul,abs_of_pos hr] at hzero hone
  apply (le_div_iff₀ hr).2
  fin_cases j
  · exact hzero
  · exact hone

lemma vertex_bound {K : Set E} {d : HexParameters} {r M : ℝ} (hr : 0 < r)
    (h0 : point r 0 ∈ K) (h1 : point 0 r ∈ K) (hv : d.Valid) (he : Encloses K d)
    (hM : d.covolume ≤ M) (i : Fin 3) (j : Fin 2) : |d.2 i j| ≤ M/r := by
  have hm : d.vertex i ∈ (d.toHex hv).set := by
    fin_cases i
    · exact (d.toHex hv).fan_vertex_mem 0
    · exact (d.toHex hv).fan_vertex_mem 1
    · exact (d.toHex hv).fan_vertex_mem 2
  have hh := (d.toHex hv).coordinate_bound hr (he _ h0) (he _ h1) hM hm j
  fin_cases j <;> exact hh

def boundedEnclosers (K : Set E) (M : ℝ) : Set HexParameters :=
  {d | d.Valid ∧ Encloses K d ∧ d.covolume ≤ M}

/-- Compactness includes degeneracies: determinant nonvanishing is derived
from the incidence constraints after taking the limit. -/
theorem isCompact_boundedEnclosers {K : Set E} {r : ℝ} (hr : 0 < r)
    (h0 : point r 0 ∈ K) (h1 : point 0 r ∈ K) (M : ℝ) :
    IsCompact (boundedEnclosers K M) := by
  let B := max (1/r) (M/r)
  let lo : HexParameters := (fun _ _ => -B,fun _ _ => -B)
  let hi : HexParameters := (fun _ _ => B,fun _ _ => B)
  apply (isCompact_Icc (a:=lo) (b:=hi)).of_isClosed_subset
  · exact isClosed_valid.inter ((isClosed_encloses K).inter
      (isClosed_le continuous_covolume continuous_const))
  · intro d hd
    have hn (i : Fin 3) (j : Fin 2) : |d.1 i j| ≤ B :=
      (coefficient_bound hr h0 h1 hd.2.1 i j).trans (le_max_left _ _)
    have hv (i : Fin 3) (j : Fin 2) : |d.2 i j| ≤ B :=
      (vertex_bound hr h0 h1 hd.1 hd.2.1 hd.2.2 i j).trans (le_max_right _ _)
    exact ⟨⟨fun i j => (abs_le.1 (hn i j)).1,fun i j => (abs_le.1 (hv i j)).1⟩,
      ⟨fun i j => (abs_le.1 (hn i j)).2,fun i j => (abs_le.1 (hv i j)).2⟩⟩

#print axioms isCompact_boundedEnclosers
end HexParameters
end Certificate.Packing
