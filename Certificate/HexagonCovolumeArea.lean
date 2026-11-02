import Certificate.HexagonFanArea

/-! The covolume of the explicitly constructed hexagonal packing lattice is
bounded by the actual enclosing hexagon area. This suffices for the general
packing comparison; no lattice-tiling theorem is assumed. -/
namespace Certificate.Packing
open Set MeasureTheory
set_option maxHeartbeats 0

lemma Hex.convex_set (H : Hex) : Convex ℝ H.set := by
  have h1 := (convex_Icc (-1:ℝ) 1).linear_preimage H.φ₁
  have h2 := (convex_Icc (-1:ℝ) 1).linear_preimage H.φ₂
  have h3 := (convex_Icc (-1:ℝ) 1).linear_preimage H.φ₃
  have he : H.set = (H.φ₁ ⁻¹' Icc (-1) 1) ∩
      ((H.φ₂ ⁻¹' Icc (-1) 1) ∩ (H.φ₃ ⁻¹' Icc (-1) 1)) := by
    ext x; simp [Hex.set,abs_le]
  rw [he]
  exact h1.inter (h2.inter h3)

lemma Hex.fan_vertex_mem (H : Hex) (i : Fin 6) : fanVertex H.a H.b H.c i ∈ H.set := by
  have ha : H.a ∈ H.set := by
    change |H.φ₁ H.a| ≤ 1 ∧ |H.φ₂ H.a| ≤ 1 ∧ |H.φ₃ H.a| ≤ 1
    rw [H.ha₁,H.ha₃]; exact ⟨by norm_num,H.hin_a,by norm_num⟩
  have hb : H.b ∈ H.set := by
    change |H.φ₁ H.b| ≤ 1 ∧ |H.φ₂ H.b| ≤ 1 ∧ |H.φ₃ H.b| ≤ 1
    rw [H.hb₁,H.hb₂]; exact ⟨by norm_num,by norm_num,H.hin_b⟩
  have hc : H.c ∈ H.set := by
    change |H.φ₁ H.c| ≤ 1 ∧ |H.φ₂ H.c| ≤ 1 ∧ |H.φ₃ H.c| ≤ 1
    rw [H.hc₂,H.hc₃]; exact ⟨H.hin_c,by norm_num,by norm_num⟩
  have hn : ∀ x ∈ H.set, -x ∈ H.set := by intro x hx; simpa [Hex.set] using hx
  fin_cases i
  · exact ha
  · exact hb
  · exact hc
  · exact hn _ ha
  · exact hn _ hb
  · exact hn _ hc

lemma Hex.fan_subset (H : Hex) : (⋃ i : Fin 6, fanTriangle H.a H.b H.c i) ⊆ H.set := by
  apply iUnion_subset
  intro i
  have hz : (0:E) ∈ H.set := by simp [Hex.set]
  have hh := Tri_subset_of_mem H.set H.convex_set hz
    (H.fan_vertex_mem i) (H.fan_vertex_mem (HVGeometry.next i))
  simp only [sub_zero] at hh
  intro x hx
  apply hh
  exact Set.mem_vadd_set.2 ⟨x,hx,by simp⟩

lemma Hex.volume_ge_covolume_of_nonneg (H : Hex) (hD : 0 ≤ det2 H.v H.w) :
    ENNReal.ofReal |det2 H.v H.w| ≤ volume H.set := by
  obtain ⟨hab,hbc,hac⟩ := H.fan_determinants_nonneg hD
  have hh := measure_mono (μ:=volume) H.fan_subset
  rw [volume_hexagon_fan H.a H.b H.c hab hbc hac] at hh
  have he : det2 H.v H.w=det2 H.a H.b+det2 H.b H.c+det2 H.a H.c := by
    simp [Hex.v,Hex.w,det2]; ring
  rwa [abs_of_nonneg hD,he]

/-- Valid for every Hex, including degeneracies and either orientation. -/
theorem Hex.volume_ge_covolume (H : Hex) :
    ENNReal.ofReal |det2 H.v H.w| ≤ volume H.set := by
  by_cases hD : 0 ≤ det2 H.v H.w
  · exact H.volume_ge_covolume_of_nonneg hD
  · have hh := H.reverse.volume_ge_covolume_of_nonneg (by rw [H.reverse_det]; linarith)
    simpa only [H.reverse_set,H.reverse_det,abs_neg] using hh

#print axioms Hex.volume_ge_covolume
end Certificate.Packing
