import Certificate.NormalizedMinimizer

/-! Supporting affine lines of a body containing zero in its interior can
be normalized to level one. This identifies geometric line uniqueness with
uniqueness of the normalized linear support form. -/
namespace Certificate.Packing
open Set Filter Topology
set_option maxHeartbeats 0

def NormalizedSupportAt (K : Set E) (p : E) (ψ : E →ₗ[ℝ] ℝ) : Prop :=
  ψ p=1 ∧ ∀ x ∈ K, ψ x ≤ 1

lemma support_level_pos {K : Set E} (h0 : (0:E) ∈ interior K) (p : E)
    (ψ : E →ₗ[ℝ] ℝ) (hne : ψ ≠ 0) (hs : ∀ x ∈ K, ψ x ≤ ψ p) : 0 < ψ p := by
  have hex : ∃ y : E, ψ y ≠ 0 := by
    by_contra h
    push_neg at h
    apply hne
    ext y
    exact h y
  obtain ⟨z,hz⟩ := hex
  have hexp : ∃ y : E, 0 < ψ y := by
    rcases lt_or_gt_of_ne hz with hz | hz
    · exact ⟨-z,by simpa using neg_pos.mpr hz⟩
    · exact ⟨z,hz⟩
  obtain ⟨y,hy⟩ := hexp
  have htend : Tendsto (fun t : ℝ => t • y) (𝓝 0) (𝓝 (0:E)) := by
    simpa using (show Continuous (fun t : ℝ => t • y) from by fun_prop).tendsto 0
  have ev : ∀ᶠ t in 𝓝 (0:ℝ), t • y ∈ K := htend (mem_interior_iff_mem_nhds.1 h0)
  obtain ⟨t,ht,hmem⟩ :=
    ((show ∀ᶠ t in 𝓝[>] (0:ℝ), 0 < t from self_mem_nhdsWithin).and
      (nhdsWithin_le_nhds ev)).exists
  have hh := hs (t • y) hmem
  rw [map_smul,smul_eq_mul] at hh
  exact (mul_pos ht hy).trans_le hh

lemma normalizedSupportAt_abs {K : Set E} (hsym : IsSymmetricSet K) {p : E}
    {ψ : E →ₗ[ℝ] ℝ} (h : NormalizedSupportAt K p ψ) : ∀ x ∈ K, |ψ x| ≤ 1 := by
  intro x hx
  have hn := h.2 (-x) ((hsym x).1 hx)
  rw [map_neg] at hn
  exact abs_le.2 ⟨by linarith,h.2 x hx⟩

theorem supporting_form_eq_pos_smul_of_unique {K : Set E} (h0 : (0:E) ∈ interior K)
    {p : E} {φ : E →ₗ[ℝ] ℝ}
    (hu : ∀ ψ : E →ₗ[ℝ] ℝ, NormalizedSupportAt K p ψ → ψ=φ)
    (ψ : E →ₗ[ℝ] ℝ) (hne : ψ ≠ 0) (hs : ∀ x ∈ K, ψ x ≤ ψ p) :
    0 < ψ p ∧ ψ=(ψ p) • φ := by
  have hp := support_level_pos h0 p ψ hne hs
  have hh : NormalizedSupportAt K p ((1/ψ p) • ψ) := by
    constructor
    · simp [hp.ne']
    · intro x hx
      change (1/ψ p)*ψ x ≤ 1
      rw [one_div_mul_eq_div,div_le_one hp]
      exact hs x hx
  have he := hu _ hh
  refine ⟨hp,?_⟩
  have hm := congrArg (fun f : E →ₗ[ℝ] ℝ => (ψ p) • f) he
  simpa [smul_smul,hp.ne'] using hm

theorem unique_normalized_support_linear_image {K : Set E} {p : E}
    (hu : ∃! φ : E →ₗ[ℝ] ℝ, NormalizedSupportAt K p φ) (L : E ≃ₗ[ℝ] E) :
    ∃! ψ : E →ₗ[ℝ] ℝ, NormalizedSupportAt (L '' K) (L p) ψ := by
  obtain ⟨φ,hφ,hu⟩ := hu
  refine ⟨φ.comp (L.symm : E →ₗ[ℝ] E),?_,?_⟩
  · constructor
    · simpa using hφ.1
    · rintro x ⟨y,hy,rfl⟩
      simpa using hφ.2 y hy
  · intro ψ hψ
    have hh : NormalizedSupportAt K p (ψ.comp (L : E →ₗ[ℝ] E)) :=
      ⟨hψ.1,fun x hx => hψ.2 (L x) ⟨x,hx,rfl⟩⟩
    have he := hu _ hh
    ext x
    have hx := LinearMap.congr_fun he (L.symm x)
    simpa using hx

#print axioms supporting_form_eq_pos_smul_of_unique
#print axioms unique_normalized_support_linear_image
end Certificate.Packing
