import Certificate.HexagonSideVariation

/-! Reusable construction of sufficiently small valid side variations. -/
namespace Certificate.Packing
open Set MeasureTheory Filter Topology
set_option maxHeartbeats 0
namespace Hex

noncomputable def variationDet (H : Hex) (ζ : E →ₗ[ℝ] ℝ) (t : ℝ) : ℝ :=
  det2 (H.movedA ζ t+H.movedB ζ t) (H.movedB ζ t+H.c)

structure SideVariationValid (H : Hex) (ζ : E →ₗ[ℝ] ℝ) (t : ℝ) : Prop where
  denA_pos : 0 < 1+t*ζ H.slideA
  denB_pos : 0 < 1+t*ζ H.slideB
  a_strip : |H.φ₂ (H.movedA ζ t)| < 1
  b_strip : |H.φ₃ (H.movedB ζ t)| < 1
  c_strip : |(H.φ₁+t • ζ) H.c| < 1
  determinant_pos : 0 < H.variationDet ζ t

theorem eventually_sideVariationValid (H : Hex) (hs : H.Strict)
    (hD : 0 < det2 H.v H.w) (ζ : E →ₗ[ℝ] ℝ) :
    ∀ᶠ t in 𝓝 (0:ℝ), H.SideVariationValid ζ t := by
  have hAc := H.movedA_continuousAt ζ
  have hBc := H.movedB_continuousAt ζ
  have hDc : ContinuousAt (H.variationDet ζ) 0 := by unfold variationDet det2; fun_prop
  have hD0 : H.variationDet ζ 0=det2 H.v H.w := by simp [variationDet,Hex.v,Hex.w]
  have eD : ∀ᶠ t in 𝓝 (0:ℝ), 0 < H.variationDet ζ t :=
    continuousAt_const.eventually_lt hDc (by rwa [hD0])
  have eA : ∀ᶠ t in 𝓝 (0:ℝ), 0 < 1+t*ζ H.slideA :=
    continuousAt_const.eventually_lt (by fun_prop) (by norm_num)
  have eB : ∀ᶠ t in 𝓝 (0:ℝ), 0 < 1+t*ζ H.slideB :=
    continuousAt_const.eventually_lt (by fun_prop) (by norm_num)
  have ea : ∀ᶠ t in 𝓝 (0:ℝ), |H.φ₂ (H.movedA ζ t)| < 1 :=
    ((H.φ₂.continuous_of_finiteDimensional.continuousAt.comp hAc).abs).eventually_lt
      continuousAt_const (by simpa using hs.1)
  have eb : ∀ᶠ t in 𝓝 (0:ℝ), |H.φ₃ (H.movedB ζ t)| < 1 :=
    ((H.φ₃.continuous_of_finiteDimensional.continuousAt.comp hBc).abs).eventually_lt
      continuousAt_const (by simpa using hs.2.1)
  have ec : ∀ᶠ t in 𝓝 (0:ℝ), |(H.φ₁+t • ζ) H.c| < 1 := by
    have hcc : ContinuousAt (fun t : ℝ => |(H.φ₁+t • ζ) H.c|) 0 := by
      simp only [LinearMap.add_apply,LinearMap.smul_apply,smul_eq_mul]; fun_prop
    exact hcc.eventually_lt continuousAt_const (by simpa using hs.2.2)
  filter_upwards [eA,eB,ea,eb,ec,eD] with t hA hB ha hb hc hd
  exact ⟨hA,hB,ha,hb,hc,hd⟩

noncomputable def vary (H : Hex) (hs : H.Strict) (ζ : E →ₗ[ℝ] ℝ) (t : ℝ)
    (hv : H.SideVariationValid ζ t) : Hex where
  φ₁ := H.φ₁+t • ζ
  φ₂ := H.φ₂
  φ₃ := H.φ₃
  a := H.movedA ζ t
  b := H.movedB ζ t
  c := H.c
  ha₁ := (H.moved_incidence hs ζ t hv.denA_pos.ne' hv.denB_pos.ne').1
  ha₃ := (H.moved_incidence hs ζ t hv.denA_pos.ne' hv.denB_pos.ne').2.1
  hb₁ := (H.moved_incidence hs ζ t hv.denA_pos.ne' hv.denB_pos.ne').2.2.1
  hb₂ := (H.moved_incidence hs ζ t hv.denA_pos.ne' hv.denB_pos.ne').2.2.2
  hc₂ := H.hc₂
  hc₃ := H.hc₃
  hin_a := hv.a_strip.le
  hin_b := hv.b_strip.le
  hin_c := hv.c_strip.le
  hdet := hv.determinant_pos.ne'

theorem vary_encloses_of_support (H : Hex) (hs : H.Strict) {K : Set E}
    (hKH : K ⊆ H.set) (ψ : E →ₗ[ℝ] ℝ) (hψ : ∀ x ∈ K, |ψ x| ≤ 1)
    (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) (hv : H.SideVariationValid (ψ-H.φ₁) t) :
    K ⊆ (H.vary hs (ψ-H.φ₁) t hv).set := by
  intro x hx
  obtain ⟨h1,h2,h3⟩ := hKH hx
  refine ⟨?_,h2,h3⟩
  change |(H.φ₁+t • (ψ-H.φ₁)) x| ≤ 1
  have he : (H.φ₁+t • (ψ-H.φ₁)) x=(1-t)*H.φ₁ x+t*ψ x := by simp; ring
  rw [he]
  calc
    |(1-t)*H.φ₁ x+t*ψ x| ≤ |(1-t)*H.φ₁ x|+|t*ψ x| := abs_add_le _ _
    _ = (1-t)*|H.φ₁ x|+t*|ψ x| := by
      rw [abs_mul,abs_mul,abs_of_nonneg ht,abs_of_nonneg (by linarith : 0 ≤ 1-t)]
    _ ≤ (1-t)*1+t*1 := add_le_add (mul_le_mul_of_nonneg_left h1 (by linarith))
      (mul_le_mul_of_nonneg_left (hψ x hx) ht)
    _ = 1 := by ring

#print axioms eventually_sideVariationValid
#print axioms vary_encloses_of_support
end Hex
end Certificate.Packing
