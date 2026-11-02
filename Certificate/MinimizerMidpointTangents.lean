import Certificate.HexagonUniqueSupport
import Certificate.SupportingFormNormalization
import Certificate.MinimizerMidpointContacts

/-! Every critical midpoint of the constructed minimizer has exactly one
supporting line. This is a statement at critical midpoints, not yet a proof
of smoothness or supporting-line uniqueness on the whole boundary. -/
namespace Certificate.Packing
open Set MeasureTheory
set_option maxHeartbeats 0
namespace Hex

noncomputable def sideNormal (H : Hex) : Fin 6 → (E →ₗ[ℝ] ℝ) :=
  ![H.φ₁,H.φ₂,H.φ₃,-H.φ₁,-H.φ₂,-H.φ₃]

noncomputable def sideRelabel (H : Hex) : Fin 6 → Hex :=
  ![H,H.rotate,H.rotate.rotate,H.rotate.rotate.rotate,
    H.rotate.rotate.rotate.rotate,H.rotate.rotate.rotate.rotate.rotate]

lemma sideRelabel_set (H : Hex) (i : Fin 6) : (H.sideRelabel i).set=H.set := by
  fin_cases i <;> simp [sideRelabel,rotate_set]

lemma sideRelabel_strict (H : Hex) (hs : H.Strict) (i : Fin 6) : (H.sideRelabel i).Strict := by
  have h1 := H.rotate_strict hs
  have h2 := H.rotate.rotate_strict h1
  have h3 := H.rotate.rotate.rotate_strict h2
  have h4 := H.rotate.rotate.rotate.rotate_strict h3
  have h5 := H.rotate.rotate.rotate.rotate.rotate_strict h4
  fin_cases i
  · exact hs
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5

lemma sideRelabel_normal (H : Hex) (i : Fin 6) : (H.sideRelabel i).φ₁=H.sideNormal i := by
  fin_cases i <;> rfl

lemma sideRelabel_midpoint (H : Hex) (i : Fin 6) :
    (1/2:ℝ) • ((H.sideRelabel i).a+(H.sideRelabel i).b)=H.midpoint i := by
  fin_cases i <;> simp [sideRelabel,rotate,midpoint] <;> module

lemma sideNormal_midpoint (H : Hex) (i : Fin 6) : H.sideNormal i (H.midpoint i)=1 := by
  fin_cases i <;>
    norm_num [sideNormal,midpoint,map_add,map_sub,map_smul,H.ha₁,H.hb₁,H.hb₂,H.hc₂,H.ha₃,H.hc₃]

lemma sideNormal_abs_le (H : Hex) (i : Fin 6) {x : E} (hx : x ∈ H.set) :
    |H.sideNormal i x| ≤ 1 := by
  fin_cases i
  · exact hx.1
  · exact hx.2.1
  · exact hx.2.2
  · simpa [sideNormal] using hx.1
  · simpa [sideNormal] using hx.2.1
  · simpa [sideNormal] using hx.2.2

theorem support_unique_at_midpoint (H : Hex) (hs : H.Strict) {K : Set E} (hKH : K ⊆ H.set)
    (hmin : ∀ G : Hex, K ⊆ G.set → volume H.set ≤ volume G.set) (i : Fin 6)
    (ψ : E →ₗ[ℝ] ℝ) (hψ : ∀ x ∈ K, |ψ x| ≤ 1) (hm : ψ (H.midpoint i)=1) :
    ψ=H.sideNormal i := by
  have hsub : K ⊆ (H.sideRelabel i).set := by rwa [sideRelabel_set]
  have hmin' : ∀ G : Hex, K ⊆ G.set → volume (H.sideRelabel i).set ≤ volume G.set := by
    simpa only [sideRelabel_set] using hmin
  have hh := (H.sideRelabel i).first_support_unique (H.sideRelabel_strict hs i) hsub hmin' ψ hψ
    (by rwa [sideRelabel_midpoint])
  rwa [sideRelabel_normal] at hh

theorem unique_normalized_support_at_midpoint (H : Hex) (hs : H.Strict)
    {K : Set E} (hsym : IsSymmetricSet K) (hKH : K ⊆ H.set)
    (hmin : ∀ G : Hex, K ⊆ G.set → volume H.set ≤ volume G.set) (i : Fin 6) :
    ∃! ψ : E →ₗ[ℝ] ℝ, NormalizedSupportAt K (H.midpoint i) ψ := by
  refine ⟨H.sideNormal i,⟨H.sideNormal_midpoint i,?_⟩,?_⟩
  · intro x hx; exact (le_abs_self _).trans (H.sideNormal_abs_le i (hKH hx))
  · intro ψ hψ
    exact H.support_unique_at_midpoint hs hKH hmin i ψ (normalizedSupportAt_abs hsym hψ) hψ.1

end Hex

theorem criticalHexagon_of_minimizer_unique_support (H : Hex)
    (hs : ratioMinimizingBody ⊆ H.set) (he : volume H.set=criticalHexArea ratioMinimizingBody)
    (i : Fin 6) :
    ∃! ψ : E →ₗ[ℝ] ℝ, NormalizedSupportAt ratioMinimizingBody (H.midpoint i) ψ := by
  apply H.unique_normalized_support_at_midpoint (criticalHexagon_of_minimizer_strict H hs he)
    ratioMinimizingBody_properties.1.2.2.2 hs
  intro G hG
  rw [he]
  exact criticalHexArea_le G hG

/-- Every nonzero supporting functional is a positive multiple of the
critical hexagon's side normal, hence defines the same supporting line. -/
theorem criticalHexagon_of_minimizer_supporting_form (H : Hex)
    (hs : ratioMinimizingBody ⊆ H.set) (he : volume H.set=criticalHexArea ratioMinimizingBody)
    (i : Fin 6) (ψ : E →ₗ[ℝ] ℝ) (hne : ψ ≠ 0)
    (hψ : ∀ x ∈ ratioMinimizingBody, ψ x ≤ ψ (H.midpoint i)) :
    0 < ψ (H.midpoint i) ∧ ψ=ψ (H.midpoint i) • H.sideNormal i := by
  apply supporting_form_eq_pos_smul_of_unique
    (symmetricConvexDisc_zero_interior ratioMinimizingBody_properties.1) _ ψ hne hψ
  intro φ hφ
  apply H.support_unique_at_midpoint (criticalHexagon_of_minimizer_strict H hs he) hs
    (fun G hG => by rw [he]; exact criticalHexArea_le G hG) i φ
    (normalizedSupportAt_abs ratioMinimizingBody_properties.1.2.2.2 hφ) hφ.1

theorem ratioMinimizingHexagon_midpoint_unique_support (i : Fin 6) :
    ∃! ψ : E →ₗ[ℝ] ℝ, NormalizedSupportAt ratioMinimizingBody
      (ratioMinimizingHexagon.midpoint i) ψ := by
  apply criticalHexagon_of_minimizer_unique_support _ ratioMinimizingHexagon_properties.1
  rw [ratioMinimizingHexagon_properties.2.1,ratioMinimizingBody_properties.2.1]

theorem initiallyNormalizedMinimizer_root_unique_support (i : Fin 6) :
    ∃! ψ : E →ₗ[ℝ] ℝ, NormalizedSupportAt initiallyNormalizedMinimizer (HVGeometry.root i) ψ := by
  have hh := unique_normalized_support_linear_image (ratioMinimizingHexagon_midpoint_unique_support i)
    ratioMinimizingInitialFrame
  change ∃! ψ : E →ₗ[ℝ] ℝ, NormalizedSupportAt initiallyNormalizedMinimizer
    (ratioMinimizingHexagon.midpointFrame (ratioMinimizingHexagon.midpoint i)) ψ at hh
  rwa [Hex.midpointFrame_all] at hh

#print axioms Hex.unique_normalized_support_at_midpoint
#print axioms criticalHexagon_of_minimizer_unique_support
#print axioms criticalHexagon_of_minimizer_supporting_form
#print axioms initiallyNormalizedMinimizer_root_unique_support
end Certificate.Packing
