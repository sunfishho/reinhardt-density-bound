import Certificate.FrameBoundaryArea
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-! A tangent to an oriented differentiable convex boundary arc is a supporting
line. The support inequality is derived, not included in the boundary data. -/
namespace Certificate.Packing
open MeasureTheory Set Filter
set_option maxHeartbeats 0

lemma scalar_linear_coordinates (f : E →L[ℝ] ℝ) (x : E) :
    f x = f (point 1 0)*x 0 + f (point 0 1)*x 1 := by
  have hx : x = x 0 • point 1 0 + x 1 • point 0 1 := by
    ext i; fin_cases i <;> simp [point]
  conv_lhs => rw [hx,map_add,map_smul,map_smul]
  simp only [smul_eq_mul]
  ring

lemma support_determinant_identity (f : E →L[ℝ] ℝ) (p v z : E) (hv : f v = 0) :
    f p * det2 v (z-p) = det2 p v * (f p-f z) := by
  rw [scalar_linear_coordinates f v] at hv
  rw [scalar_linear_coordinates f p,scalar_linear_coordinates f z]
  simp only [det2,PiLp.sub_apply]
  linear_combination (p 0*z 1-p 1*z 0)*hv

/-- Strict orientation relative to an interior origin determines which side
of the tangent contains the entire convex body. -/
theorem convex_boundary_tangent_support {K : Set E} (hc : Convex ℝ K)
    (hclosed : IsClosed K) (h0 : (0:E) ∈ interior K)
    {γ : ℝ → E} {v : E} {a b t : ℝ} (ht : t ∈ Ioo a b)
    (hb : ∀ s ∈ Ioo a b, γ s ∈ frontier K) (hd : HasDerivAt γ v t)
    (horient : 0 < det2 (γ t) v) :
    ∀ z ∈ K, 0 ≤ det2 v (z-γ t) := by
  have hp := hb t ht
  obtain ⟨f,hf⟩ := geometric_hahn_banach_open_point hc.interior isOpen_interior hp.2
  have hfpos : 0 < f (γ t) := by simpa using hf 0 h0
  have hsupp : ∀ z ∈ K, f z ≤ f (γ t) := by
    intro z hz
    apply closure_minimal (fun y hy => (hf y hy).le)
      (isClosed_le f.continuous continuous_const)
    rw [hc.closure_interior_eq_closure_of_nonempty_interior ⟨0,h0⟩]
    exact subset_closure hz
  have hmax : IsLocalMax (fun s => f (γ s)) t := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
    exact hsupp _ (hclosed.closure_eq ▸ frontier_subset_closure (hb s hs))
  have hv : f v = 0 := hmax.hasDerivAt_eq_zero (f.hasFDerivAt.comp_hasDerivAt t hd)
  intro z hz
  have he := support_determinant_identity f (γ t) v z hv
  have hn := mul_nonneg horient.le (sub_nonneg.2 (hsupp z hz))
  rw [← he] at hn
  exact nonneg_of_mul_nonneg_right hn hfpos

#print axioms convex_boundary_tangent_support
end Certificate.Packing
