import Certificate.FrameBoundaryStar
import Mathlib.Analysis.Calculus.DerivativeTest

/-! The curvature sign of a convex boundary follows from its supporting tangent.
Only differentiability of the tangent at the point in question is needed. -/
namespace Certificate.Packing
open Set Filter MeasureTheory Topology
set_option maxHeartbeats 0

theorem second_derivative_nonneg_of_local_min {f f' : ℝ → ℝ} {d t : ℝ}
    (hmin : IsLocalMin f t)
    (hd : ∀ᶠ s in 𝓝 t, HasDerivAt f (f' s) s)
    (hdd : HasDerivAt f' d t) : 0 ≤ d := by
  have he : deriv f =ᶠ[𝓝 t] f' := hd.mono (fun _ h => h.deriv)
  have hsecond : deriv (deriv f) t = d := he.deriv_eq.trans hdd.deriv
  by_contra hn
  have hneg : deriv (deriv f) t < 0 := by rw [hsecond]; exact lt_of_not_ge hn
  have hmax := isLocalMax_of_deriv_deriv_neg hneg hmin.deriv_eq_zero
    (hd.self_of_nhds.continuousAt)
  have hconst : f =ᶠ[𝓝 t] (fun _ => f t) := by
    filter_upwards [hmin,hmax] with s hs hs'
    exact le_antisymm hs' hs
  have hz : deriv (deriv f) t = 0 := by
    simpa using hconst.deriv.deriv_eq
  linarith

/-- An oriented convex boundary has nonnegative signed curvature wherever
its tangent is differentiable. The second derivative need not be continuous. -/
theorem convex_boundary_curvature_nonneg {K : Set E}
    (hc : Convex ℝ K) (hclosed : IsClosed K) (h0 : (0:E) ∈ interior K)
    {γ v : ℝ → E} {w : E} {a b t : ℝ} (ht : t ∈ Ioo a b)
    (hb : ∀ s ∈ Ioo a b, γ s ∈ frontier K)
    (hd : ∀ s ∈ Ioo a b, HasDerivAt γ (v s) s)
    (hdd : HasDerivAt v w t) (horient : 0 < det2 (γ t) (v t)) :
    0 ≤ det2 (v t) w := by
  let f := fun s => det2 (v t) (γ s-γ t)
  let f' := fun s => det2 (v t) (v s)
  have hmin : IsLocalMin f t := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
    have hsupport := convex_boundary_tangent_support hc hclosed h0 ht hb (hd t ht)
      horient (γ s) (hclosed.closure_eq ▸ frontier_subset_closure (hb s hs))
    simpa [f,det2] using hsupport
  have hfd : ∀ᶠ s in 𝓝 t, HasDerivAt f (f' s) s := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
    have hh := (detLinear (v t)).toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt s
      ((hd s hs).sub_const (γ t))
    convert! hh using 1
  have hfdd : HasDerivAt f' (det2 (v t) w) t := by
    have hh := (detLinear (v t)).toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t hdd
    convert! hh using 1
  exact second_derivative_nonneg_of_local_min hmin hfd hfdd

#print axioms second_derivative_nonneg_of_local_min
#print axioms convex_boundary_curvature_nonneg
end Certificate.Packing
