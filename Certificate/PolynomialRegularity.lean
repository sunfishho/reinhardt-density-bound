import Certificate.SparsePolynomial
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous

namespace Certificate.Sparse

/-- Polynomial potentials preserve the regularity actually supplied by the control
reduction. In particular, no continuously differentiable control is required. -/
theorem ac_pow (f : ℝ → ℝ) (a b : ℝ)
    (hf : AbsolutelyContinuousOnInterval f a b) (n : ℕ) :
    AbsolutelyContinuousOnInterval (fun t => f t ^ n) a b := by
  induction n with
  | zero => simpa using (LipschitzWith.const (1 : ℝ)).lipschitzOnWith.absolutelyContinuousOnInterval
  | succ n ih => simpa only [pow_succ,Pi.mul_apply] using ih.fun_mul hf

theorem Exponent.absolutelyContinuous_eval (e : Exponent)
    (x : ℝ → Fin 8 → ℝ) (a b : ℝ)
    (hx : ∀ i, AbsolutelyContinuousOnInterval (fun t => x t i) a b) :
    AbsolutelyContinuousOnInterval (fun t => e.eval (x t)) a b := by
  exact (((((((ac_pow _ _ _ (hx 0) e.g11).mul (ac_pow _ _ _ (hx 1) e.g12)).mul
    (ac_pow _ _ _ (hx 2) e.g21)).mul (ac_pow _ _ _ (hx 3) e.g22)).mul
    (ac_pow _ _ _ (hx 4) e.a)).mul (ac_pow _ _ _ (hx 5) e.p)).mul
    (ac_pow _ _ _ (hx 6) e.h)).mul (ac_pow _ _ _ (hx 7) e.t)

theorem absolutelyContinuous_eval (p : Polynomial) (x : ℝ → Fin 8 → ℝ) (a b : ℝ)
    (hx : ∀ i, AbsolutelyContinuousOnInterval (fun t => x t i) a b) :
    AbsolutelyContinuousOnInterval (fun t => eval (x t) p) a b := by
  induction p with
  | nil => exact (LipschitzWith.const (0 : ℝ)).lipschitzOnWith.absolutelyContinuousOnInterval
  | cons term p ih =>
    rcases term with ⟨c,e⟩
    exact ((e.absolutelyContinuous_eval x a b hx).const_mul (c : ℝ)).add ih

theorem absolutelyContinuous_potential (p : Polynomial) (den : ℝ)
    (x : ℝ → Fin 8 → ℝ) (a b : ℝ)
    (hx : ∀ i, AbsolutelyContinuousOnInterval (fun t => x t i) a b) :
    AbsolutelyContinuousOnInterval (fun t => eval (x t) p / den) a b := by
  simpa only [div_eq_mul_inv,mul_comm] using
    (absolutelyContinuous_eval p x a b hx).const_mul den⁻¹

#print axioms absolutelyContinuous_potential
end Certificate.Sparse
