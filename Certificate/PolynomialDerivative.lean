import Certificate.SparsePolynomial
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Algebra.BigOperators.Fin

namespace Certificate.Sparse
open scoped BigOperators
set_option maxHeartbeats 0

/-- Formal partialPoly derivative of one monomial, including zero exponents. -/
def Exponent.partialPoly (e : Exponent) (i : Fin 8) : Term :=
  match i.val with
  | 0 => (e.g11, {e with g11 := e.g11-1})
  | 1 => (e.g12, {e with g12 := e.g12-1})
  | 2 => (e.g21, {e with g21 := e.g21-1})
  | 3 => (e.g22, {e with g22 := e.g22-1})
  | 4 => (e.a, {e with a := e.a-1})
  | 5 => (e.p, {e with p := e.p-1})
  | 6 => (e.h, {e with h := e.h-1})
  | _ => (e.t, {e with t := e.t-1})

def partialPoly (p : Polynomial) (i : Fin 8) : Polynomial :=
  p.map fun (c,e) => (c * (e.partialPoly i).1, (e.partialPoly i).2)

def directionalValue (p : Polynomial) (x v : Fin 8 → ℝ) : ℝ :=
  ∑ i, eval x (partialPoly p i) * v i

theorem Exponent.hasDerivAt_eval (e : Exponent) (x : ℝ → Fin 8 → ℝ)
    (v : Fin 8 → ℝ) (s : ℝ) (hx : ∀ i, HasDerivAt (fun t => x t i) (v i) s) :
    HasDerivAt (fun t => e.eval (x t))
      (∑ i, Certificate.Sparse.eval (x s) [e.partialPoly i] * v i) s := by
  have hd := (((((((hx 0).fun_pow e.g11).fun_mul ((hx 1).fun_pow e.g12)).mul
    ((hx 2).fun_pow e.g21)).fun_mul ((hx 3).fun_pow e.g22)).mul
    ((hx 4).fun_pow e.a)).fun_mul ((hx 5).fun_pow e.p)).fun_mul ((hx 6).fun_pow e.h)
  have hd := hd.fun_mul ((hx 7).fun_pow e.t)
  convert! hd using 1
  simp [Fin.sum_univ_succ, Exponent.partialPoly, Certificate.Sparse.eval,
    Exponent.eval, Pi.mul_apply]
  ring

theorem hasDerivAt_eval (p : Polynomial) (x : ℝ → Fin 8 → ℝ)
    (v : Fin 8 → ℝ) (s : ℝ) (hx : ∀ i, HasDerivAt (fun t => x t i) (v i) s) :
    HasDerivAt (fun t => eval (x t) p) (directionalValue p (x s) v) s := by
  induction p with
  | nil => simpa [directionalValue,partialPoly,eval] using hasDerivAt_const s (0 : ℝ)
  | cons term p ih =>
    rcases term with ⟨c,e⟩
    have hd := ((e.hasDerivAt_eval x v s hx).const_mul (c : ℝ)).fun_add ih
    convert! hd using 1
    simp only [directionalValue,partialPoly,List.map_cons,eval,Int.cast_mul,
      Finset.sum_add_distrib,Finset.mul_sum,add_mul,zero_mul,add_zero,
      Finset.sum_const_zero,mul_add]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    ring

#print axioms hasDerivAt_eval
end Certificate.Sparse
