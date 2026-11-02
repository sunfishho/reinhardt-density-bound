import Certificate.SparsePolynomial
import Certificate.Multipliers
import Mathlib.Tactic.NormNum

namespace Certificate.Sparse

def one : Polynomial := [(1,⟨0,0,0,0,0,0,0,0⟩)]
def sqrtRelation : Polynomial := [(1,⟨0,0,0,0,0,0,0,2⟩),(-3,⟨0,0,0,0,0,0,0,0⟩)]

def product : List Polynomial → Polynomial
  | [] => one
  | p::ps => mulFast p (product ps)

theorem eval_product_nonnegative (primitive : ConstraintLabel → Polynomial)
    (x : Fin 8 → ℝ) (hp : ∀ label, 0 ≤ eval x (primitive label))
    (labels : List ConstraintLabel) : 0 ≤ eval x (product (labels.map primitive)) := by
  induction labels with
  | nil => simp [product,one,eval,Exponent.eval]
  | cons label labels ih =>
    simp only [List.map_cons,product,eval_mulFast]
    exact mul_nonneg (hp label) ih

theorem eval_sqrtRelation (x : Fin 8 → ℝ) (hroot : (x 7)^2=3) :
    eval x sqrtRelation = 0 := by
  simp [sqrtRelation,eval,Exponent.eval,hroot]

/-- Positive rational scaling and an exact square-root relation justify a multiplier. -/
structure MultiplierCertificate where
  labels : List ConstraintLabel
  polynomial : Polynomial
  productDenominator : ℤ
  multiplierDenominator : ℤ
  sqrtCorrection : Polynomial

namespace MultiplierCertificate
noncomputable def check (d : MultiplierCertificate) (primitive : ConstraintLabel → Polynomial) : Bool :=
  checkEqual (scale d.productDenominator d.polynomial)
    (merge (scale d.multiplierDenominator (product (d.labels.map primitive)))
      (mulFast d.sqrtCorrection sqrtRelation))

theorem nonnegative (d : MultiplierCertificate) (primitive : ConstraintLabel → Polynomial)
    (hcheck : d.check primitive = true) (hd : 0 < d.productDenominator)
    (hq : 0 ≤ d.multiplierDenominator) (x : Fin 8 → ℝ) (hroot : (x 7)^2=3)
    (hp : ∀ label, 0 ≤ eval x (primitive label)) : 0 ≤ eval x d.polynomial := by
  have heq := eq_of_check x _ _ hcheck
  simp only [eval_scale,eval_merge,eval_mulFast,eval_sqrtRelation x hroot,mul_zero,add_zero] at heq
  have hd' : (0 : ℝ) < d.productDenominator := by exact_mod_cast hd
  have hq' : (0 : ℝ) ≤ d.multiplierDenominator := by exact_mod_cast hq
  have hright := mul_nonneg hq' (eval_product_nonnegative primitive x hp d.labels)
  have hleft : 0 ≤ (d.productDenominator : ℝ)*eval x d.polynomial := by
    rw [heq]
    exact hright
  exact (mul_nonneg_iff_of_pos_left hd').mp hleft

#print axioms nonnegative
end MultiplierCertificate
end Certificate.Sparse
