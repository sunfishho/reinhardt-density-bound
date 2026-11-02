import Certificate.FastGram
import Certificate.SparsePolynomial

namespace Certificate.Sparse
open Matrix

/-- A balanced, exact sum of finitely many sparse polynomials. -/
def polynomialSum {n : ℕ} (p : Fin n → Polynomial) : Polynomial :=
  normalize (List.ofFn p).flatten

theorem evalMany_eq_sum_map {R : Type*} [CommRing R] (x : Fin 8 → R) (ps : List Polynomial) :
    evalMany x ps = (ps.map (eval x)).sum := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [evalMany,ih]

theorem eval_polynomialSum {R : Type*} [CommRing R] (x : Fin 8 → R)
    {n : ℕ} (p : Fin n → Polynomial) : eval x (polynomialSum p) = ∑ i, eval x (p i) := by
  rw [polynomialSum,eval_normalize,eval_flatten,evalMany_eq_sum_map]
  simp only [List.map_ofFn, List.sum_ofFn, Function.comp_apply]

def sqrtExponent : Exponent := ⟨0,0,0,0,0,0,0,1⟩

noncomputable def gramTerm (d : GramData) (basis : Fin d.size → Exponent)
    (i j : Fin d.size) : Polynomial :=
  [(d.A i j,(basis i).add (basis j)),
   (d.B i j,((basis i).add (basis j)).add sqrtExponent)]

noncomputable def gramRowPolynomial (d : GramData) (basis : Fin d.size → Exponent)
    (i : Fin d.size) : Polynomial := polynomialSum (gramTerm d basis i)

noncomputable def gramPolynomial (d : GramData) (basis : Fin d.size → Exponent) : Polynomial :=
  polynomialSum (gramRowPolynomial d basis)

theorem eval_gramTerm {R : Type*} [CommRing R] (x : Fin 8 → R)
    (d : GramData) (basis : Fin d.size → Exponent) (i j : Fin d.size) :
    eval x (gramTerm d basis i j) =
    ((d.A i j : R)+(d.B i j : R)*x 7)*(basis i).eval x*(basis j).eval x := by
  have ht : sqrtExponent.eval x = x 7 := by simp [sqrtExponent,Exponent.eval]
  simp only [gramTerm,eval,Exponent.eval_add,ht,add_zero]
  ring

noncomputable def gramForm (d : GramData) (v : Fin d.size → ℝ) : ℝ :=
  ∑ i, ∑ j, (realGram d.A d.B d.den) i j * v i * v j

theorem eval_gramPolynomial (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (d : GramData) (basis : Fin d.size → Exponent) (hden : d.den ≠ 0) :
    eval x (gramPolynomial d basis) = (d.den : ℝ) * gramForm d (fun i => (basis i).eval x) := by
  have hd : (d.den : ℝ) ≠ 0 := by exact_mod_cast hden
  simp only [gramPolynomial,gramRowPolynomial,eval_polynomialSum,eval_gramTerm,hx,
    gramForm,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  simp only [realGram]
  field_simp

theorem gramForm_nonneg (d : GramData) (hPSD : (realGram d.A d.B d.den).PosSemidef)
    (v : Fin d.size → ℝ) : 0 ≤ gramForm d v := by
  have h := hPSD.dotProduct_mulVec_nonneg v
  have heq : star v ⬝ᵥ ((realGram d.A d.B d.den) *ᵥ v) = gramForm d v := by
    simp only [dotProduct,Matrix.mulVec,gramForm,Pi.star_apply,star_trivial,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [heq] at h
  exact h

theorem eval_gramPolynomial_nonneg (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (d : GramData) (basis : Fin d.size → Exponent) (hden : 0 < d.den)
    (hPSD : (realGram d.A d.B d.den).PosSemidef) :
    0 ≤ eval x (gramPolynomial d basis) := by
  rw [eval_gramPolynomial x hx d basis (ne_of_gt hden)]
  have hd : (0 : ℝ) ≤ d.den := by exact_mod_cast hden.le
  exact mul_nonneg hd (gramForm_nonneg d hPSD _)

#print axioms eval_gramPolynomial_nonneg
end Certificate.Sparse
