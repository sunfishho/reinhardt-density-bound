import Certificate.FastExpansion

namespace Certificate.Sparse

/-- Zero coefficients need not participate in the balanced polynomial merge. -/
def withoutZeros (p : Polynomial) : Polynomial :=
  p.filter (fun t => t.1 != 0)

theorem eval_withoutZeros {R : Type*} [CommRing R] (x : Fin 8 → R)
    (p : Polynomial) : eval x (withoutZeros p) = eval x p := by
  induction p with
  | nil => rfl
  | cons term p ih =>
    rcases term with ⟨c,e⟩
    by_cases hc : c = 0
    · subst c
      simpa [withoutZeros, eval] using ih
    · simpa [withoutZeros, eval, hc] using congrArg (fun v => (c : R) * e.eval x + v) ih

noncomputable def sparseGramRow (d : GramData) (basis : Fin d.size → Exponent)
    (i : Fin d.size) : Polynomial :=
  collapse 20 (List.ofFn (fun j => withoutZeros (gramTerm d basis i j)))

noncomputable def sparseGramPolynomial (d : GramData) (basis : Fin d.size → Exponent) : Polynomial :=
  collapse 20 (List.ofFn (sparseGramRow d basis))

theorem eval_sparseGramPolynomial {R : Type*} [CommRing R] (x : Fin 8 → R)
    (d : GramData) (basis : Fin d.size → Exponent) :
    eval x (sparseGramPolynomial d basis) = eval x (gramPolynomial d basis) := by
  simp only [sparseGramPolynomial, sparseGramRow, gramPolynomial, gramRowPolynomial,
    eval_collapse, evalMany_eq_sum_map, List.map_ofFn, List.sum_ofFn,
    Function.comp_apply, eval_polynomialSum, eval_withoutZeros]

theorem eval_sparseGramPolynomial_nonneg (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (d : GramData) (basis : Fin d.size → Exponent) (hden : 0 < d.den)
    (hPSD : (realGram d.A d.B d.den).PosSemidef) :
    0 ≤ eval x (sparseGramPolynomial d basis) := by
  rw [eval_sparseGramPolynomial]
  exact eval_gramPolynomial_nonneg x hx d basis hden hPSD

#print axioms eval_sparseGramPolynomial_nonneg
end Certificate.Sparse
