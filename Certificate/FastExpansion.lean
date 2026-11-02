import Certificate.SOSPolynomial
namespace Certificate.Sparse

/-- Merge already sorted two-term entries before rows, avoiding a fresh sort of
all individual terms. Soundness does not assume that input lists are sorted. -/
noncomputable def fastGramRow (d : GramData) (basis : Fin d.size → Exponent)
    (i : Fin d.size) : Polynomial :=
  collapse 20 (List.ofFn (gramTerm d basis i))

noncomputable def fastGramPolynomial (d : GramData) (basis : Fin d.size → Exponent) : Polynomial :=
  collapse 20 (List.ofFn (fastGramRow d basis))

theorem eval_fastGramPolynomial {R : Type*} [CommRing R] (x : Fin 8 → R)
    (d : GramData) (basis : Fin d.size → Exponent) :
    eval x (fastGramPolynomial d basis) = eval x (gramPolynomial d basis) := by
  simp only [fastGramPolynomial,fastGramRow,gramPolynomial,gramRowPolynomial,
    eval_collapse,evalMany_eq_sum_map,List.map_ofFn,List.sum_ofFn,
    Function.comp_apply,eval_polynomialSum]

theorem eval_fastGramPolynomial_nonneg (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (d : GramData) (basis : Fin d.size → Exponent) (hden : 0 < d.den)
    (hPSD : (realGram d.A d.B d.den).PosSemidef) :
    0 ≤ eval x (fastGramPolynomial d basis) := by
  rw [eval_fastGramPolynomial]
  exact eval_gramPolynomial_nonneg x hx d basis hden hPSD

#print axioms eval_fastGramPolynomial_nonneg
end Certificate.Sparse
