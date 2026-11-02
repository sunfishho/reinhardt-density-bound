import Certificate.FastExpansion

namespace Certificate.Sparse

/-- Appending two checked groups of rows adds their evaluations. -/
theorem evalMany_append {R : Type*} [CommRing R] (x : Fin 8 → R)
    (ps qs : List Polynomial) :
    evalMany x (ps ++ qs) = evalMany x ps + evalMany x qs := by
  induction ps with
  | nil => simp [evalMany]
  | cons p ps ih => simp [evalMany, ih, add_assoc]

/-- A single exact row check forms a leaf of the expansion certificate.
The witness may contain zero coefficients; no canonical-form assumption is needed. -/
theorem gram_row_leaf {R : Type*} [CommRing R] (x : Fin 8 → R)
    (d : GramData) (basis : Fin d.size → Exponent) (i : Fin d.size)
    (witness : Polynomial) (hcheck : fastGramRow d basis i = witness) :
    evalMany x ([i].map (fastGramRow d basis)) = eval x witness := by
  simp only [List.map_cons, List.map_nil, evalMany, add_zero, hcheck]

/-- A small exact merge check joins two already verified groups. Child witnesses
are opaque to this proof: their matrix arithmetic is not recomputed here. -/
theorem gram_rows_join {R : Type*} [CommRing R] (x : Fin 8 → R)
    (d : GramData) (basis : Fin d.size → Exponent)
    (leftIndices rightIndices : List (Fin d.size))
    (leftWitness rightWitness witness : Polynomial)
    (hleft : evalMany x (leftIndices.map (fastGramRow d basis)) = eval x leftWitness)
    (hright : evalMany x (rightIndices.map (fastGramRow d basis)) = eval x rightWitness)
    (hcheck : merge leftWitness rightWitness = witness) :
    evalMany x ((leftIndices ++ rightIndices).map (fastGramRow d basis)) =
      eval x witness := by
  rw [List.map_append, evalMany_append, hleft, hright, ← eval_merge, hcheck]

/-- Coverage is checked on small row indices, independently of polynomial data.
Together with the tree proof, it connects the witness to the actual Gram matrix. -/
theorem gram_expansion_of_tree {R : Type*} [CommRing R] (x : Fin 8 → R)
    (d : GramData) (basis : Fin d.size → Exponent)
    (indices : List (Fin d.size)) (witness : Polynomial)
    (hcoverage : indices = List.ofFn (fun i : Fin d.size => i))
    (htree : evalMany x (indices.map (fastGramRow d basis)) = eval x witness) :
    eval x (gramPolynomial d basis) = eval x witness := by
  rw [← eval_fastGramPolynomial, fastGramPolynomial, eval_collapse]
  rw [hcoverage] at htree
  simpa only [List.map_ofFn, Function.comp_def] using htree

theorem gram_tree_witness_nonneg (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (d : GramData) (basis : Fin d.size → Exponent)
    (indices : List (Fin d.size)) (witness : Polynomial)
    (hcoverage : indices = List.ofFn (fun i : Fin d.size => i))
    (htree : evalMany x (indices.map (fastGramRow d basis)) = eval x witness)
    (hden : 0 < d.den) (hPSD : (realGram d.A d.B d.den).PosSemidef) :
    0 ≤ eval x witness := by
  rw [← gram_expansion_of_tree x d basis indices witness hcoverage htree]
  exact eval_gramPolynomial_nonneg x hx d basis hden hPSD

#print axioms gram_expansion_of_tree
#print axioms gram_tree_witness_nonneg
end Certificate.Sparse
