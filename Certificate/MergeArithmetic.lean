import Certificate.SparsePolynomial

namespace Certificate.Sparse

/-- Equality checking by a single merge. Soundness needs no sortedness hypothesis;
sorted inputs make the check effective without sorting the inputs again. -/
def checkEqualMerged (p q : Polynomial) : Bool :=
  isZero (merge p (scale (-1) q))

theorem eq_of_checkMerged {R : Type*} [CommRing R] (x : Fin 8 → R)
    (p q : Polynomial) (hcheck : checkEqualMerged p q = true) :
    eval x p = eval x q := by
  have hz := eval_eq_zero_of_check x _ hcheck
  rw [eval_merge, eval_scale] at hz
  apply sub_eq_zero.mp
  simpa only [Int.cast_neg, Int.cast_one, neg_one_mul, sub_eq_add_neg] using hz

/-- Multiply by merging the translated copies of the second polynomial.
Unlike `mulFast`, this preserves their existing order rather than splitting
every translated term into a singleton and sorting everything again. -/
def mulMerged (p q : Polynomial) : Polynomial :=
  collapse 20 (p.map (fun t => termMul t q))

theorem eval_mulMerged {R : Type*} [CommRing R] (x : Fin 8 → R)
    (p q : Polynomial) : eval x (mulMerged p q) = eval x p * eval x q := by
  unfold mulMerged
  rw [eval_collapse]
  induction p with
  | nil => simp [evalMany, eval]
  | cons term p ih =>
    rcases term with ⟨c,e⟩
    simp only [List.map_cons, evalMany, eval_termMul, ih, eval]
    ring

#print axioms eq_of_checkMerged
#print axioms eval_mulMerged
end Certificate.Sparse
