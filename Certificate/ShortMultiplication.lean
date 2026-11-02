import Certificate.MergeArithmetic

namespace Certificate.Sparse

/-- Use the shorter factor for the outer merge tree. In particular, multiplying
by a single monomial only translates/scales the existing ordered polynomial. -/
def mulShort (p q : Polynomial) : Polynomial :=
  if p.length ≤ q.length then mulMerged p q else mulMerged q p

theorem eval_mulShort {R : Type*} [CommRing R] (x : Fin 8 → R)
    (p q : Polynomial) : eval x (mulShort p q) = eval x p * eval x q := by
  unfold mulShort
  split <;> simp only [eval_mulMerged, mul_comm]

#print axioms eval_mulShort
end Certificate.Sparse
