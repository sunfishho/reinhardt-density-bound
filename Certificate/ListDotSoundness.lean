import Certificate.DiagonalCheck
import Certificate.GramSoundness
import Mathlib.Algebra.BigOperators.Fin

namespace Certificate

theorem dot_eq_sum_get {n : ℕ} (a b : List ℤ) (ha : a.length = n) (hb : b.length = n) :
    dot a b = ∑ i : Fin n, a[i.val]! * b[i.val]! := by
  unfold dot
  rw [← List.sum_eq_foldl]
  have heq : a.zipWith (· * ·) b = List.ofFn (fun i : Fin n => a[i.val]! * b[i.val]!) := by
    apply List.ext_getElem
    · simp [ha, hb]
    · intro i hleft hright
      have hi : i < n := by simpa using hright
      simp [List.getElem_zipWith, ha, hb]
  rw [heq, List.sum_ofFn]

/-- Replacing a finite dot product by the efficient list checker preserves its value. -/
theorem gramDot_eq_listDot {n k : ℕ} (rows : Fin n → List ℤ)
    (hlen : ∀ i, (rows i).length = k) (i j : Fin n) :
    gramDot (fun (i : Fin n) (t : Fin k) => (rows i)[t.val]!) i j = dot (rows i) (rows j) := by
  exact (dot_eq_sum_get (rows i) (rows j) (hlen i) (hlen j)).symm

#print axioms dot_eq_sum_get
end Certificate
