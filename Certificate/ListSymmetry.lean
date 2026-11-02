import Certificate.DiagonalCheck
import Mathlib.Data.List.FinRange

namespace Certificate

theorem symmetry_of_list_check {n : ℕ} (m : List (List ℤ)) (hlen : m.length = n)
    (hcheck : symmetric m = true) (i j : Fin n) :
    (m[j.val]!)[i.val]! = (m[i.val]!)[j.val]! := by
  have hi : i.val < m.length := hlen ▸ i.isLt
  have hj : j.val < m.length := hlen ▸ j.isLt
  unfold symmetric at hcheck
  have h1 := List.all_eq_true.mp hcheck i.val (List.mem_range.mpr hi)
  have h2 := List.all_eq_true.mp h1 j.val (List.mem_range.mpr hj)
  exact (of_decide_eq_true h2).symm

end Certificate
