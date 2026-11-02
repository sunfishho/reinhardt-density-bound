import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.Tactic.Linarith

namespace Certificate
open Matrix
/-- A real symmetric matrix with nonnegative diagonally dominant rows is PSD. -/
theorem posSemidef_of_row_dominance {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hsym : A.IsHermitian)
    (hrow : ∀ i, ∑ j ∈ Finset.univ.erase i, ‖A i j‖ ≤ A i i) :
    A.PosSemidef := by
  apply hsym.posSemidef_iff_eigenvalues_nonneg.mpr
  intro i
  change 0 ≤ hsym.eigenvalues i
  have hv : Module.End.HasEigenvalue (Matrix.toLin' A) (hsym.eigenvalues i) := by
    apply Module.End.hasEigenvalue_of_hasEigenvector
    refine ⟨?_, ?_⟩
    · apply Module.End.mem_eigenspace_iff.mpr
      simpa only [Matrix.toLin'_apply] using hsym.mulVec_eigenvectorBasis i
    · intro hz
      have hb : hsym.eigenvectorBasis i = 0 := by
        ext j
        exact congrFun hz j
      exact hsym.eigenvectorBasis.orthonormal.ne_zero i hb
  obtain ⟨k,hk⟩ := eigenvalue_mem_ball hv
  rw [Metric.mem_closedBall, Real.dist_eq] at hk
  have hlow := (abs_le.mp hk).1
  have hr := hrow k
  linarith
#print axioms posSemidef_of_row_dominance
end Certificate
