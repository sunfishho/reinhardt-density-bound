import Mathlib.Analysis.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

namespace Certificate

/-- Seven real coordinates of the determinant-one control state. -/
structure State where
  g11 : ℝ
  g12 : ℝ
  g21 : ℝ
  g22 : ℝ
  a : ℝ
  p : ℝ
  h : ℝ

namespace State
noncomputable def g (x : State) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![x.g11, x.g12; x.g21, x.g22]
noncomputable def X (x : State) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![x.a, x.p-x.h; x.p+x.h, -x.a]
noncomputable def cost (x : State) : ℝ := 3*x.h

def determinantConstraints (x : State) : Prop :=
  x.g11*x.g22-x.g12*x.g21=1 ∧ x.h^2-x.a^2-x.p^2=1
end State

noncomputable def Z (u : Fin 3 → ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(u 1-u 2)*Real.sqrt 3/3, (u 0-2*u 1-2*u 2)/3;
    u 0, -(u 1-u 2)*Real.sqrt 3/3]

/-- Correct denominator of the cleared differential certificate. -/
noncomputable def denominatorAt (x : State) (u : Fin 3 → ℝ) : ℝ :=
  -Matrix.trace (x.X * Z u)

noncomputable def clearedNumerator (x : State) (u : Fin 3 → ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ := denominatorAt x u • (1 : Matrix (Fin 2) (Fin 2) ℝ)
      + (2 : ℝ) • (x.X * Z u)

/-- The control vector field uses precisely the same denominator as the certificate. -/
noncomputable def controlField (x : State) (u : Fin 3 → ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  (1 : Matrix (Fin 2) (Fin 2) ℝ) + (2 / denominatorAt x u) • (x.X * Z u)

theorem controlField_eq_cleared (x : State) (u : Fin 3 → ℝ)
    (hr : denominatorAt x u ≠ 0) :
    controlField x u = (denominatorAt x u)⁻¹ • clearedNumerator x u := by
  unfold controlField clearedNumerator
  rw [smul_add, smul_smul, inv_mul_cancel₀ hr, one_smul, smul_smul]
  congr 1
  congr 1
  simp only [div_eq_mul_inv, mul_comm]

/-- The quadratic X constraint follows from determinant one and the stated height bound. -/
theorem xNorm_constraint (x : State) (hdet : x.h^2-x.a^2-x.p^2=1)
    (hl : 0 ≤ x.h) (hu : x.h ≤ 12/5) :
    0 ≤ (12/5 : ℝ)^2-1-x.a^2-x.p^2 := by
  have hh := mul_nonneg hl (sub_nonneg.mpr hu)
  nlinarith only [hdet, hh, hl, hu]

#print axioms controlField_eq_cleared
#print axioms xNorm_constraint
end Certificate
