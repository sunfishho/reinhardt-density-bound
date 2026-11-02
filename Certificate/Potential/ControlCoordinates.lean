import Certificate.Potential.TrajectoryAlgebra
namespace Certificate.Potential
open scoped BigOperators
set_option maxHeartbeats 0

/-- The weighted vertex denominator is exactly -tr(X Z(u)). -/
theorem controlDenominator_linear (x : State) (u : Fin 3 → ℝ) :
    controlDenominator x u = denominatorAt x u := by
  norm_num [controlDenominator,denominatorAt,State.X,Z,vertex,
    Matrix.trace,Matrix.mul_apply,Fin.sum_univ_succ,Matrix.cons_val]
  <;> norm_num [Fin.ext_iff] <;> ring

noncomputable def coordinateTangent (G W : Matrix (Fin 2) (Fin 2) ℝ) : Fin 8 → ℝ :=
  ![G 0 0,G 0 1,G 1 0,G 1 1,W 0 0,(W 0 1+W 1 0)/2,(W 1 0-W 0 1)/2,0]

/-- The path derivative used by the certificate agrees with the original matrix ODE. -/
theorem controlTangent_coordinates (x : State) (u : Fin 3 → ℝ)
    (hr : denominatorAt x u ≠ 0) :
    controlTangent x u = coordinateTangent (x.g*x.X) (controlField x u) := by
  rw [controlField_eq_cleared x u hr]
  funext i
  fin_cases i <;>
    simp [controlTangent,controlDenominator_linear,gTangent,xTangentNumerator,
      coordinateTangent,clearedNumerator,denominatorAt,State.X,Z,vertex,
      Matrix.trace,Matrix.mul_apply,Fin.sum_univ_succ,Matrix.cons_val] <;> norm_num [Fin.ext_iff] <;> ring_nf <;> simp

#print axioms controlTangent_coordinates
end Certificate.Potential
