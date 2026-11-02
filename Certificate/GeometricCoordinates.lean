import Certificate.Problem
namespace Certificate
set_option maxHeartbeats 0

noncomputable def State.coordinates (x : State) : Fin 8 → ℝ :=
  ![x.g11,x.g12,x.g21,x.g22,x.a,x.p,x.h,Real.sqrt 3]

/-- Determinant one supplies the algebraic identity used to normalize the control field. -/
theorem State.X_sq (x : State) (hdet : x.h^2-x.a^2-x.p^2=1) :
    x.X*x.X = -(1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [State.X,Matrix.mul_apply,Fin.sum_univ_two] <;> nlinarith [hdet]

theorem original_controlField (x : State) (u : Fin 3 → ℝ)
    (hdet : x.h^2-x.a^2-x.p^2=1) :
    x.X * ((2 / denominatorAt x u) • Z u - x.X) = controlField x u := by
  rw [mul_sub,Matrix.mul_smul,x.X_sq hdet]
  simp only [controlField,sub_neg_eq_add,add_comm]

noncomputable def rotation : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1/2,-Real.sqrt 3/2;Real.sqrt 3/2,1/2]

noncomputable def rotateState (x : State) : State where
  g11 := 1/2
  g12 := -Real.sqrt 3/2
  g21 := Real.sqrt 3/2
  g22 := 1/2
  a := (-x.a+Real.sqrt 3*x.p)/2
  p := (-Real.sqrt 3*x.a-x.p)/2
  h := x.h

noncomputable def initialState (x : State) : State where
  g11 := 1
  g12 := 0
  g21 := 0
  g22 := 1
  a := x.a
  p := x.p
  h := x.h

theorem rotation_left_inverse : rotation.transpose*rotation = 1 := by
  have hs : Real.sqrt (3 : ℝ)^2=3 := Real.sq_sqrt (by norm_num)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotation,Matrix.mul_apply,Fin.sum_univ_two] <;> nlinarith [hs]

theorem rotateState_X (x : State) :
    (rotateState x).X = rotation.transpose * x.X * rotation := by
  have hs : Real.sqrt (3 : ℝ)^2=3 := Real.sq_sqrt (by norm_num)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [State.X,rotateState,rotation,Matrix.mul_apply,Fin.sum_univ_two] <;>
    ring_nf <;> simp only [hs] <;> ring

#print axioms original_controlField
#print axioms rotateState_X
end Certificate
