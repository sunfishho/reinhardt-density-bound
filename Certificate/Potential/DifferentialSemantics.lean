import Certificate.Potential.Semantics
namespace Certificate.Potential
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 10000

noncomputable def vertex (k : Fin 3) : Fin 3 → ℝ := fun i => if i=k then 1 else 0
noncomputable def denominatorPoly (k : Fin 3) : Polynomial := ![r3_0,r3_1,r3_2] k
noncomputable def xVelocityPoly (k : Fin 3) : Fin 8 → Polynomial :=
  ![xVelocity3_0,xVelocity3_1,xVelocity3_2] k
noncomputable def clearedTarget (k : Fin 3) : Polynomial :=
  ![clearedTarget_0,clearedTarget_1,clearedTarget_2] k

noncomputable def gTangent (x : State) : Fin 8 → ℝ :=
  ![(x.g*x.X) 0 0,(x.g*x.X) 0 1,(x.g*x.X) 1 0,(x.g*x.X) 1 1,0,0,0,0]
noncomputable def xTangentNumerator (x : State) (k : Fin 3) : Fin 8 → ℝ :=
  let N := clearedNumerator x (vertex k)
  ![0,0,0,0,N 0 0,(N 0 1+N 1 0)/2,(N 1 0-N 0 1)/2,0]

noncomputable def dG (x : State) : ℝ :=
  directionalValue polynomial x.coordinates (gTangent x) / denominator
noncomputable def dX (x : State) (k : Fin 3) : ℝ :=
  directionalValue polynomial x.coordinates (xTangentNumerator x k) / denominator

theorem gVelocity_correct (x : State) (i : Fin 8) :
    eval x.coordinates (gVelocity i) = gTangent x i := by
  fin_cases i <;> norm_num [gVelocity,gTangent,eval,Exponent.eval,State.coordinates,Matrix.cons_val,
    State.g,State.X,Matrix.mul_apply,Fin.sum_univ_two] <;> simp only [Matrix.cons_val] <;> norm_num [Fin.ext_iff] <;> ring

theorem denominatorPoly_correct (x : State) (k : Fin 3) :
    eval x.coordinates (denominatorPoly k) = 3*denominatorAt x (vertex k) := by
  fin_cases k <;> norm_num [denominatorPoly,r3_0,r3_1,r3_2,eval,Exponent.eval,State.coordinates,Matrix.cons_val,
    denominatorAt,State.X,Z,vertex,Matrix.trace,
    Matrix.mul_apply,Fin.sum_univ_two] <;> simp only [Matrix.cons_val] <;> norm_num [Fin.ext_iff] <;> ring

theorem xVelocityPoly_correct (x : State) (k : Fin 3) (i : Fin 8) :
    eval x.coordinates (xVelocityPoly k i) = 3*xTangentNumerator x k i := by
  fin_cases k <;> fin_cases i <;>
    norm_num [xVelocityPoly,xVelocity3_0,xVelocity3_1,xVelocity3_2,
      xTangentNumerator,eval,Exponent.eval,State.coordinates,Matrix.cons_val,clearedNumerator,
      denominatorAt,State.X,Z,vertex,Matrix.trace,Matrix.mul_apply,Fin.sum_univ_two] <;> simp only [Matrix.cons_val] <;> norm_num [Fin.ext_iff] <;> ring

theorem cost_correct (x : State) : eval x.coordinates cost = x.cost := by
  norm_num [cost,eval,Exponent.eval,State.coordinates,Matrix.cons_val,State.cost] <;> simp only [Matrix.cons_val]

private theorem apply_vector_three {A B C : Type*} (f : A → B → C)
    (a0 a1 a2 : A) (b0 b1 b2 : B) (k : Fin 3) :
    ![f a0 b0, f a1 b1, f a2 b2] k =
      f (![a0,a1,a2] k) (![b0,b1,b2] k) := by
  fin_cases k <;> rfl

/-- Keep the selector proof abstract, so Lean does not expand the stored potential. -/
theorem clearedTarget_form (k : Fin 3) : clearedTarget k =
    merge (mulFast (denominatorPoly k) (merge (scale denominator cost)
      (scale (-1) (directionalPolynomial polynomial gVelocity))))
      (scale (-1) (directionalPolynomial polynomial (xVelocityPoly k))) :=
  apply_vector_three (fun r W =>
      merge (mulFast r (merge (scale denominator cost)
        (scale (-1) (directionalPolynomial polynomial gVelocity))))
        (scale (-1) (directionalPolynomial polynomial W)))
    r3_0 r3_1 r3_2 xVelocity3_0 xVelocity3_1 xVelocity3_2 k

#print axioms clearedTarget_form

theorem clearedTarget_evaluation (x : State) (k : Fin 3) :
    eval x.coordinates (clearedTarget k) =
      3*(denominator : ℝ)*(denominatorAt x (vertex k)*(x.cost-dG x)-dX x k) := by
  have hd : (denominator : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt denominator_pos)
  rw [clearedTarget_form]
  simp only [eval_merge,eval_mulFast,eval_scale,eval_directionalPolynomial,
    denominatorPoly_correct,gVelocity_correct,xVelocityPoly_correct,cost_correct]
  have hxscale : directionalValue polynomial x.coordinates (fun i => 3*xTangentNumerator x k i) =
      3*directionalValue polynomial x.coordinates (xTangentNumerator x k) := by
    unfold directionalValue
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hxscale]
  unfold dG dX
  field_simp [hd]
  <;> ring

#print axioms clearedTarget_evaluation
end Certificate.Potential
