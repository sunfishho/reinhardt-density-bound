import Certificate.Potential.Data
import Certificate.GeometricCoordinates
import Certificate.PolynomialRegularity

namespace Certificate.Potential
open Certificate.Sparse
set_option maxHeartbeats 0

noncomputable def stateValue (x : State) : ℝ := value x.coordinates

@[simp] theorem coordinate_0 (x : State) : x.coordinates 0 = x.g11 := rfl
@[simp] theorem coordinate_1 (x : State) : x.coordinates 1 = x.g12 := rfl
@[simp] theorem coordinate_2 (x : State) : x.coordinates 2 = x.g21 := rfl
@[simp] theorem coordinate_3 (x : State) : x.coordinates 3 = x.g22 := rfl
@[simp] theorem coordinate_4 (x : State) : x.coordinates 4 = x.a := rfl
@[simp] theorem coordinate_5 (x : State) : x.coordinates 5 = x.p := rfl
@[simp] theorem coordinate_6 (x : State) : x.coordinates 6 = x.h := rfl
@[simp] theorem coordinate_7 (x : State) : x.coordinates 7 = Real.sqrt 3 := rfl

theorem rotatedCoordinates_correct (x : State) (i : Fin 8) :
    eval x.coordinates (rotatedCoordinates2 i) = 2*(rotateState x).coordinates i := by
  fin_cases i <;>
    norm_num [rotatedCoordinates2,eval,Exponent.eval,State.coordinates,rotateState,Matrix.cons_val] <;> simp only [Matrix.cons_val] <;> ring

theorem initialCoordinates_correct (x : State) (i : Fin 8) :
    eval x.coordinates (initialCoordinates2 i) = 2*(initialState x).coordinates i := by
  fin_cases i <;>
    norm_num [initialCoordinates2,eval,Exponent.eval,State.coordinates,initialState,Matrix.cons_val] <;> simp only [Matrix.cons_val] <;> ring

/-- The boundary expression is exactly the change of the stored potential under
`g(0)=I`, `g(T)=R`, `X(T)=R⁻¹X(0)R`; no boundary inequality is assumed here. -/
theorem boundary_evaluation (x : State) :
    eval x.coordinates boundaryTarget =
      16*(denominator : ℝ)*(stateValue (rotateState x)-stateValue (initialState x)) := by
  have hR := eval_scaledSubstitute x.coordinates (rotateState x).coordinates
    polynomial rotatedCoordinates2 2 4 degree_bound (rotatedCoordinates_correct x)
  have hI := eval_scaledSubstitute x.coordinates (initialState x).coordinates
    polynomial initialCoordinates2 2 4 degree_bound (initialCoordinates_correct x)
  have hd : (denominator : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt denominator_pos)
  simp only [boundaryTarget,eval_merge,eval_scale,hR,hI]
  unfold stateValue value
  field_simp [hd]
  <;> ring

/-- The potential is absolutely continuous for absolutely continuous coordinate paths. -/
theorem path_absolutelyContinuous (x : ℝ → Fin 8 → ℝ) (a b : ℝ)
    (hx : ∀ i, AbsolutelyContinuousOnInterval (fun t => x t i) a b) :
    AbsolutelyContinuousOnInterval (fun t => value (x t)) a b :=
  absolutelyContinuous_potential polynomial (denominator : ℝ) x a b hx

/-- Exact chain rule for this particular stored potential. -/
theorem path_hasDerivAt (x : ℝ → Fin 8 → ℝ) (v : Fin 8 → ℝ) (s : ℝ)
    (hx : ∀ i, HasDerivAt (fun t => x t i) (v i) s) :
    HasDerivAt (fun t => value (x t))
      (directionalValue polynomial (x s) v / denominator) s :=
  (hasDerivAt_eval polynomial x v s hx).div_const _

#print axioms boundary_evaluation
#print axioms path_absolutelyContinuous
#print axioms path_hasDerivAt
end Certificate.Potential
