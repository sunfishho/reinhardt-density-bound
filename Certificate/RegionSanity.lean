import Certificate.PrimitiveData
import Certificate.GeometricCoordinates

namespace Certificate
open Sparse

/-- The normalized circle's initial state is an explicit point of the certificate
region. This checks that the region assumptions are jointly satisfiable. -/
noncomputable def circleInitial : State := ⟨1, 0, 0, 1, 0, 0, 1⟩

theorem circleInitial_determinants : circleInitial.determinantConstraints := by
  norm_num [circleInitial, State.determinantConstraints]

theorem circleInitial_region : PrimitiveData.Region circleInitial.coordinates := by
  have hs : 1 ≤ Real.sqrt (3 : ℝ) := by
    have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
    have hpos := Real.sqrt_nonneg (3 : ℝ)
    nlinarith
  intro label
  cases label <;>
    norm_num [PrimitiveData.polynomial, PrimitiveData.sector1, PrimitiveData.sector2,
      PrimitiveData.sector1Rot1, PrimitiveData.sector2Rot1,
      PrimitiveData.sector1Rot2, PrimitiveData.sector2Rot2, PrimitiveData.gNorm,
      PrimitiveData.denominator0, PrimitiveData.denominator1, PrimitiveData.denominator2,
      PrimitiveData.hLower, PrimitiveData.hUpper, PrimitiveData.xNorm,
      PrimitiveData.horoballY, PrimitiveData.horoballPlus, PrimitiveData.horoballMinus,
      PrimitiveData.halfplane0, PrimitiveData.halfplane1, PrimitiveData.halfplane2,
      State.coordinates, circleInitial, eval, Exponent.eval, Matrix.cons_val] <;>
    simp only [Matrix.cons_val] <;> norm_num <;>
    nlinarith only [hs]

#print axioms circleInitial_region
end Certificate
