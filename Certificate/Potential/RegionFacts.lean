import Certificate.Potential.DifferentialSemantics
import Certificate.PrimitiveData
namespace Certificate.Potential
open Certificate.Sparse
set_option maxHeartbeats 0
theorem region_denominator_0 (x : State) (hx : PrimitiveData.Region x.coordinates) :
    (769 : ℝ)/10000 ≤ denominatorAt x (vertex 0) := by
  have h := hx .denominator0
  change 0 ≤ eval x.coordinates PrimitiveData.denominator0 at h
  norm_num [PrimitiveData.denominator0,eval,Exponent.eval,State.coordinates] at h
  simp only [Matrix.cons_val] at h
  have he := denominatorPoly_correct x 0
  change eval x.coordinates r3_0 = 3*denominatorAt x (vertex 0) at he
  norm_num [r3_0,eval,Exponent.eval,State.coordinates] at he
  simp only [Matrix.cons_val] at he
  nlinarith only [h,he]
theorem region_denominator_1 (x : State) (hx : PrimitiveData.Region x.coordinates) :
    (769 : ℝ)/10000 ≤ denominatorAt x (vertex 1) := by
  have h := hx .denominator1
  change 0 ≤ eval x.coordinates PrimitiveData.denominator1 at h
  norm_num [PrimitiveData.denominator1,eval,Exponent.eval,State.coordinates] at h
  simp only [Matrix.cons_val] at h
  have he := denominatorPoly_correct x 1
  change eval x.coordinates r3_1 = 3*denominatorAt x (vertex 1) at he
  norm_num [r3_1,eval,Exponent.eval,State.coordinates] at he
  simp only [Matrix.cons_val] at he
  nlinarith only [h,he]
theorem region_denominator_2 (x : State) (hx : PrimitiveData.Region x.coordinates) :
    (769 : ℝ)/10000 ≤ denominatorAt x (vertex 2) := by
  have h := hx .denominator2
  change 0 ≤ eval x.coordinates PrimitiveData.denominator2 at h
  norm_num [PrimitiveData.denominator2,eval,Exponent.eval,State.coordinates] at h
  simp only [Matrix.cons_val] at h
  have he := denominatorPoly_correct x 2
  change eval x.coordinates r3_2 = 3*denominatorAt x (vertex 2) at he
  norm_num [r3_2,eval,Exponent.eval,State.coordinates] at he
  simp only [Matrix.cons_val] at he
  nlinarith only [h,he]
theorem region_denominator (x : State) (hx : PrimitiveData.Region x.coordinates) (k : Fin 3) :
    (769 : ℝ)/10000 ≤ denominatorAt x (vertex k) := by
  fin_cases k
  · exact region_denominator_0 x hx
  · exact region_denominator_1 x hx
  · exact region_denominator_2 x hx
#print axioms region_denominator
end Certificate.Potential
