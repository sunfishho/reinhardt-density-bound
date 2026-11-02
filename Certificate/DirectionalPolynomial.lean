import Certificate.PolynomialDerivative
import Certificate.SOSPolynomial
namespace Certificate.Sparse
noncomputable def directionalPolynomial (p : Polynomial) (v : Fin 8 → Polynomial) : Polynomial :=
  polynomialSum (fun i => mulFast (partialPoly p i) (v i))

theorem eval_directionalPolynomial (p : Polynomial) (v : Fin 8 → Polynomial) (x : Fin 8 → ℝ) :
    eval x (directionalPolynomial p v) = directionalValue p x (fun i => eval x (v i)) := by
  simp only [directionalPolynomial,eval_polynomialSum,eval_mulFast,directionalValue]
#print axioms eval_directionalPolynomial
end Certificate.Sparse
