import Certificate.PolynomialDerivative
namespace Certificate.Sparse
open scoped BigOperators

theorem directionalValue_add (p : Polynomial) (x v w : Fin 8 → ℝ) :
    directionalValue p x (fun i => v i+w i) = directionalValue p x v+directionalValue p x w := by
  simp only [directionalValue,mul_add,Finset.sum_add_distrib]

theorem directionalValue_scale (p : Polynomial) (x v : Fin 8 → ℝ) (c : ℝ) :
    directionalValue p x (fun i => c*v i) = c*directionalValue p x v := by
  unfold directionalValue
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem directionalValue_sum (p : Polynomial) (x : Fin 8 → ℝ)
    {n : ℕ} (v : Fin n → Fin 8 → ℝ) :
    directionalValue p x (fun i => ∑ k, v k i) = ∑ k, directionalValue p x (v k) := by
  simp only [directionalValue,Finset.mul_sum]
  exact Finset.sum_comm

#print axioms directionalValue_sum
end Certificate.Sparse
