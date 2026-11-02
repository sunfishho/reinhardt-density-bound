import Certificate.Potential.DifferentialSemantics
import Certificate.DirectionalLinearity
namespace Certificate.Potential
open Certificate.Sparse
open scoped BigOperators
set_option maxHeartbeats 0

noncomputable def controlDenominator (x : State) (u : Fin 3 → ℝ) : ℝ :=
  ∑ k, u k*denominatorAt x (vertex k)
noncomputable def controlTangent (x : State) (u : Fin 3 → ℝ) : Fin 8 → ℝ :=
  fun i => gTangent x i+(controlDenominator x u)⁻¹*(∑ k, u k*xTangentNumerator x k i)

theorem directional_control (x : State) (u : Fin 3 → ℝ) :
    directionalValue polynomial x.coordinates (controlTangent x u) / denominator =
      dG x+(∑ k, u k*dX x k)/controlDenominator x u := by
  unfold controlTangent
  rw [directionalValue_add,directionalValue_scale,directionalValue_sum]
  simp only [directionalValue_scale]
  unfold dG dX
  simp only [div_eq_mul_inv,Finset.mul_sum,Finset.sum_mul]
  rw [add_mul]
  congr 1
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  ring

/-- The derivative in the original normalized control coordinates, with the
actual stored potential. -/
theorem path_control_derivative (x : ℝ → State) (u : Fin 3 → ℝ) (s : ℝ)
    (hx : ∀ i, HasDerivAt (fun t => (x t).coordinates i) (controlTangent (x s) u i) s) :
    HasDerivAt (fun t => stateValue (x t))
      (dG (x s)+(∑ k, u k*dX (x s) k)/controlDenominator (x s) u) s := by
  have hd := path_hasDerivAt (fun t => (x t).coordinates) (controlTangent (x s) u) s hx
  rw [directional_control] at hd
  exact hd

#print axioms path_control_derivative
end Certificate.Potential
