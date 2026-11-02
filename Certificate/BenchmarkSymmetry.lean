import Certificate.BenchmarkMatrixLite
import Certificate.ListSymmetry
namespace Certificate.BenchmarkLite
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem list_symmetric_A : symmetric gramA = true := by decide +kernel
theorem list_symmetric_B : symmetric gramB = true := by decide +kernel

theorem symmetric_A : ∀ i j : Fin 104, A j i = A i j :=
  symmetry_of_list_check gramA (by decide +kernel) list_symmetric_A

theorem symmetric_B : ∀ i j : Fin 104, B j i = B i j :=
  symmetry_of_list_check gramB (by decide +kernel) list_symmetric_B

#print axioms symmetric_A
#print axioms symmetric_B
end Certificate.BenchmarkLite
