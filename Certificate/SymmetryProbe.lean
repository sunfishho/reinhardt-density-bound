import Certificate.BenchmarkFastRows
namespace Certificate.BenchmarkLite
set_option maxHeartbeats 0
set_option maxRecDepth 100000
#synth Decidable (∀ i j : Fin 2, (0 : ℤ) = 0)
#synth Decidable (∀ i j : Fin 104, A j i = A i j)
theorem symmetryA : ∀ i j : Fin 104, A j i = A i j := by
  unfold A
  decide +kernel
end Certificate.BenchmarkLite
