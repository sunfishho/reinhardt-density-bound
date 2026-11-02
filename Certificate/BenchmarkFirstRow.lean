import Certificate.BenchmarkMatrix
namespace Certificate.Benchmark
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem first_row : rowCondition 0 := by decide +kernel
#print axioms first_row
end Certificate.Benchmark
