import Certificate.BenchmarkMatrixLite
namespace Certificate.BenchmarkLite
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option cbv.maxSteps 10000000
theorem first_row : rowCondition 0 := by
  unfold rowCondition
  decide_cbv
#print axioms first_row
end Certificate.BenchmarkLite
