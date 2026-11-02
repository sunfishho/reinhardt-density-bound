import Certificate.BenchmarkFastRows
namespace Certificate.BenchmarkLite
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem fast_first_row : fastRowCondition 0 := by
  unfold fastRowCondition
  decide +kernel

theorem actual_first_row : rowCondition 0 := (rowCondition_iff_fast 0).mpr fast_first_row
#print axioms actual_first_row
end Certificate.BenchmarkLite
