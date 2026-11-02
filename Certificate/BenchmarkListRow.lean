import Certificate.BenchmarkDataLite
namespace Certificate.BenchmarkLite
set_option maxRecDepth 100000
set_option maxHeartbeats 0
/-- A performance probe for the original list checker, not yet a real PSD theorem. -/
theorem list_first_row :
    checkRow 0 gramA_0 gramB_0 factor
      (denominator / (factorDenominator * factorDenominator)) sqrtScale sqrtLo sqrtHi = true := by
  decide +kernel
#print axioms list_first_row
end Certificate.BenchmarkLite
