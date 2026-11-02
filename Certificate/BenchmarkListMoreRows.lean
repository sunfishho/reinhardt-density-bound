import Certificate.BenchmarkListRow
namespace Certificate.BenchmarkLite
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
theorem list_middle_row :
    checkRow 51 gramA_51 gramB_51 factor
      (denominator / (factorDenominator * factorDenominator)) sqrtScale sqrtLo sqrtHi = true := by
  decide +kernel
#print axioms list_middle_row
theorem list_last_row :
    checkRow 103 gramA_103 gramB_103 factor
      (denominator / (factorDenominator * factorDenominator)) sqrtScale sqrtLo sqrtHi = true := by
  decide +kernel
#print axioms list_last_row
end Certificate.BenchmarkLite
