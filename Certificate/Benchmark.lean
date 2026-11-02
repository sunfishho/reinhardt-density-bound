import Certificate.BenchmarkData
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Certificate.Benchmark
/-- Full 104×104 exact residual-dominance check, reduced by the Lean kernel. -/
theorem check_full_block :
    checkGramWitness n denominator factorDenominator sqrtScale sqrtLo sqrtHi
      gramA gramB factor = true := by
  decide +kernel
#print axioms check_full_block
end Certificate.Benchmark
