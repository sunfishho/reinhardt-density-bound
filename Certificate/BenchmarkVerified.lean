import Certificate.BenchmarkRows
import Certificate.BenchmarkSymmetry
namespace Certificate.BenchmarkLite
set_option maxHeartbeats 0
set_option maxRecDepth 100000
/-- The actual reconstructed 104×104 Gram block is positive semidefinite over ℝ. -/
theorem block0_posSemidef : (realGram A B denominator).PosSemidef := by
  apply gram_certificate_sound A B L denominator c sqrtScale sqrtLo sqrtHi
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact symmetric_A
  · exact symmetric_B
  · exact actual_all_rows

#print axioms block0_posSemidef
end Certificate.BenchmarkLite
