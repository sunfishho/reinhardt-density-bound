import Certificate.SOS.H1_1B043Data
import Certificate.FastExpansion
import Certificate.MergeArithmetic
import Certificate.SparseExpansion
namespace Certificate.Benchmarks.H1_1B043DirectMergeWeighted
open Certificate.Sparse Certificate.SOS.H1_1B043
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
theorem checked : checkEqualMerged (mulMerged gram multiplier) weighted = true := by decide +kernel
#print axioms checked
end Certificate.Benchmarks.H1_1B043DirectMergeWeighted
