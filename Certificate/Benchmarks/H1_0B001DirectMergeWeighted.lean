import Certificate.SOS.H1_0B001Data
import Certificate.FastExpansion
import Certificate.MergeArithmetic
import Certificate.SparseExpansion
namespace Certificate.Benchmarks.H1_0B001DirectMergeWeighted
open Certificate.Sparse Certificate.SOS.H1_0B001
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
theorem checked : checkEqualMerged (mulMerged gram multiplier) weighted = true := by decide +kernel
#print axioms checked
end Certificate.Benchmarks.H1_0B001DirectMergeWeighted
