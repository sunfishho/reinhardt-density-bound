import Certificate.Chunked.H1_0B000.Chunk001
namespace Certificate.Chunked.Benchmarks.H104MergeRfl
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem check : merge Certificate.Chunked.H1_0B000.Node100.witness Certificate.Chunked.H1_0B000.Node101.witness = Certificate.Chunked.H1_0B000.Node102.witness := by
  rfl
#print axioms check
end Certificate.Chunked.Benchmarks.H104MergeRfl
