import Certificate.Chunked.H1_0B000.Chunk000
namespace Certificate.Chunked.Benchmarks.H104LeafDecide
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem check : fastGramRow Certificate.Generated.H1_0B000.data Certificate.SOS.H1_0B000.basis
    (⟨103, by decide⟩ : Fin Certificate.Generated.H1_0B000.data.size) = Certificate.Chunked.H1_0B000.Leaf103.witness := by
  decide +kernel
#print axioms check
end Certificate.Chunked.Benchmarks.H104LeafDecide
