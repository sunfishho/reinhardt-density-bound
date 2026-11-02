import Certificate.Chunked.H2B001.Chunk000
import Certificate.MergeArithmetic
namespace Certificate.Chunked.H2B001
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
theorem coverage : Node002.indices = List.ofFn (fun i : Fin Certificate.Generated.H2B001.data.size => i) := by
  decide +kernel
theorem final_check : checkEqualMerged Node002.witness Certificate.SOS.H2B001.gram = true := by
  decide +kernel
theorem gram_evaluation {R : Type*} [CommRing R] (x : Fin 8 → R) :
    eval x (gramPolynomial Certificate.Generated.H2B001.data Certificate.SOS.H2B001.basis) = eval x Certificate.SOS.H2B001.gram := by
  exact (gram_expansion_of_tree x Certificate.Generated.H2B001.data Certificate.SOS.H2B001.basis Node002.indices
    Node002.witness coverage (Node002.evaluation x)).trans
    (eq_of_checkMerged x _ _ final_check)
theorem gram_nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hden : 0 < Certificate.Generated.H2B001.data.den)
    (hPSD : (realGram Certificate.Generated.H2B001.data.A Certificate.Generated.H2B001.data.B Certificate.Generated.H2B001.data.den).PosSemidef) :
    0 ≤ eval x Certificate.SOS.H2B001.gram := by
  rw [← gram_evaluation]
  exact eval_gramPolynomial_nonneg x hx Certificate.Generated.H2B001.data Certificate.SOS.H2B001.basis hden hPSD
#print axioms gram_evaluation
#print axioms gram_nonnegative
end Certificate.Chunked.H2B001
