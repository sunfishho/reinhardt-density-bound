import Certificate.ChunkedExpansion
import Certificate.SOS.H2B001Data
namespace Certificate.Chunked.H2B001.Leaf000
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
noncomputable def witness_000 : Polynomial := [
  (Int.ofNat 4760259488659363856384, ⟨0, 0, 0, 0, 0, 0, 0, 0⟩),
  (Int.negSucc 15481123719086079, ⟨0, 0, 0, 0, 1, 0, 0, 0⟩),
  (Int.negSucc 312966397105044193279, ⟨0, 0, 0, 0, 0, 1, 0, 0⟩),
  (Int.negSucc 4730477747273516187647, ⟨0, 0, 0, 0, 0, 0, 1, 0⟩),
  (Int.ofNat 0, ⟨0, 0, 0, 0, 0, 0, 0, 1⟩),
  (Int.ofNat 0, ⟨0, 0, 0, 0, 1, 0, 0, 1⟩),
  (Int.ofNat 0, ⟨0, 0, 0, 0, 0, 1, 0, 1⟩),
  (Int.ofNat 0, ⟨0, 0, 0, 0, 0, 0, 1, 1⟩)]
noncomputable def witness : Polynomial := witness_000
def indices : List (Fin Certificate.Generated.H2B001.data.size) := [(⟨0, by decide⟩ : Fin Certificate.Generated.H2B001.data.size)]
theorem check : fastGramRow Certificate.Generated.H2B001.data Certificate.SOS.H2B001.basis (⟨0, by decide⟩ : Fin Certificate.Generated.H2B001.data.size) = witness := by
  decide +kernel
theorem evaluation {R : Type*} [CommRing R] (x : Fin 8 → R) :
    evalMany x (indices.map (fastGramRow Certificate.Generated.H2B001.data Certificate.SOS.H2B001.basis)) = eval x witness :=
  gram_row_leaf x Certificate.Generated.H2B001.data Certificate.SOS.H2B001.basis (⟨0, by decide⟩ : Fin Certificate.Generated.H2B001.data.size) witness check
#print axioms evaluation
end Certificate.Chunked.H2B001.Leaf000

namespace Certificate.Chunked.H2B001.Leaf001
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
noncomputable def witness_000 : Polynomial := [
  (Int.negSucc 15481123719086079, ⟨0, 0, 0, 0, 1, 0, 0, 0⟩),
  (Int.ofNat 299756494973036396544, ⟨0, 0, 0, 0, 2, 0, 0, 0⟩),
  (Int.ofNat 10696049115004928, ⟨0, 0, 0, 0, 1, 1, 0, 0⟩),
  (Int.ofNat 15199648742375424, ⟨0, 0, 0, 0, 1, 0, 1, 0⟩),
  (Int.ofNat 0, ⟨0, 0, 0, 0, 1, 0, 0, 1⟩),
  (Int.ofNat 0, ⟨0, 0, 0, 0, 2, 0, 0, 1⟩),
  (Int.ofNat 0, ⟨0, 0, 0, 0, 1, 1, 0, 1⟩),
  (Int.ofNat 0, ⟨0, 0, 0, 0, 1, 0, 1, 1⟩)]
noncomputable def witness : Polynomial := witness_000
def indices : List (Fin Certificate.Generated.H2B001.data.size) := [(⟨1, by decide⟩ : Fin Certificate.Generated.H2B001.data.size)]
theorem check : fastGramRow Certificate.Generated.H2B001.data Certificate.SOS.H2B001.basis (⟨1, by decide⟩ : Fin Certificate.Generated.H2B001.data.size) = witness := by
  decide +kernel
theorem evaluation {R : Type*} [CommRing R] (x : Fin 8 → R) :
    evalMany x (indices.map (fastGramRow Certificate.Generated.H2B001.data Certificate.SOS.H2B001.basis)) = eval x witness :=
  gram_row_leaf x Certificate.Generated.H2B001.data Certificate.SOS.H2B001.basis (⟨1, by decide⟩ : Fin Certificate.Generated.H2B001.data.size) witness check
#print axioms evaluation
end Certificate.Chunked.H2B001.Leaf001

namespace Certificate.Chunked.H2B001.Leaf002
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
noncomputable def witness_000 : Polynomial := [
  (Int.negSucc 312966397105044193279, ⟨0, 0, 0, 0, 0, 1, 0, 0⟩),
  (Int.ofNat 10696049115004928, ⟨0, 0, 0, 0, 1, 1, 0, 0⟩),
  (Int.ofNat 229703565719241752576, ⟨0, 0, 0, 0, 0, 2, 0, 0⟩),
  (Int.ofNat 311799683326578524160, ⟨0, 0, 0, 0, 0, 1, 1, 0⟩),
  (Int.ofNat 0, ⟨0, 0, 0, 0, 0, 1, 0, 1⟩),
  (Int.ofNat 0, ⟨0, 0, 0, 0, 1, 1, 0, 1⟩),
  (Int.ofNat 0, ⟨0, 0, 0, 0, 0, 2, 0, 1⟩),
  (Int.ofNat 0, ⟨0, 0, 0, 0, 0, 1, 1, 1⟩)]
noncomputable def witness : Polynomial := witness_000
def indices : List (Fin Certificate.Generated.H2B001.data.size) := [(⟨2, by decide⟩ : Fin Certificate.Generated.H2B001.data.size)]
theorem check : fastGramRow Certificate.Generated.H2B001.data Certificate.SOS.H2B001.basis (⟨2, by decide⟩ : Fin Certificate.Generated.H2B001.data.size) = witness := by
  decide +kernel
theorem evaluation {R : Type*} [CommRing R] (x : Fin 8 → R) :
    evalMany x (indices.map (fastGramRow Certificate.Generated.H2B001.data Certificate.SOS.H2B001.basis)) = eval x witness :=
  gram_row_leaf x Certificate.Generated.H2B001.data Certificate.SOS.H2B001.basis (⟨2, by decide⟩ : Fin Certificate.Generated.H2B001.data.size) witness check
#print axioms evaluation
end Certificate.Chunked.H2B001.Leaf002

namespace Certificate.Chunked.H2B001.Leaf003
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
noncomputable def witness_000 : Polynomial := [
  (Int.negSucc 4730477747273516187647, ⟨0, 0, 0, 0, 0, 0, 1, 0⟩),
  (Int.ofNat 15199648742375424, ⟨0, 0, 0, 0, 1, 0, 1, 0⟩),
  (Int.ofNat 311799683326578524160, ⟨0, 0, 0, 0, 0, 1, 1, 0⟩),
  (Int.ofNat 4732313808546599796736, ⟨0, 0, 0, 0, 0, 0, 2, 0⟩),
  (Int.ofNat 0, ⟨0, 0, 0, 0, 0, 0, 1, 1⟩),
  (Int.ofNat 0, ⟨0, 0, 0, 0, 1, 0, 1, 1⟩),
  (Int.ofNat 0, ⟨0, 0, 0, 0, 0, 1, 1, 1⟩),
  (Int.ofNat 0, ⟨0, 0, 0, 0, 0, 0, 2, 1⟩)]
noncomputable def witness : Polynomial := witness_000
def indices : List (Fin Certificate.Generated.H2B001.data.size) := [(⟨3, by decide⟩ : Fin Certificate.Generated.H2B001.data.size)]
theorem check : fastGramRow Certificate.Generated.H2B001.data Certificate.SOS.H2B001.basis (⟨3, by decide⟩ : Fin Certificate.Generated.H2B001.data.size) = witness := by
  decide +kernel
theorem evaluation {R : Type*} [CommRing R] (x : Fin 8 → R) :
    evalMany x (indices.map (fastGramRow Certificate.Generated.H2B001.data Certificate.SOS.H2B001.basis)) = eval x witness :=
  gram_row_leaf x Certificate.Generated.H2B001.data Certificate.SOS.H2B001.basis (⟨3, by decide⟩ : Fin Certificate.Generated.H2B001.data.size) witness check
#print axioms evaluation
end Certificate.Chunked.H2B001.Leaf003

namespace Certificate.Chunked.H2B001.Node000
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
noncomputable def witness_000 : Polynomial := [
  (Int.ofNat 4760259488659363856384, ⟨0, 0, 0, 0, 0, 0, 0, 0⟩),
  (Int.negSucc 30962247438172159, ⟨0, 0, 0, 0, 1, 0, 0, 0⟩),
  (Int.ofNat 299756494973036396544, ⟨0, 0, 0, 0, 2, 0, 0, 0⟩),
  (Int.negSucc 312966397105044193279, ⟨0, 0, 0, 0, 0, 1, 0, 0⟩),
  (Int.ofNat 10696049115004928, ⟨0, 0, 0, 0, 1, 1, 0, 0⟩),
  (Int.negSucc 4730477747273516187647, ⟨0, 0, 0, 0, 0, 0, 1, 0⟩),
  (Int.ofNat 15199648742375424, ⟨0, 0, 0, 0, 1, 0, 1, 0⟩),
  (Int.ofNat 0, ⟨0, 0, 0, 0, 0, 0, 0, 1⟩),
  (Int.ofNat 0, ⟨0, 0, 0, 0, 1, 0, 0, 1⟩),
  (Int.ofNat 0, ⟨0, 0, 0, 0, 2, 0, 0, 1⟩),
  (Int.ofNat 0, ⟨0, 0, 0, 0, 0, 1, 0, 1⟩),
  (Int.ofNat 0, ⟨0, 0, 0, 0, 1, 1, 0, 1⟩),
  (Int.ofNat 0, ⟨0, 0, 0, 0, 0, 0, 1, 1⟩),
  (Int.ofNat 0, ⟨0, 0, 0, 0, 1, 0, 1, 1⟩)]
noncomputable def witness : Polynomial := witness_000
def indices : List (Fin Certificate.Generated.H2B001.data.size) := Leaf000.indices ++ Leaf001.indices
theorem check : merge Leaf000.witness Leaf001.witness = witness := by
  decide +kernel
theorem evaluation {R : Type*} [CommRing R] (x : Fin 8 → R) :
    evalMany x (indices.map (fastGramRow Certificate.Generated.H2B001.data Certificate.SOS.H2B001.basis)) = eval x witness :=
  gram_rows_join x Certificate.Generated.H2B001.data Certificate.SOS.H2B001.basis Leaf000.indices Leaf001.indices
    Leaf000.witness Leaf001.witness witness (Leaf000.evaluation x) (Leaf001.evaluation x) check
#print axioms evaluation
end Certificate.Chunked.H2B001.Node000

namespace Certificate.Chunked.H2B001.Node001
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
noncomputable def witness_000 : Polynomial := [
  (Int.negSucc 312966397105044193279, ⟨0, 0, 0, 0, 0, 1, 0, 0⟩),
  (Int.ofNat 10696049115004928, ⟨0, 0, 0, 0, 1, 1, 0, 0⟩),
  (Int.ofNat 229703565719241752576, ⟨0, 0, 0, 0, 0, 2, 0, 0⟩),
  (Int.negSucc 4730477747273516187647, ⟨0, 0, 0, 0, 0, 0, 1, 0⟩),
  (Int.ofNat 15199648742375424, ⟨0, 0, 0, 0, 1, 0, 1, 0⟩),
  (Int.ofNat 623599366653157048320, ⟨0, 0, 0, 0, 0, 1, 1, 0⟩),
  (Int.ofNat 4732313808546599796736, ⟨0, 0, 0, 0, 0, 0, 2, 0⟩),
  (Int.ofNat 0, ⟨0, 0, 0, 0, 0, 1, 0, 1⟩),
  (Int.ofNat 0, ⟨0, 0, 0, 0, 1, 1, 0, 1⟩),
  (Int.ofNat 0, ⟨0, 0, 0, 0, 0, 2, 0, 1⟩),
  (Int.ofNat 0, ⟨0, 0, 0, 0, 0, 0, 1, 1⟩),
  (Int.ofNat 0, ⟨0, 0, 0, 0, 1, 0, 1, 1⟩),
  (Int.ofNat 0, ⟨0, 0, 0, 0, 0, 1, 1, 1⟩),
  (Int.ofNat 0, ⟨0, 0, 0, 0, 0, 0, 2, 1⟩)]
noncomputable def witness : Polynomial := witness_000
def indices : List (Fin Certificate.Generated.H2B001.data.size) := Leaf002.indices ++ Leaf003.indices
theorem check : merge Leaf002.witness Leaf003.witness = witness := by
  decide +kernel
theorem evaluation {R : Type*} [CommRing R] (x : Fin 8 → R) :
    evalMany x (indices.map (fastGramRow Certificate.Generated.H2B001.data Certificate.SOS.H2B001.basis)) = eval x witness :=
  gram_rows_join x Certificate.Generated.H2B001.data Certificate.SOS.H2B001.basis Leaf002.indices Leaf003.indices
    Leaf002.witness Leaf003.witness witness (Leaf002.evaluation x) (Leaf003.evaluation x) check
#print axioms evaluation
end Certificate.Chunked.H2B001.Node001

namespace Certificate.Chunked.H2B001.Node002
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
noncomputable def witness_000 : Polynomial := [
  (Int.ofNat 4760259488659363856384, ⟨0, 0, 0, 0, 0, 0, 0, 0⟩),
  (Int.negSucc 30962247438172159, ⟨0, 0, 0, 0, 1, 0, 0, 0⟩),
  (Int.ofNat 299756494973036396544, ⟨0, 0, 0, 0, 2, 0, 0, 0⟩),
  (Int.negSucc 625932794210088386559, ⟨0, 0, 0, 0, 0, 1, 0, 0⟩),
  (Int.ofNat 21392098230009856, ⟨0, 0, 0, 0, 1, 1, 0, 0⟩),
  (Int.ofNat 229703565719241752576, ⟨0, 0, 0, 0, 0, 2, 0, 0⟩),
  (Int.negSucc 9460955494547032375295, ⟨0, 0, 0, 0, 0, 0, 1, 0⟩),
  (Int.ofNat 30399297484750848, ⟨0, 0, 0, 0, 1, 0, 1, 0⟩),
  (Int.ofNat 623599366653157048320, ⟨0, 0, 0, 0, 0, 1, 1, 0⟩),
  (Int.ofNat 4732313808546599796736, ⟨0, 0, 0, 0, 0, 0, 2, 0⟩),
  (Int.ofNat 0, ⟨0, 0, 0, 0, 0, 0, 0, 1⟩),
  (Int.ofNat 0, ⟨0, 0, 0, 0, 1, 0, 0, 1⟩),
  (Int.ofNat 0, ⟨0, 0, 0, 0, 2, 0, 0, 1⟩),
  (Int.ofNat 0, ⟨0, 0, 0, 0, 0, 1, 0, 1⟩),
  (Int.ofNat 0, ⟨0, 0, 0, 0, 1, 1, 0, 1⟩),
  (Int.ofNat 0, ⟨0, 0, 0, 0, 0, 2, 0, 1⟩),
  (Int.ofNat 0, ⟨0, 0, 0, 0, 0, 0, 1, 1⟩),
  (Int.ofNat 0, ⟨0, 0, 0, 0, 1, 0, 1, 1⟩),
  (Int.ofNat 0, ⟨0, 0, 0, 0, 0, 1, 1, 1⟩),
  (Int.ofNat 0, ⟨0, 0, 0, 0, 0, 0, 2, 1⟩)]
noncomputable def witness : Polynomial := witness_000
def indices : List (Fin Certificate.Generated.H2B001.data.size) := Node000.indices ++ Node001.indices
theorem check : merge Node000.witness Node001.witness = witness := by
  decide +kernel
theorem evaluation {R : Type*} [CommRing R] (x : Fin 8 → R) :
    evalMany x (indices.map (fastGramRow Certificate.Generated.H2B001.data Certificate.SOS.H2B001.basis)) = eval x witness :=
  gram_rows_join x Certificate.Generated.H2B001.data Certificate.SOS.H2B001.basis Node000.indices Node001.indices
    Node000.witness Node001.witness witness (Node000.evaluation x) (Node001.evaluation x) check
#print axioms evaluation
end Certificate.Chunked.H2B001.Node002
