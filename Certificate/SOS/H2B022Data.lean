import Certificate.Generated.H2B022Data
import Certificate.SOSPolynomial
namespace Certificate.SOS.H2B022
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def basisList : List Exponent := [⟨0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0⟩]
noncomputable def basis : Fin Certificate.Generated.H2B022.data.size → Exponent := fun i => basisList.getD i.val ⟨0,0,0,0,0,0,0,0⟩
noncomputable def gram_0 : Polynomial := [
  (Int.ofNat 16262046768572217163776, ⟨0, 0, 0, 0, 0, 0, 0, 0⟩),
  (Int.ofNat 2814749767106560, ⟨0, 0, 0, 0, 1, 0, 0, 0⟩),
  (Int.ofNat 14828331175223377264640, ⟨0, 0, 0, 0, 2, 0, 0, 0⟩),
  (Int.negSucc 455765408189801037823, ⟨0, 0, 0, 0, 0, 1, 0, 0⟩),
  (Int.ofNat 36028797018963968, ⟨0, 0, 0, 0, 1, 1, 0, 0⟩),
  (Int.ofNat 14490672104311414063104, ⟨0, 0, 0, 0, 0, 2, 0, 0⟩),
  (Int.negSucc 32315920273868767363071, ⟨0, 0, 0, 0, 0, 0, 1, 0⟩),
  (Int.negSucc 2814749767106559, ⟨0, 0, 0, 0, 1, 0, 1, 0⟩),
  (Int.ofNat 289920351911882522624, ⟨0, 0, 0, 0, 0, 1, 1, 0⟩),
  (Int.ofNat 16188962353819248754688, ⟨0, 0, 0, 0, 0, 0, 2, 0⟩)]
noncomputable def gram : Polynomial := gram_0
noncomputable def multiplier_0 : Polynomial := [
  (Int.negSucc 11, ⟨0, 0, 0, 0, 0, 0, 0, 0⟩),
  (Int.ofNat 17, ⟨0, 0, 0, 0, 0, 0, 1, 0⟩),
  (Int.negSucc 4, ⟨0, 0, 0, 0, 0, 0, 2, 0⟩)]
noncomputable def multiplier : Polynomial := multiplier_0
noncomputable def weighted_0 : Polynomial := [
  (Int.negSucc 195144561222866605965311, ⟨0, 0, 0, 0, 0, 0, 0, 0⟩),
  (Int.negSucc 33776997205278719, ⟨0, 0, 0, 0, 1, 0, 0, 0⟩),
  (Int.negSucc 177939974102680527175679, ⟨0, 0, 0, 0, 2, 0, 0, 0⟩),
  (Int.ofNat 5469184898277612453888, ⟨0, 0, 0, 0, 0, 1, 0, 0⟩),
  (Int.negSucc 432345564227567615, ⟨0, 0, 0, 0, 1, 1, 0, 0⟩),
  (Int.negSucc 173888065251736968757247, ⟨0, 0, 0, 0, 0, 2, 0, 0⟩),
  (Int.ofNat 664245838352152900141056, ⟨0, 0, 0, 0, 0, 0, 1, 0⟩),
  (Int.ofNat 81627743246090240, ⟨0, 0, 0, 0, 1, 0, 1, 0⟩),
  (Int.ofNat 252081629978797413498880, ⟨0, 0, 0, 0, 2, 0, 1, 0⟩),
  (Int.negSucc 11227056162169207914495, ⟨0, 0, 0, 0, 0, 1, 1, 0⟩),
  (Int.ofNat 612489549322387456, ⟨0, 0, 0, 0, 1, 1, 1, 0⟩),
  (Int.ofNat 246341425773294039072768, ⟨0, 0, 0, 0, 0, 2, 1, 0⟩),
  (Int.negSucc 824948426744461116047359, ⟨0, 0, 0, 0, 0, 0, 2, 0⟩),
  (Int.negSucc 61924494876344319, ⟨0, 0, 0, 0, 1, 0, 2, 0⟩),
  (Int.negSucc 74141655876116886323199, ⟨0, 0, 0, 0, 2, 0, 2, 0⟩),
  (Int.ofNat 7207473023451008073728, ⟨0, 0, 0, 0, 0, 1, 2, 0⟩),
  (Int.negSucc 180143985094819839, ⟨0, 0, 0, 0, 1, 1, 2, 0⟩),
  (Int.negSucc 72453360521557070315519, ⟨0, 0, 0, 0, 0, 2, 2, 0⟩),
  (Int.ofNat 436791961384271065645056, ⟨0, 0, 0, 0, 0, 0, 3, 0⟩),
  (Int.ofNat 14073748835532800, ⟨0, 0, 0, 0, 1, 0, 3, 0⟩),
  (Int.negSucc 1449601759559412613119, ⟨0, 0, 0, 0, 0, 1, 3, 0⟩),
  (Int.negSucc 80944811769096243773439, ⟨0, 0, 0, 0, 0, 0, 4, 0⟩)]
noncomputable def weighted : Polynomial := weighted_0
noncomputable def weight : ℤ := 540000000
end Certificate.SOS.H2B022
