import Certificate.Generated.H2B011Data
import Certificate.SOSPolynomial
namespace Certificate.SOS.H2B011
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def basisList : List Exponent := [⟨0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0⟩]
noncomputable def basis : Fin Certificate.Generated.H2B011.data.size → Exponent := fun i => basisList.getD i.val ⟨0,0,0,0,0,0,0,0⟩
noncomputable def gram_0 : Polynomial := [
  (Int.ofNat 390192716140309905408, ⟨0, 0, 0, 0, 0, 0, 0, 0⟩),
  (Int.negSucc 2251799813685247, ⟨0, 0, 0, 0, 1, 0, 0, 0⟩),
  (Int.ofNat 37385506406709329920, ⟨0, 0, 0, 0, 2, 0, 0, 0⟩),
  (Int.negSucc 49814315478345056255, ⟨0, 0, 0, 0, 0, 1, 0, 0⟩),
  (Int.ofNat 1688849860263936, ⟨0, 0, 0, 0, 1, 1, 0, 0⟩),
  (Int.ofNat 32038607749113708544, ⟨0, 0, 0, 0, 0, 2, 0, 0⟩),
  (Int.negSucc 747162940779461083135, ⟨0, 0, 0, 0, 0, 0, 1, 0⟩),
  (Int.ofNat 2251799813685248, ⟨0, 0, 0, 0, 1, 0, 1, 0⟩),
  (Int.ofNat 49629104943669444608, ⟨0, 0, 0, 0, 0, 1, 1, 0⟩),
  (Int.ofNat 387970471199179276288, ⟨0, 0, 0, 0, 0, 0, 2, 0⟩)]
noncomputable def gram : Polynomial := gram_0
noncomputable def multiplier_0 : Polynomial := [
  (Int.negSucc 0, ⟨0, 0, 0, 0, 0, 0, 0, 0⟩),
  (Int.negSucc 9, ⟨0, 0, 0, 0, 0, 1, 0, 1⟩),
  (Int.ofNat 5, ⟨0, 0, 0, 0, 0, 0, 1, 1⟩)]
noncomputable def multiplier : Polynomial := multiplier_0
noncomputable def weighted_0 : Polynomial := [
  (Int.negSucc 390192716140309905407, ⟨0, 0, 0, 0, 0, 0, 0, 0⟩),
  (Int.ofNat 2251799813685248, ⟨0, 0, 0, 0, 1, 0, 0, 0⟩),
  (Int.negSucc 37385506406709329919, ⟨0, 0, 0, 0, 2, 0, 0, 0⟩),
  (Int.ofNat 49814315478345056256, ⟨0, 0, 0, 0, 0, 1, 0, 0⟩),
  (Int.negSucc 1688849860263935, ⟨0, 0, 0, 0, 1, 1, 0, 0⟩),
  (Int.negSucc 32038607749113708543, ⟨0, 0, 0, 0, 0, 2, 0, 0⟩),
  (Int.ofNat 747162940779461083136, ⟨0, 0, 0, 0, 0, 0, 1, 0⟩),
  (Int.negSucc 2251799813685247, ⟨0, 0, 0, 0, 1, 0, 1, 0⟩),
  (Int.negSucc 49629104943669444607, ⟨0, 0, 0, 0, 0, 1, 1, 0⟩),
  (Int.negSucc 387970471199179276287, ⟨0, 0, 0, 0, 0, 0, 2, 0⟩),
  (Int.negSucc 3901927161403099054079, ⟨0, 0, 0, 0, 0, 1, 0, 1⟩),
  (Int.ofNat 22517998136852480, ⟨0, 0, 0, 0, 1, 1, 0, 1⟩),
  (Int.negSucc 373855064067093299199, ⟨0, 0, 0, 0, 2, 1, 0, 1⟩),
  (Int.ofNat 498143154783450562560, ⟨0, 0, 0, 0, 0, 2, 0, 1⟩),
  (Int.negSucc 16888498602639359, ⟨0, 0, 0, 0, 1, 2, 0, 1⟩),
  (Int.negSucc 320386077491137085439, ⟨0, 0, 0, 0, 0, 3, 0, 1⟩),
  (Int.ofNat 1950963580701549527040, ⟨0, 0, 0, 0, 0, 0, 1, 1⟩),
  (Int.negSucc 11258999068426239, ⟨0, 0, 0, 0, 1, 0, 1, 1⟩),
  (Int.ofNat 186927532033546649600, ⟨0, 0, 0, 0, 2, 0, 1, 1⟩),
  (Int.ofNat 7222557830402885550080, ⟨0, 0, 0, 0, 0, 1, 1, 1⟩),
  (Int.negSucc 14073748835532799, ⟨0, 0, 0, 0, 1, 1, 1, 1⟩),
  (Int.negSucc 336098010691125903359, ⟨0, 0, 0, 0, 0, 2, 1, 1⟩),
  (Int.negSucc 3735814703897305415679, ⟨0, 0, 0, 0, 0, 0, 2, 1⟩),
  (Int.ofNat 11258999068426240, ⟨0, 0, 0, 0, 1, 0, 2, 1⟩),
  (Int.negSucc 3631559187273445539839, ⟨0, 0, 0, 0, 0, 1, 2, 1⟩),
  (Int.ofNat 1939852355995896381440, ⟨0, 0, 0, 0, 0, 0, 3, 1⟩)]
noncomputable def weighted : Polynomial := weighted_0
noncomputable def weight : ℤ := 2700000000
end Certificate.SOS.H2B011
