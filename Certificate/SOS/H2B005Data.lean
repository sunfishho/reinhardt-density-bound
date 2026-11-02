import Certificate.Generated.H2B005Data
import Certificate.SOSPolynomial
namespace Certificate.SOS.H2B005
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def basisList : List Exponent := [⟨0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0⟩]
noncomputable def basis : Fin Certificate.Generated.H2B005.data.size → Exponent := fun i => basisList.getD i.val ⟨0,0,0,0,0,0,0,0⟩
noncomputable def gram_0 : Polynomial := [
  (Int.ofNat 74931593724682135666688, ⟨0, 0, 0, 0, 0, 0, 0, 0⟩),
  (Int.ofNat 118283103563212128256, ⟨0, 0, 0, 0, 2, 0, 0, 0⟩),
  (Int.negSucc 121261108816810868735, ⟨0, 0, 0, 0, 0, 1, 0, 0⟩),
  (Int.ofNat 120390788188821520384, ⟨0, 0, 0, 0, 0, 2, 0, 0⟩),
  (Int.negSucc 149353611906926740766719, ⟨0, 0, 0, 0, 0, 0, 1, 0⟩),
  (Int.ofNat 119202963787102552064, ⟨0, 0, 0, 0, 0, 1, 1, 0⟩),
  (Int.ofNat 74453862572259788455936, ⟨0, 0, 0, 0, 0, 0, 2, 0⟩)]
noncomputable def gram : Polynomial := gram_0
noncomputable def multiplier_0 : Polynomial := [
  (Int.ofNat 12, ⟨0, 0, 0, 0, 0, 0, 0, 0⟩),
  (Int.negSucc 4, ⟨0, 0, 0, 0, 0, 0, 1, 0⟩)]
noncomputable def multiplier : Polynomial := multiplier_0
noncomputable def weighted_0 : Polynomial := [
  (Int.ofNat 899179124696185628000256, ⟨0, 0, 0, 0, 0, 0, 0, 0⟩),
  (Int.ofNat 1419397242758545539072, ⟨0, 0, 0, 0, 2, 0, 0, 0⟩),
  (Int.negSucc 1455133305801730424831, ⟨0, 0, 0, 0, 0, 1, 0, 0⟩),
  (Int.ofNat 1444689458265858244608, ⟨0, 0, 0, 0, 0, 2, 0, 0⟩),
  (Int.negSucc 2166901311506531567534079, ⟨0, 0, 0, 0, 0, 0, 1, 0⟩),
  (Int.negSucc 591415517816060641279, ⟨0, 0, 0, 0, 2, 0, 1, 0⟩),
  (Int.ofNat 2036741109529284968448, ⟨0, 0, 0, 0, 0, 1, 1, 0⟩),
  (Int.negSucc 601953940944107601919, ⟨0, 0, 0, 0, 0, 2, 1, 0⟩),
  (Int.ofNat 1640214410401751165304832, ⟨0, 0, 0, 0, 0, 0, 2, 0⟩),
  (Int.negSucc 596014818935512760319, ⟨0, 0, 0, 0, 0, 1, 2, 0⟩),
  (Int.negSucc 372269312861298942279679, ⟨0, 0, 0, 0, 0, 0, 3, 0⟩)]
noncomputable def weighted : Polynomial := weighted_0
noncomputable def weight : ℤ := 540000000
end Certificate.SOS.H2B005
