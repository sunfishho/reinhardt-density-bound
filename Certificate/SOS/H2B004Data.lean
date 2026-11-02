import Certificate.Generated.H2B004Data
import Certificate.SOSPolynomial
namespace Certificate.SOS.H2B004
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def basisList : List Exponent := [⟨0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0⟩]
noncomputable def basis : Fin Certificate.Generated.H2B004.data.size → Exponent := fun i => basisList.getD i.val ⟨0,0,0,0,0,0,0,0⟩
noncomputable def gram_0 : Polynomial := [
  (Int.ofNat 4547804990987927814144, ⟨0, 0, 0, 0, 0, 0, 0, 0⟩),
  (Int.ofNat 2907678167717629657088, ⟨0, 0, 0, 0, 2, 0, 0, 0⟩),
  (Int.ofNat 605319255765660205056, ⟨0, 0, 0, 0, 0, 1, 0, 0⟩),
  (Int.ofNat 1125899906842624, ⟨0, 0, 0, 0, 1, 1, 0, 0⟩),
  (Int.ofNat 3289592704792879169536, ⟨0, 0, 0, 0, 0, 2, 0, 0⟩),
  (Int.negSucc 8559760439312245587967, ⟨0, 0, 0, 0, 0, 0, 1, 0⟩),
  (Int.negSucc 641428554627963420671, ⟨0, 0, 0, 0, 0, 1, 1, 0⟩),
  (Int.ofNat 4187671832035478994944, ⟨0, 0, 0, 0, 0, 0, 2, 0⟩)]
noncomputable def gram : Polynomial := gram_0
noncomputable def multiplier_0 : Polynomial := [
  (Int.negSucc 0, ⟨0, 0, 0, 0, 0, 0, 0, 0⟩),
  (Int.ofNat 1, ⟨0, 0, 0, 0, 0, 0, 1, 0⟩)]
noncomputable def multiplier : Polynomial := multiplier_0
noncomputable def weighted_0 : Polynomial := [
  (Int.negSucc 4547804990987927814143, ⟨0, 0, 0, 0, 0, 0, 0, 0⟩),
  (Int.negSucc 2907678167717629657087, ⟨0, 0, 0, 0, 2, 0, 0, 0⟩),
  (Int.negSucc 605319255765660205055, ⟨0, 0, 0, 0, 0, 1, 0, 0⟩),
  (Int.negSucc 1125899906842623, ⟨0, 0, 0, 0, 1, 1, 0, 0⟩),
  (Int.negSucc 3289592704792879169535, ⟨0, 0, 0, 0, 0, 2, 0, 0⟩),
  (Int.ofNat 13107565430300173402112, ⟨0, 0, 0, 0, 0, 0, 1, 0⟩),
  (Int.ofNat 2907678167717629657088, ⟨0, 0, 0, 0, 2, 0, 1, 0⟩),
  (Int.ofNat 1246747810393623625728, ⟨0, 0, 0, 0, 0, 1, 1, 0⟩),
  (Int.ofNat 1125899906842624, ⟨0, 0, 0, 0, 1, 1, 1, 0⟩),
  (Int.ofNat 3289592704792879169536, ⟨0, 0, 0, 0, 0, 2, 1, 0⟩),
  (Int.negSucc 12747432271347724582911, ⟨0, 0, 0, 0, 0, 0, 2, 0⟩),
  (Int.negSucc 641428554627963420671, ⟨0, 0, 0, 0, 0, 1, 2, 0⟩),
  (Int.ofNat 4187671832035478994944, ⟨0, 0, 0, 0, 0, 0, 3, 0⟩)]
noncomputable def weighted : Polynomial := weighted_0
noncomputable def weight : ℤ := 2700000000
end Certificate.SOS.H2B004
