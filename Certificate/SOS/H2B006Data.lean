import Certificate.Generated.H2B006Data
import Certificate.SOSPolynomial
namespace Certificate.SOS.H2B006
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def basisList : List Exponent := [⟨0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0⟩]
noncomputable def basis : Fin Certificate.Generated.H2B006.data.size → Exponent := fun i => basisList.getD i.val ⟨0,0,0,0,0,0,0,0⟩
noncomputable def gram_0 : Polynomial := [
  (Int.ofNat 13751778335397758631936, ⟨0, 0, 0, 0, 0, 0, 0, 0⟩),
  (Int.ofNat 45663122521816301568, ⟨0, 0, 0, 0, 2, 0, 0, 0⟩),
  (Int.negSucc 24441598127693103103, ⟨0, 0, 0, 0, 0, 1, 0, 0⟩),
  (Int.ofNat 46273641746301714432, ⟨0, 0, 0, 0, 0, 2, 0, 0⟩),
  (Int.negSucc 27390832135072387170303, ⟨0, 0, 0, 0, 0, 0, 1, 0⟩),
  (Int.ofNat 23882588823945740288, ⟨0, 0, 0, 0, 0, 1, 1, 0⟩),
  (Int.ofNat 13670176769324502482944, ⟨0, 0, 0, 0, 0, 0, 2, 0⟩)]
noncomputable def gram : Polynomial := gram_0
noncomputable def multiplier_0 : Polynomial := [
  (Int.ofNat 119, ⟨0, 0, 0, 0, 0, 0, 0, 0⟩),
  (Int.negSucc 24, ⟨0, 0, 0, 0, 2, 0, 0, 0⟩),
  (Int.negSucc 24, ⟨0, 0, 0, 0, 0, 2, 0, 0⟩)]
noncomputable def multiplier : Polynomial := multiplier_0
noncomputable def weighted_0 : Polynomial := [
  (Int.ofNat 1636461621912333277200384, ⟨0, 0, 0, 0, 0, 0, 0, 0⟩),
  (Int.negSucc 338360546804847825911807, ⟨0, 0, 0, 0, 2, 0, 0, 0⟩),
  (Int.negSucc 1141578063045407539199, ⟨0, 0, 0, 0, 4, 0, 0, 0⟩),
  (Int.negSucc 2908550177195479269375, ⟨0, 0, 0, 0, 0, 1, 0, 0⟩),
  (Int.ofNat 611039953192327577600, ⟨0, 0, 0, 0, 2, 1, 0, 0⟩),
  (Int.negSucc 338287895017134061780991, ⟨0, 0, 0, 0, 0, 2, 0, 0⟩),
  (Int.negSucc 2298419106702950399999, ⟨0, 0, 0, 0, 2, 2, 0, 0⟩),
  (Int.ofNat 611039953192327577600, ⟨0, 0, 0, 0, 0, 3, 0, 0⟩),
  (Int.negSucc 1156841043657542860799, ⟨0, 0, 0, 0, 0, 4, 0, 0⟩),
  (Int.negSucc 3259509024073614073266175, ⟨0, 0, 0, 0, 0, 0, 1, 0⟩),
  (Int.ofNat 684770803376809679257600, ⟨0, 0, 0, 0, 2, 0, 1, 0⟩),
  (Int.ofNat 2842028070049543094272, ⟨0, 0, 0, 0, 0, 1, 1, 0⟩),
  (Int.negSucc 597064720598643507199, ⟨0, 0, 0, 0, 2, 1, 1, 0⟩),
  (Int.ofNat 684770803376809679257600, ⟨0, 0, 0, 0, 0, 2, 1, 0⟩),
  (Int.negSucc 597064720598643507199, ⟨0, 0, 0, 0, 0, 3, 1, 0⟩),
  (Int.ofNat 1626751035549615795470336, ⟨0, 0, 0, 0, 0, 0, 2, 0⟩),
  (Int.negSucc 341754419233112562073599, ⟨0, 0, 0, 0, 2, 0, 2, 0⟩),
  (Int.negSucc 341754419233112562073599, ⟨0, 0, 0, 0, 0, 2, 2, 0⟩)]
noncomputable def weighted : Polynomial := weighted_0
noncomputable def weight : ℤ := 108000000
end Certificate.SOS.H2B006
