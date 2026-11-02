import Certificate.Generated.H2B016Data
import Certificate.SOSPolynomial
namespace Certificate.SOS.H2B016
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def basisList : List Exponent := [⟨0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0⟩]
noncomputable def basis : Fin Certificate.Generated.H2B016.data.size → Exponent := fun i => basisList.getD i.val ⟨0,0,0,0,0,0,0,0⟩
noncomputable def gram_0 : Polynomial := [
  (Int.ofNat 26245353954749676781568, ⟨0, 0, 0, 0, 0, 0, 0, 0⟩),
  (Int.negSucc 9007199254740991, ⟨0, 0, 0, 0, 1, 0, 0, 0⟩),
  (Int.ofNat 221929789812446855168, ⟨0, 0, 0, 0, 2, 0, 0, 0⟩),
  (Int.negSucc 271787733912182063103, ⟨0, 0, 0, 0, 0, 1, 0, 0⟩),
  (Int.ofNat 15762598695796736, ⟨0, 0, 0, 0, 1, 1, 0, 0⟩),
  (Int.ofNat 169939672764128428032, ⟨0, 0, 0, 0, 0, 2, 0, 0⟩),
  (Int.negSucc 52337595092317964861439, ⟨0, 0, 0, 0, 0, 0, 1, 0⟩),
  (Int.ofNat 9007199254740992, ⟨0, 0, 0, 0, 1, 0, 1, 0⟩),
  (Int.ofNat 270514904067496476672, ⟨0, 0, 0, 0, 0, 1, 1, 0⟩),
  (Int.ofNat 26123738750412163907584, ⟨0, 0, 0, 0, 0, 0, 2, 0⟩)]
noncomputable def gram : Polynomial := gram_0
noncomputable def multiplier_0 : Polynomial := [
  (Int.negSucc 27683, ⟨0, 0, 0, 0, 0, 0, 0, 0⟩),
  (Int.negSucc 479999, ⟨0, 0, 0, 0, 0, 1, 0, 0⟩),
  (Int.ofNat 251535, ⟨0, 0, 0, 0, 0, 0, 1, 0⟩),
  (Int.ofNat 200000, ⟨0, 0, 0, 0, 0, 1, 1, 0⟩),
  (Int.negSucc 99999, ⟨0, 0, 0, 0, 0, 0, 2, 0⟩)]
noncomputable def multiplier : Polynomial := multiplier_0
noncomputable def weighted_0 : Polynomial := [
  (Int.negSucc 726576378883290052020928511, ⟨0, 0, 0, 0, 0, 0, 0, 0⟩),
  (Int.ofNat 249355304168249622528, ⟨0, 0, 0, 0, 1, 0, 0, 0⟩),
  (Int.negSucc 6143904301167778738470911, ⟨0, 0, 0, 0, 2, 0, 0, 0⟩),
  (Int.negSucc 12590245726654220006917668863, ⟨0, 0, 0, 0, 0, 1, 0, 0⟩),
  (Int.ofNat 3887083859981239320576, ⟨0, 0, 0, 0, 1, 1, 0, 0⟩),
  (Int.negSucc 106526299109974490480639999, ⟨0, 0, 0, 0, 2, 1, 0, 0⟩),
  (Int.ofNat 125753502377045258888282112, ⟨0, 0, 0, 0, 0, 2, 0, 0⟩),
  (Int.negSucc 7566047373982433279999, ⟨0, 0, 0, 0, 1, 2, 0, 0⟩),
  (Int.negSucc 81571042926781645455359999, ⟨0, 0, 0, 0, 0, 3, 0, 0⟩),
  (Int.ofNat 8050539089543690488475811840, ⟨0, 0, 0, 0, 0, 0, 1, 0⟩),
  (Int.negSucc 2514981168709525045247, ⟨0, 0, 0, 0, 1, 0, 1, 0⟩),
  (Int.ofNat 55823109680473819714682880, ⟨0, 0, 0, 0, 2, 0, 1, 0⟩),
  (Int.ofNat 30295263373008753202101747712, ⟨0, 0, 0, 0, 0, 1, 1, 0⟩),
  (Int.negSucc 2160050230276642570239, ⟨0, 0, 0, 0, 1, 1, 1, 0⟩),
  (Int.ofNat 44385957962489371033600000, ⟨0, 0, 0, 0, 2, 1, 1, 0⟩),
  (Int.negSucc 141458925146109677278330879, ⟨0, 0, 0, 0, 0, 2, 1, 0⟩),
  (Int.ofNat 3152519739159347200000, ⟨0, 0, 0, 0, 1, 2, 1, 0⟩),
  (Int.ofNat 33987934552825685606400000, ⟨0, 0, 0, 0, 0, 3, 1, 0⟩),
  (Int.negSucc 16512481960587577315196665855, ⟨0, 0, 0, 0, 0, 0, 2, 0⟩),
  (Int.ofNat 3166345790015374622720, ⟨0, 0, 0, 0, 1, 0, 2, 0⟩),
  (Int.negSucc 22192978981244685516799999, ⟨0, 0, 0, 0, 2, 0, 2, 0⟩),
  (Int.negSucc 22911690878875595715358228479, ⟨0, 0, 0, 0, 0, 1, 2, 0⟩),
  (Int.ofNat 225179981368524800000, ⟨0, 0, 0, 0, 1, 1, 2, 0⟩),
  (Int.ofNat 37109013537086452531200000, ⟨0, 0, 0, 0, 0, 2, 2, 0⟩),
  (Int.ofNat 11804794135816720134638141440, ⟨0, 0, 0, 0, 0, 0, 3, 0⟩),
  (Int.negSucc 900719925474099199999, ⟨0, 0, 0, 0, 1, 0, 3, 0⟩),
  (Int.ofNat 5197696259675683133849600000, ⟨0, 0, 0, 0, 0, 1, 3, 0⟩),
  (Int.negSucc 2612373875041216390758399999, ⟨0, 0, 0, 0, 0, 0, 4, 0⟩)]
noncomputable def weighted : Polynomial := weighted_0
noncomputable def weight : ℤ := 18000
end Certificate.SOS.H2B016
