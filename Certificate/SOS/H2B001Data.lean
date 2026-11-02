import Certificate.Generated.H2B001Data
import Certificate.SOSPolynomial
namespace Certificate.SOS.H2B001
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def basisList : List Exponent := [⟨0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0⟩]
noncomputable def basis : Fin Certificate.Generated.H2B001.data.size → Exponent := fun i => basisList.getD i.val ⟨0,0,0,0,0,0,0,0⟩
noncomputable def gram_0 : Polynomial := [
  (Int.ofNat 4760259488659363856384, ⟨0, 0, 0, 0, 0, 0, 0, 0⟩),
  (Int.negSucc 30962247438172159, ⟨0, 0, 0, 0, 1, 0, 0, 0⟩),
  (Int.ofNat 299756494973036396544, ⟨0, 0, 0, 0, 2, 0, 0, 0⟩),
  (Int.negSucc 625932794210088386559, ⟨0, 0, 0, 0, 0, 1, 0, 0⟩),
  (Int.ofNat 21392098230009856, ⟨0, 0, 0, 0, 1, 1, 0, 0⟩),
  (Int.ofNat 229703565719241752576, ⟨0, 0, 0, 0, 0, 2, 0, 0⟩),
  (Int.negSucc 9460955494547032375295, ⟨0, 0, 0, 0, 0, 0, 1, 0⟩),
  (Int.ofNat 30399297484750848, ⟨0, 0, 0, 0, 1, 0, 1, 0⟩),
  (Int.ofNat 623599366653157048320, ⟨0, 0, 0, 0, 0, 1, 1, 0⟩),
  (Int.ofNat 4732313808546599796736, ⟨0, 0, 0, 0, 0, 0, 2, 0⟩)]
noncomputable def gram : Polynomial := gram_0
noncomputable def multiplier_0 : Polynomial := [
  (Int.negSucc 2306, ⟨0, 0, 0, 0, 0, 0, 0, 0⟩),
  (Int.negSucc 39999, ⟨0, 0, 0, 0, 0, 1, 0, 0⟩),
  (Int.ofNat 20000, ⟨0, 0, 0, 0, 0, 0, 1, 0⟩)]
noncomputable def multiplier : Polynomial := multiplier_0
noncomputable def weighted_0 : Polynomial := [
  (Int.negSucc 10981918640337152416677887, ⟨0, 0, 0, 0, 0, 0, 0, 0⟩),
  (Int.ofNat 71429904839863173120, ⟨0, 0, 0, 0, 1, 0, 0, 0⟩),
  (Int.negSucc 691538233902794966827007, ⟨0, 0, 0, 0, 2, 0, 0, 0⟩),
  (Int.negSucc 188966352590131880347566079, ⟨0, 0, 0, 0, 0, 1, 0, 0⟩),
  (Int.ofNat 1189138326910253662208, ⟨0, 0, 0, 0, 1, 1, 0, 0⟩),
  (Int.negSucc 11990259798921455861759999, ⟨0, 0, 0, 0, 2, 1, 0, 0⟩),
  (Int.ofNat 24507385642289244739207168, ⟨0, 0, 0, 0, 0, 2, 0, 0⟩),
  (Int.negSucc 855683929200394239999, ⟨0, 0, 0, 0, 1, 2, 0, 0⟩),
  (Int.negSucc 9188142628769670103039999, ⟨0, 0, 0, 0, 0, 3, 0, 0⟩),
  (Int.ofNat 117031614099107280817487872, ⟨0, 0, 0, 0, 0, 0, 1, 0⟩),
  (Int.negSucc 689376128060763406335, ⟨0, 0, 0, 0, 1, 0, 1, 0⟩),
  (Int.ofNat 5995129899460727930880000, ⟨0, 0, 0, 0, 2, 0, 1, 0⟩),
  (Int.ofNat 364480920158810693970165760, ⟨0, 0, 0, 0, 0, 1, 1, 0⟩),
  (Int.negSucc 788129934789836799999, ⟨0, 0, 0, 0, 1, 1, 1, 0⟩),
  (Int.negSucc 20349903351741446881279999, ⟨0, 0, 0, 0, 0, 2, 1, 0⟩),
  (Int.negSucc 200136557847257653236989951, ⟨0, 0, 0, 0, 0, 0, 2, 0⟩),
  (Int.ofNat 607985949695016960000, ⟨0, 0, 0, 0, 1, 0, 2, 0⟩),
  (Int.negSucc 176820565008800850903039999, ⟨0, 0, 0, 0, 0, 1, 2, 0⟩),
  (Int.ofNat 94646276170931995934720000, ⟨0, 0, 0, 0, 0, 0, 3, 0⟩)]
noncomputable def weighted : Polynomial := weighted_0
noncomputable def weight : ℤ := 90000
end Certificate.SOS.H2B001
