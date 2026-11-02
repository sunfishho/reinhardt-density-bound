import Certificate.Generated.H2B003Data
import Certificate.SOSPolynomial
namespace Certificate.SOS.H2B003
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def basisList : List Exponent := [⟨0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0⟩]
noncomputable def basis : Fin Certificate.Generated.H2B003.data.size → Exponent := fun i => basisList.getD i.val ⟨0,0,0,0,0,0,0,0⟩
noncomputable def gram_0 : Polynomial := [
  (Int.ofNat 3990035865987952148480, ⟨0, 0, 0, 0, 0, 0, 0, 0⟩),
  (Int.ofNat 532202752865346781184, ⟨0, 0, 0, 0, 1, 0, 0, 0⟩),
  (Int.ofNat 244072018855390609408, ⟨0, 0, 0, 0, 2, 0, 0, 0⟩),
  (Int.ofNat 309372524602402537472, ⟨0, 0, 0, 0, 0, 1, 0, 0⟩),
  (Int.negSucc 58152730188421529599, ⟨0, 0, 0, 0, 1, 1, 0, 0⟩),
  (Int.ofNat 286869163164339011584, ⟨0, 0, 0, 0, 0, 2, 0, 0⟩),
  (Int.negSucc 7931788640370865209343, ⟨0, 0, 0, 0, 0, 0, 1, 0⟩),
  (Int.negSucc 532527012038517456895, ⟨0, 0, 0, 0, 1, 0, 1, 0⟩),
  (Int.negSucc 313935233974882271231, ⟨0, 0, 0, 0, 0, 1, 1, 0⟩),
  (Int.ofNat 3973363540167426572288, ⟨0, 0, 0, 0, 0, 0, 2, 0⟩)]
noncomputable def gram : Polynomial := gram_0
noncomputable def multiplier_0 : Polynomial := [
  (Int.negSucc 2306, ⟨0, 0, 0, 0, 0, 0, 0, 0⟩),
  (Int.ofNat 20000, ⟨0, 0, 0, 0, 0, 1, 0, 0⟩),
  (Int.ofNat 20000, ⟨0, 0, 0, 0, 0, 0, 1, 0⟩),
  (Int.ofNat 20000, ⟨0, 0, 0, 0, 1, 0, 0, 1⟩)]
noncomputable def multiplier : Polynomial := multiplier_0
noncomputable def weighted_0 : Polynomial := [
  (Int.negSucc 9205012742834205606543359, ⟨0, 0, 0, 0, 0, 0, 0, 0⟩),
  (Int.negSucc 1227791750860355024191487, ⟨0, 0, 0, 0, 1, 0, 0, 0⟩),
  (Int.negSucc 563074147499386135904255, ⟨0, 0, 0, 0, 2, 0, 0, 0⟩),
  (Int.ofNat 79086994905501300315652096, ⟨0, 0, 0, 0, 0, 1, 0, 0⟩),
  (Int.ofNat 10778213405851624092467200, ⟨0, 0, 0, 0, 1, 1, 0, 0⟩),
  (Int.ofNat 4881440377107812188160000, ⟨0, 0, 0, 0, 2, 1, 0, 0⟩),
  (Int.ofNat 5525643332627920649715712, ⟨0, 0, 0, 0, 0, 2, 0, 0⟩),
  (Int.negSucc 1163054603768430591999999, ⟨0, 0, 0, 0, 1, 2, 0, 0⟩),
  (Int.ofNat 5737383263286780231680000, ⟨0, 0, 0, 0, 0, 3, 0, 0⟩),
  (Int.ofNat 98099353713094629007556608, ⟨0, 0, 0, 0, 0, 0, 1, 0⟩),
  (Int.ofNat 11872594874079795396739072, ⟨0, 0, 0, 0, 1, 0, 1, 0⟩),
  (Int.ofNat 4881440377107812188160000, ⟨0, 0, 0, 0, 2, 0, 1, 0⟩),
  (Int.negSucc 151724073730589200037707775, ⟨0, 0, 0, 0, 0, 1, 1, 0⟩),
  (Int.negSucc 11813594844538779729919999, ⟨0, 0, 0, 0, 1, 1, 1, 0⟩),
  (Int.negSucc 541321416210865192959999, ⟨0, 0, 0, 0, 0, 2, 1, 0⟩),
  (Int.negSucc 167802322494583557289148415, ⟨0, 0, 0, 0, 0, 0, 2, 0⟩),
  (Int.negSucc 10650540240770349137919999, ⟨0, 0, 0, 0, 1, 0, 2, 0⟩),
  (Int.ofNat 73188566123850886021120000, ⟨0, 0, 0, 0, 0, 1, 2, 0⟩),
  (Int.ofNat 79467270803348531445760000, ⟨0, 0, 0, 0, 0, 0, 3, 0⟩),
  (Int.ofNat 79800717319759042969600000, ⟨0, 0, 0, 0, 1, 0, 0, 1⟩),
  (Int.ofNat 10644055057306935623680000, ⟨0, 0, 0, 0, 2, 0, 0, 1⟩),
  (Int.ofNat 4881440377107812188160000, ⟨0, 0, 0, 0, 3, 0, 0, 1⟩),
  (Int.ofNat 6187450492048050749440000, ⟨0, 0, 0, 0, 1, 1, 0, 1⟩),
  (Int.negSucc 1163054603768430591999999, ⟨0, 0, 0, 0, 2, 1, 0, 1⟩),
  (Int.ofNat 5737383263286780231680000, ⟨0, 0, 0, 0, 1, 2, 0, 1⟩),
  (Int.negSucc 158635772807417304186879999, ⟨0, 0, 0, 0, 1, 0, 1, 1⟩),
  (Int.negSucc 10650540240770349137919999, ⟨0, 0, 0, 0, 2, 0, 1, 1⟩),
  (Int.negSucc 6278704679497645424639999, ⟨0, 0, 0, 0, 1, 1, 1, 1⟩),
  (Int.ofNat 79467270803348531445760000, ⟨0, 0, 0, 0, 1, 0, 2, 1⟩)]
noncomputable def weighted : Polynomial := weighted_0
noncomputable def weight : ℤ := 90000
end Certificate.SOS.H2B003
