import Certificate.Generated.H2B002Data
import Certificate.SOSPolynomial
namespace Certificate.SOS.H2B002
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def basisList : List Exponent := [⟨0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0⟩]
noncomputable def basis : Fin Certificate.Generated.H2B002.data.size → Exponent := fun i => basisList.getD i.val ⟨0,0,0,0,0,0,0,0⟩
noncomputable def gram_0 : Polynomial := [
  (Int.ofNat 3990037554837812412416, ⟨0, 0, 0, 0, 0, 0, 0, 0⟩),
  (Int.negSucc 532172353567862030335, ⟨0, 0, 0, 0, 1, 0, 0, 0⟩),
  (Int.ofNat 244053441506927706112, ⟨0, 0, 0, 0, 2, 0, 0, 0⟩),
  (Int.ofNat 309429382547698089984, ⟨0, 0, 0, 0, 0, 1, 0, 0⟩),
  (Int.ofNat 58129649240331255808, ⟨0, 0, 0, 0, 1, 1, 0, 0⟩),
  (Int.ofNat 286889147887685468160, ⟨0, 0, 0, 0, 0, 2, 0, 0⟩),
  (Int.negSucc 7931792581020539158527, ⟨0, 0, 0, 0, 0, 0, 1, 0⟩),
  (Int.ofNat 532497175690986127360, ⟨0, 0, 0, 0, 1, 0, 1, 0⟩),
  (Int.negSucc 313992654870131245055, ⟨0, 0, 0, 0, 0, 1, 1, 0⟩),
  (Int.ofNat 3973365791967240257536, ⟨0, 0, 0, 0, 0, 0, 2, 0⟩)]
noncomputable def gram : Polynomial := gram_0
noncomputable def multiplier_0 : Polynomial := [
  (Int.negSucc 2306, ⟨0, 0, 0, 0, 0, 0, 0, 0⟩),
  (Int.ofNat 20000, ⟨0, 0, 0, 0, 0, 1, 0, 0⟩),
  (Int.ofNat 20000, ⟨0, 0, 0, 0, 0, 0, 1, 0⟩),
  (Int.negSucc 19999, ⟨0, 0, 0, 0, 1, 0, 0, 1⟩)]
noncomputable def multiplier : Polynomial := multiplier_0
noncomputable def weighted_0 : Polynomial := [
  (Int.negSucc 9205016639010833235443711, ⟨0, 0, 0, 0, 0, 0, 0, 0⟩),
  (Int.ofNat 1227721619681057703985152, ⟨0, 0, 0, 0, 1, 0, 0, 0⟩),
  (Int.negSucc 563031289556482218000383, ⟨0, 0, 0, 0, 2, 0, 0, 0⟩),
  (Int.ofNat 79086897511218708754726912, ⟨0, 0, 0, 0, 0, 1, 0, 0⟩),
  (Int.negSucc 10777552172154684813869055, ⟨0, 0, 0, 0, 1, 1, 0, 0⟩),
  (Int.ofNat 4881068830138554122240000, ⟨0, 0, 0, 0, 2, 1, 0, 0⟩),
  (Int.ofNat 5526734386777071424634880, ⟨0, 0, 0, 0, 0, 2, 0, 0⟩),
  (Int.ofNat 1162592984806625116160000, ⟨0, 0, 0, 0, 1, 2, 0, 0⟩),
  (Int.ofNat 5737782957753709363200000, ⟨0, 0, 0, 0, 0, 3, 0, 0⟩),
  (Int.ofNat 98099396581170632087044096, ⟨0, 0, 0, 0, 0, 0, 1, 0⟩),
  (Int.negSucc 11871918055676345602539519, ⟨0, 0, 0, 0, 1, 0, 1, 0⟩),
  (Int.ofNat 4881068830138554122240000, ⟨0, 0, 0, 0, 2, 0, 1, 0⟩),
  (Int.negSucc 151722882914671428588535807, ⟨0, 0, 0, 0, 0, 1, 1, 0⟩),
  (Int.ofNat 11812536498626347663360000, ⟨0, 0, 0, 0, 1, 1, 1, 0⟩),
  (Int.negSucc 542070139648915537919999, ⟨0, 0, 0, 0, 0, 2, 1, 0⟩),
  (Int.negSucc 167802406502479206444695551, ⟨0, 0, 0, 0, 0, 0, 2, 0⟩),
  (Int.ofNat 10649943513819722547200000, ⟨0, 0, 0, 0, 1, 0, 2, 0⟩),
  (Int.ofNat 73187462741942180249600000, ⟨0, 0, 0, 0, 0, 1, 2, 0⟩),
  (Int.ofNat 79467315839344805150720000, ⟨0, 0, 0, 0, 0, 0, 3, 0⟩),
  (Int.negSucc 79800751096756248248319999, ⟨0, 0, 0, 0, 1, 0, 0, 1⟩),
  (Int.ofNat 10643447071357240606720000, ⟨0, 0, 0, 0, 2, 0, 0, 1⟩),
  (Int.negSucc 4881068830138554122239999, ⟨0, 0, 0, 0, 3, 0, 0, 1⟩),
  (Int.negSucc 6188587650953961799679999, ⟨0, 0, 0, 0, 1, 1, 0, 1⟩),
  (Int.negSucc 1162592984806625116159999, ⟨0, 0, 0, 0, 2, 1, 0, 1⟩),
  (Int.negSucc 5737782957753709363199999, ⟨0, 0, 0, 0, 1, 2, 0, 1⟩),
  (Int.ofNat 158635851620410783170560000, ⟨0, 0, 0, 0, 1, 0, 1, 1⟩),
  (Int.negSucc 10649943513819722547199999, ⟨0, 0, 0, 0, 2, 0, 1, 1⟩),
  (Int.ofNat 6279853097402624901120000, ⟨0, 0, 0, 0, 1, 1, 1, 1⟩),
  (Int.negSucc 79467315839344805150719999, ⟨0, 0, 0, 0, 1, 0, 2, 1⟩)]
noncomputable def weighted : Polynomial := weighted_0
noncomputable def weight : ℤ := 90000
end Certificate.SOS.H2B002
