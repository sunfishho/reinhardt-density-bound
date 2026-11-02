import Certificate.Generated.H2B007Data
import Certificate.SOSPolynomial
namespace Certificate.SOS.H2B007
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def basisList : List Exponent := [⟨0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0⟩]
noncomputable def basis : Fin Certificate.Generated.H2B007.data.size → Exponent := fun i => basisList.getD i.val ⟨0,0,0,0,0,0,0,0⟩
noncomputable def gram_0 : Polynomial := [
  (Int.ofNat 2607083721738925637632, ⟨0, 0, 0, 0, 0, 0, 0, 0⟩),
  (Int.negSucc 6755399441055743, ⟨0, 0, 0, 0, 1, 0, 0, 0⟩),
  (Int.ofNat 168662620794792181760, ⟨0, 0, 0, 0, 2, 0, 0, 0⟩),
  (Int.ofNat 305751630501996658688, ⟨0, 0, 0, 0, 0, 1, 0, 0⟩),
  (Int.negSucc 9007199254740991, ⟨0, 0, 0, 0, 1, 1, 0, 0⟩),
  (Int.ofNat 222135829495399055360, ⟨0, 0, 0, 0, 0, 2, 0, 0⟩),
  (Int.negSucc 5171061239644474572799, ⟨0, 0, 0, 0, 0, 0, 1, 0⟩),
  (Int.ofNat 6755399441055744, ⟨0, 0, 0, 0, 1, 0, 1, 0⟩),
  (Int.negSucc 309397294400353075199, ⟨0, 0, 0, 0, 0, 1, 1, 0⟩),
  (Int.ofNat 2595427280003383951360, ⟨0, 0, 0, 0, 0, 0, 2, 0⟩)]
noncomputable def gram : Polynomial := gram_0
noncomputable def multiplier_0 : Polynomial := [
  (Int.negSucc 1, ⟨0, 0, 0, 0, 0, 0, 0, 0⟩),
  (Int.ofNat 9, ⟨0, 0, 0, 0, 0, 1, 0, 0⟩),
  (Int.ofNat 9, ⟨0, 0, 0, 0, 0, 0, 1, 0⟩)]
noncomputable def multiplier : Polynomial := multiplier_0
noncomputable def weighted_0 : Polynomial := [
  (Int.negSucc 5214167443477851275263, ⟨0, 0, 0, 0, 0, 0, 0, 0⟩),
  (Int.ofNat 13510798882111488, ⟨0, 0, 0, 0, 1, 0, 0, 0⟩),
  (Int.negSucc 337325241589584363519, ⟨0, 0, 0, 0, 2, 0, 0, 0⟩),
  (Int.ofNat 22852250234646337421312, ⟨0, 0, 0, 0, 0, 1, 0, 0⟩),
  (Int.negSucc 42784196460019711, ⟨0, 0, 0, 0, 1, 1, 0, 0⟩),
  (Int.ofNat 1517963587153129635840, ⟨0, 0, 0, 0, 2, 1, 0, 0⟩),
  (Int.ofNat 2307493015527171817472, ⟨0, 0, 0, 0, 0, 2, 0, 0⟩),
  (Int.negSucc 81064793292668927, ⟨0, 0, 0, 0, 1, 2, 0, 0⟩),
  (Int.ofNat 1999222465458591498240, ⟨0, 0, 0, 0, 0, 3, 0, 0⟩),
  (Int.ofNat 33805875974939279884288, ⟨0, 0, 0, 0, 0, 0, 1, 0⟩),
  (Int.negSucc 74309393851613183, ⟨0, 0, 0, 0, 1, 0, 1, 0⟩),
  (Int.ofNat 1517963587153129635840, ⟨0, 0, 0, 0, 2, 0, 1, 0⟩),
  (Int.negSucc 43168991893481595076607, ⟨0, 0, 0, 0, 0, 1, 1, 0⟩),
  (Int.negSucc 20266198323167231, ⟨0, 0, 0, 0, 1, 1, 1, 0⟩),
  (Int.negSucc 785353184144586178559, ⟨0, 0, 0, 0, 0, 2, 1, 0⟩),
  (Int.negSucc 51730405716807039057919, ⟨0, 0, 0, 0, 0, 0, 2, 0⟩),
  (Int.ofNat 60798594969501696, ⟨0, 0, 0, 0, 1, 0, 2, 0⟩),
  (Int.ofNat 20574269870427277885440, ⟨0, 0, 0, 0, 0, 1, 2, 0⟩),
  (Int.ofNat 23358845520030455562240, ⟨0, 0, 0, 0, 0, 0, 3, 0⟩)]
noncomputable def weighted : Polynomial := weighted_0
noncomputable def weight : ℤ := 300000000
end Certificate.SOS.H2B007
