import Certificate.Generated.H2B012Data
import Certificate.SOSPolynomial
namespace Certificate.SOS.H2B012
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def basisList : List Exponent := [⟨0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0⟩]
noncomputable def basis : Fin Certificate.Generated.H2B012.data.size → Exponent := fun i => basisList.getD i.val ⟨0,0,0,0,0,0,0,0⟩
noncomputable def gram_0 : Polynomial := [
  (Int.ofNat 328221777892808327168, ⟨0, 0, 0, 0, 0, 0, 0, 0⟩),
  (Int.ofNat 42146374162793365504, ⟨0, 0, 0, 0, 1, 0, 0, 0⟩),
  (Int.ofNat 33131293608704475136, ⟨0, 0, 0, 0, 2, 0, 0, 0⟩),
  (Int.ofNat 24505211472429711360, ⟨0, 0, 0, 0, 0, 1, 0, 0⟩),
  (Int.negSucc 4437171532866781183, ⟨0, 0, 0, 0, 1, 1, 0, 0⟩),
  (Int.ofNat 36405410537802825728, ⟨0, 0, 0, 0, 0, 2, 0, 0⟩),
  (Int.negSucc 624123473059792289791, ⟨0, 0, 0, 0, 0, 0, 1, 0⟩),
  (Int.negSucc 42168329210976796671, ⟨0, 0, 0, 0, 1, 0, 1, 0⟩),
  (Int.negSucc 24855366343457767423, ⟨0, 0, 0, 0, 0, 1, 1, 0⟩),
  (Int.ofNat 326901660252035350528, ⟨0, 0, 0, 0, 0, 0, 2, 0⟩)]
noncomputable def gram : Polynomial := gram_0
noncomputable def multiplier_0 : Polynomial := [
  (Int.negSucc 0, ⟨0, 0, 0, 0, 0, 0, 0, 0⟩),
  (Int.ofNat 15, ⟨0, 0, 0, 0, 1, 0, 0, 0⟩),
  (Int.ofNat 5, ⟨0, 0, 0, 0, 0, 1, 0, 1⟩),
  (Int.ofNat 5, ⟨0, 0, 0, 0, 0, 0, 1, 1⟩)]
noncomputable def multiplier : Polynomial := multiplier_0
noncomputable def weighted_0 : Polynomial := [
  (Int.negSucc 328221777892808327167, ⟨0, 0, 0, 0, 0, 0, 0, 0⟩),
  (Int.ofNat 4881180294229331542016, ⟨0, 0, 0, 0, 1, 0, 0, 0⟩),
  (Int.ofNat 599064318833196007424, ⟨0, 0, 0, 0, 2, 0, 0, 0⟩),
  (Int.ofNat 496969404130567127040, ⟨0, 0, 0, 0, 3, 0, 0, 0⟩),
  (Int.negSucc 24505211472429711359, ⟨0, 0, 0, 0, 0, 1, 0, 0⟩),
  (Int.ofNat 372015343619312451584, ⟨0, 0, 0, 0, 1, 1, 0, 0⟩),
  (Int.negSucc 66557572993001717759, ⟨0, 0, 0, 0, 2, 1, 0, 0⟩),
  (Int.negSucc 36405410537802825727, ⟨0, 0, 0, 0, 0, 2, 0, 0⟩),
  (Int.ofNat 546081158067042385920, ⟨0, 0, 0, 0, 1, 2, 0, 0⟩),
  (Int.ofNat 624123473059792289792, ⟨0, 0, 0, 0, 0, 0, 1, 0⟩),
  (Int.negSucc 9319683766685907550207, ⟨0, 0, 0, 0, 1, 0, 1, 0⟩),
  (Int.negSucc 632524938164651950079, ⟨0, 0, 0, 0, 2, 0, 1, 0⟩),
  (Int.ofNat 24855366343457767424, ⟨0, 0, 0, 0, 0, 1, 1, 0⟩),
  (Int.negSucc 372830495151866511359, ⟨0, 0, 0, 0, 1, 1, 1, 0⟩),
  (Int.negSucc 326901660252035350527, ⟨0, 0, 0, 0, 0, 0, 2, 0⟩),
  (Int.ofNat 4903524903780530257920, ⟨0, 0, 0, 0, 1, 0, 2, 0⟩),
  (Int.ofNat 1641108889464041635840, ⟨0, 0, 0, 0, 0, 1, 0, 1⟩),
  (Int.ofNat 210731870813966827520, ⟨0, 0, 0, 0, 1, 1, 0, 1⟩),
  (Int.ofNat 165656468043522375680, ⟨0, 0, 0, 0, 2, 1, 0, 1⟩),
  (Int.ofNat 122526057362148556800, ⟨0, 0, 0, 0, 0, 2, 0, 1⟩),
  (Int.negSucc 22185857664333905919, ⟨0, 0, 0, 0, 1, 2, 0, 1⟩),
  (Int.ofNat 182027052689014128640, ⟨0, 0, 0, 0, 0, 3, 0, 1⟩),
  (Int.ofNat 1641108889464041635840, ⟨0, 0, 0, 0, 0, 0, 1, 1⟩),
  (Int.ofNat 210731870813966827520, ⟨0, 0, 0, 0, 1, 0, 1, 1⟩),
  (Int.ofNat 165656468043522375680, ⟨0, 0, 0, 0, 2, 0, 1, 1⟩),
  (Int.negSucc 2998091307936812892159, ⟨0, 0, 0, 0, 0, 1, 1, 1⟩),
  (Int.negSucc 233027503719217889279, ⟨0, 0, 0, 0, 1, 1, 1, 1⟩),
  (Int.ofNat 57750220971725291520, ⟨0, 0, 0, 0, 0, 2, 1, 1⟩),
  (Int.negSucc 3120617365298961448959, ⟨0, 0, 0, 0, 0, 0, 2, 1⟩),
  (Int.negSucc 210841646054883983359, ⟨0, 0, 0, 0, 1, 0, 2, 1⟩),
  (Int.ofNat 1510231469542887915520, ⟨0, 0, 0, 0, 0, 1, 2, 1⟩),
  (Int.ofNat 1634508301260176752640, ⟨0, 0, 0, 0, 0, 0, 3, 1⟩)]
noncomputable def weighted : Polynomial := weighted_0
noncomputable def weight : ℤ := 2700000000
end Certificate.SOS.H2B012
