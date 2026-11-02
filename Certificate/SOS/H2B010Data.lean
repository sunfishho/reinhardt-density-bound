import Certificate.Generated.H2B010Data
import Certificate.SOSPolynomial
namespace Certificate.SOS.H2B010
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def basisList : List Exponent := [⟨0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0⟩]
noncomputable def basis : Fin Certificate.Generated.H2B010.data.size → Exponent := fun i => basisList.getD i.val ⟨0,0,0,0,0,0,0,0⟩
noncomputable def gram_0 : Polynomial := [
  (Int.ofNat 328221777892808327168, ⟨0, 0, 0, 0, 0, 0, 0, 0⟩),
  (Int.negSucc 42143559413026258943, ⟨0, 0, 0, 0, 1, 0, 0, 0⟩),
  (Int.ofNat 33129886233820921856, ⟨0, 0, 0, 0, 2, 0, 0, 0⟩),
  (Int.ofNat 24509715072057081856, ⟨0, 0, 0, 0, 0, 1, 0, 0⟩),
  (Int.ofNat 4435482683006517248, ⟨0, 0, 0, 0, 1, 1, 0, 0⟩),
  (Int.ofNat 36406817912686379008, ⟨0, 0, 0, 0, 0, 2, 0, 0⟩),
  (Int.negSucc 624124036009745711103, ⟨0, 0, 0, 0, 0, 0, 1, 0⟩),
  (Int.ofNat 42166077411163111424, ⟨0, 0, 0, 0, 1, 0, 1, 0⟩),
  (Int.negSucc 24859869943085137919, ⟨0, 0, 0, 0, 0, 1, 1, 0⟩),
  (Int.ofNat 326901941727012061184, ⟨0, 0, 0, 0, 0, 0, 2, 0⟩)]
noncomputable def gram : Polynomial := gram_0
noncomputable def multiplier_0 : Polynomial := [
  (Int.negSucc 0, ⟨0, 0, 0, 0, 0, 0, 0, 0⟩),
  (Int.negSucc 14, ⟨0, 0, 0, 0, 1, 0, 0, 0⟩),
  (Int.ofNat 5, ⟨0, 0, 0, 0, 0, 1, 0, 1⟩),
  (Int.ofNat 5, ⟨0, 0, 0, 0, 0, 0, 1, 1⟩)]
noncomputable def multiplier : Polynomial := multiplier_0
noncomputable def weighted_0 : Polynomial := [
  (Int.negSucc 328221777892808327167, ⟨0, 0, 0, 0, 0, 0, 0, 0⟩),
  (Int.negSucc 4881183108979098648575, ⟨0, 0, 0, 0, 1, 0, 0, 0⟩),
  (Int.ofNat 599023504961572962304, ⟨0, 0, 0, 0, 2, 0, 0, 0⟩),
  (Int.negSucc 496948293507313827839, ⟨0, 0, 0, 0, 3, 0, 0, 0⟩),
  (Int.negSucc 24509715072057081855, ⟨0, 0, 0, 0, 0, 1, 0, 0⟩),
  (Int.negSucc 372081208763862745087, ⟨0, 0, 0, 0, 1, 1, 0, 0⟩),
  (Int.negSucc 66532240245097758719, ⟨0, 0, 0, 0, 2, 1, 0, 0⟩),
  (Int.negSucc 36406817912686379007, ⟨0, 0, 0, 0, 0, 2, 0, 0⟩),
  (Int.negSucc 546102268690295685119, ⟨0, 0, 0, 0, 1, 2, 0, 0⟩),
  (Int.ofNat 624124036009745711104, ⟨0, 0, 0, 0, 0, 0, 1, 0⟩),
  (Int.ofNat 9319694462735022555136, ⟨0, 0, 0, 0, 1, 0, 1, 0⟩),
  (Int.negSucc 632491161167446671359, ⟨0, 0, 0, 0, 2, 0, 1, 0⟩),
  (Int.ofNat 24859869943085137920, ⟨0, 0, 0, 0, 0, 1, 1, 0⟩),
  (Int.ofNat 372898049146277068800, ⟨0, 0, 0, 0, 1, 1, 1, 0⟩),
  (Int.negSucc 326901941727012061183, ⟨0, 0, 0, 0, 0, 0, 2, 0⟩),
  (Int.negSucc 4903529125905180917759, ⟨0, 0, 0, 0, 1, 0, 2, 0⟩),
  (Int.ofNat 1641108889464041635840, ⟨0, 0, 0, 0, 0, 1, 0, 1⟩),
  (Int.negSucc 210717797065131294719, ⟨0, 0, 0, 0, 1, 1, 0, 1⟩),
  (Int.ofNat 165649431169104609280, ⟨0, 0, 0, 0, 2, 1, 0, 1⟩),
  (Int.ofNat 122548575360285409280, ⟨0, 0, 0, 0, 0, 2, 0, 1⟩),
  (Int.ofNat 22177413415032586240, ⟨0, 0, 0, 0, 1, 2, 0, 1⟩),
  (Int.ofNat 182034089563431895040, ⟨0, 0, 0, 0, 0, 3, 0, 1⟩),
  (Int.ofNat 1641108889464041635840, ⟨0, 0, 0, 0, 0, 0, 1, 1⟩),
  (Int.negSucc 210717797065131294719, ⟨0, 0, 0, 0, 1, 0, 1, 1⟩),
  (Int.ofNat 165649431169104609280, ⟨0, 0, 0, 0, 2, 0, 1, 1⟩),
  (Int.negSucc 2998071604688443146239, ⟨0, 0, 0, 0, 0, 1, 1, 1⟩),
  (Int.ofNat 233007800470848143360, ⟨0, 0, 0, 0, 1, 1, 1, 1⟩),
  (Int.ofNat 57734739848006205440, ⟨0, 0, 0, 0, 0, 2, 1, 1⟩),
  (Int.negSucc 3120620180048728555519, ⟨0, 0, 0, 0, 0, 0, 2, 1⟩),
  (Int.ofNat 210830387055815557120, ⟨0, 0, 0, 0, 1, 0, 2, 1⟩),
  (Int.ofNat 1510210358919634616320, ⟨0, 0, 0, 0, 0, 1, 2, 1⟩),
  (Int.ofNat 1634509708635060305920, ⟨0, 0, 0, 0, 0, 0, 3, 1⟩)]
noncomputable def weighted : Polynomial := weighted_0
noncomputable def weight : ℤ := 2700000000
end Certificate.SOS.H2B010
