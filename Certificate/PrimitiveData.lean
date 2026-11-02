import Certificate.MultiplierSoundness
namespace Certificate.PrimitiveData
open Certificate.Sparse
noncomputable def sector1 : Polynomial := [(Int.ofNat 1, ⟨0, 0, 1, 0, 0, 0, 0, 0⟩)]
noncomputable def sector2 : Polynomial := [(Int.negSucc 0, ⟨0, 0, 1, 0, 0, 0, 0, 0⟩), (Int.ofNat 1, ⟨0, 0, 0, 1, 0, 0, 0, 1⟩)]
noncomputable def sector1Rot1 : Polynomial := [(Int.negSucc 2, ⟨0, 1, 0, 0, 0, 0, 0, 0⟩), (Int.ofNat 1, ⟨0, 0, 1, 0, 0, 0, 0, 0⟩), (Int.ofNat 1, ⟨1, 0, 0, 0, 0, 0, 0, 1⟩), (Int.negSucc 0, ⟨0, 0, 0, 1, 0, 0, 0, 1⟩)]
noncomputable def sector2Rot1 : Polynomial := [(Int.ofNat 3, ⟨0, 1, 0, 0, 0, 0, 0, 0⟩), (Int.ofNat 1, ⟨0, 0, 1, 0, 0, 0, 0, 0⟩), (Int.ofNat 1, ⟨1, 0, 0, 0, 0, 0, 0, 1⟩), (Int.ofNat 1, ⟨0, 0, 0, 1, 0, 0, 0, 1⟩)]
noncomputable def sector1Rot2 : Polynomial := [(Int.negSucc 2, ⟨0, 1, 0, 0, 0, 0, 0, 0⟩), (Int.ofNat 1, ⟨0, 0, 1, 0, 0, 0, 0, 0⟩), (Int.negSucc 0, ⟨1, 0, 0, 0, 0, 0, 0, 1⟩), (Int.ofNat 1, ⟨0, 0, 0, 1, 0, 0, 0, 1⟩)]
noncomputable def sector2Rot2 : Polynomial := [(Int.negSucc 0, ⟨0, 0, 1, 0, 0, 0, 0, 0⟩), (Int.ofNat 1, ⟨1, 0, 0, 0, 0, 0, 0, 1⟩)]
noncomputable def gNorm : Polynomial := [(Int.ofNat 16, ⟨0, 0, 0, 0, 0, 0, 0, 0⟩), (Int.negSucc 4, ⟨2, 0, 0, 0, 0, 0, 0, 0⟩), (Int.negSucc 4, ⟨0, 2, 0, 0, 0, 0, 0, 0⟩), (Int.negSucc 4, ⟨0, 0, 2, 0, 0, 0, 0, 0⟩), (Int.negSucc 4, ⟨0, 0, 0, 2, 0, 0, 0, 0⟩)]
noncomputable def denominator0 : Polynomial := [(Int.negSucc 2306, ⟨0, 0, 0, 0, 0, 0, 0, 0⟩), (Int.negSucc 39999, ⟨0, 0, 0, 0, 0, 1, 0, 0⟩), (Int.ofNat 20000, ⟨0, 0, 0, 0, 0, 0, 1, 0⟩)]
noncomputable def denominator1 : Polynomial := [(Int.negSucc 2306, ⟨0, 0, 0, 0, 0, 0, 0, 0⟩), (Int.ofNat 20000, ⟨0, 0, 0, 0, 0, 1, 0, 0⟩), (Int.ofNat 20000, ⟨0, 0, 0, 0, 0, 0, 1, 0⟩), (Int.negSucc 19999, ⟨0, 0, 0, 0, 1, 0, 0, 1⟩)]
noncomputable def denominator2 : Polynomial := [(Int.negSucc 2306, ⟨0, 0, 0, 0, 0, 0, 0, 0⟩), (Int.ofNat 20000, ⟨0, 0, 0, 0, 0, 1, 0, 0⟩), (Int.ofNat 20000, ⟨0, 0, 0, 0, 0, 0, 1, 0⟩), (Int.ofNat 20000, ⟨0, 0, 0, 0, 1, 0, 0, 1⟩)]
noncomputable def hLower : Polynomial := [(Int.negSucc 0, ⟨0, 0, 0, 0, 0, 0, 0, 0⟩), (Int.ofNat 1, ⟨0, 0, 0, 0, 0, 0, 1, 0⟩)]
noncomputable def hUpper : Polynomial := [(Int.ofNat 12, ⟨0, 0, 0, 0, 0, 0, 0, 0⟩), (Int.negSucc 4, ⟨0, 0, 0, 0, 0, 0, 1, 0⟩)]
noncomputable def xNorm : Polynomial := [(Int.ofNat 119, ⟨0, 0, 0, 0, 0, 0, 0, 0⟩), (Int.negSucc 24, ⟨0, 0, 0, 0, 2, 0, 0, 0⟩), (Int.negSucc 24, ⟨0, 0, 0, 0, 0, 2, 0, 0⟩)]
noncomputable def horoballY : Polynomial := [(Int.negSucc 1, ⟨0, 0, 0, 0, 0, 0, 0, 0⟩), (Int.ofNat 9, ⟨0, 0, 0, 0, 0, 1, 0, 0⟩), (Int.ofNat 9, ⟨0, 0, 0, 0, 0, 0, 1, 0⟩)]
noncomputable def horoballPlus : Polynomial := [(Int.ofNat 27, ⟨0, 0, 0, 0, 0, 0, 0, 0⟩), (Int.ofNat 27, ⟨0, 0, 0, 0, 2, 0, 0, 0⟩), (Int.negSucc 7, ⟨0, 0, 0, 0, 0, 1, 0, 0⟩), (Int.ofNat 9, ⟨0, 0, 0, 0, 0, 2, 0, 0⟩), (Int.negSucc 7, ⟨0, 0, 0, 0, 0, 0, 1, 0⟩), (Int.ofNat 18, ⟨0, 0, 0, 0, 0, 1, 1, 0⟩), (Int.ofNat 9, ⟨0, 0, 0, 0, 0, 0, 2, 0⟩), (Int.negSucc 17, ⟨0, 0, 0, 0, 1, 1, 0, 1⟩), (Int.negSucc 17, ⟨0, 0, 0, 0, 1, 0, 1, 1⟩)]
noncomputable def horoballMinus : Polynomial := [(Int.ofNat 27, ⟨0, 0, 0, 0, 0, 0, 0, 0⟩), (Int.ofNat 27, ⟨0, 0, 0, 0, 2, 0, 0, 0⟩), (Int.negSucc 7, ⟨0, 0, 0, 0, 0, 1, 0, 0⟩), (Int.ofNat 9, ⟨0, 0, 0, 0, 0, 2, 0, 0⟩), (Int.negSucc 7, ⟨0, 0, 0, 0, 0, 0, 1, 0⟩), (Int.ofNat 18, ⟨0, 0, 0, 0, 0, 1, 1, 0⟩), (Int.ofNat 9, ⟨0, 0, 0, 0, 0, 0, 2, 0⟩), (Int.ofNat 18, ⟨0, 0, 0, 0, 1, 1, 0, 1⟩), (Int.ofNat 18, ⟨0, 0, 0, 0, 1, 0, 1, 1⟩)]
noncomputable def halfplane0 : Polynomial := [(Int.negSucc 0, ⟨0, 0, 0, 0, 0, 0, 0, 0⟩), (Int.negSucc 14, ⟨0, 0, 0, 0, 1, 0, 0, 0⟩), (Int.ofNat 5, ⟨0, 0, 0, 0, 0, 1, 0, 1⟩), (Int.ofNat 5, ⟨0, 0, 0, 0, 0, 0, 1, 1⟩)]
noncomputable def halfplane1 : Polynomial := [(Int.negSucc 0, ⟨0, 0, 0, 0, 0, 0, 0, 0⟩), (Int.negSucc 9, ⟨0, 0, 0, 0, 0, 1, 0, 1⟩), (Int.ofNat 5, ⟨0, 0, 0, 0, 0, 0, 1, 1⟩)]
noncomputable def halfplane2 : Polynomial := [(Int.negSucc 0, ⟨0, 0, 0, 0, 0, 0, 0, 0⟩), (Int.ofNat 15, ⟨0, 0, 0, 0, 1, 0, 0, 0⟩), (Int.ofNat 5, ⟨0, 0, 0, 0, 0, 1, 0, 1⟩), (Int.ofNat 5, ⟨0, 0, 0, 0, 0, 0, 1, 1⟩)]
noncomputable def polynomial : ConstraintLabel → Polynomial
  | .sector1 => sector1
  | .sector2 => sector2
  | .sector1Rot1 => sector1Rot1
  | .sector2Rot1 => sector2Rot1
  | .sector1Rot2 => sector1Rot2
  | .sector2Rot2 => sector2Rot2
  | .gNorm => gNorm
  | .denominator0 => denominator0
  | .denominator1 => denominator1
  | .denominator2 => denominator2
  | .hLower => hLower
  | .hUpper => hUpper
  | .xNorm => xNorm
  | .horoballY => horoballY
  | .horoballPlus => horoballPlus
  | .horoballMinus => horoballMinus
  | .halfplane0 => halfplane0
  | .halfplane1 => halfplane1
  | .halfplane2 => halfplane2
def Region (x : Fin 8 → ℝ) : Prop := ∀ label, 0 ≤ eval x (polynomial label)
end Certificate.PrimitiveData
