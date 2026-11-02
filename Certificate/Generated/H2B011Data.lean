import Certificate.FastGram

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Certificate.Generated.H2B011
noncomputable def a_0 : List ℤ := [Int.ofNat 390192716140309905408, Int.negSucc 1125899906842623, Int.negSucc 24907157739172528127, Int.negSucc 373581470389730541567]
noncomputable def a_1 : List ℤ := [Int.negSucc 1125899906842623, Int.ofNat 37385506406709329920, Int.ofNat 844424930131968, Int.ofNat 1125899906842624]
noncomputable def a_2 : List ℤ := [Int.negSucc 24907157739172528127, Int.ofNat 844424930131968, Int.ofNat 32038607749113708544, Int.ofNat 24814552471834722304]
noncomputable def a_3 : List ℤ := [Int.negSucc 373581470389730541567, Int.ofNat 1125899906842624, Int.ofNat 24814552471834722304, Int.ofNat 387970471199179276288]
noncomputable def a : List (List ℤ) := [a_0, a_1, a_2, a_3]
noncomputable def b_0 : List ℤ := [Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0]
noncomputable def b_1 : List ℤ := [Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0]
noncomputable def b_2 : List ℤ := [Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0]
noncomputable def b_3 : List ℤ := [Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0]
noncomputable def b : List (List ℤ) := [b_0, b_1, b_2, b_3]
noncomputable def factor_0 : List ℤ := [Int.ofNat 19694843821, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0]
noncomputable def factor_1 : List ℤ := [Int.negSucc 57166, Int.ofNat 5922808742, Int.ofNat 0, Int.ofNat 0]
noncomputable def factor_2 : List ℤ := [Int.negSucc 1264653731, Int.ofNat 130365, Int.ofNat 5304094236, Int.ofNat 0]
noncomputable def factor_3 : List ℤ := [Int.negSucc 18968491132, Int.ofNat 7011, Int.ofNat 155724867, Int.ofNat 5082983581]
noncomputable def factor : List (List ℤ) := [factor_0, factor_1, factor_2, factor_3]
noncomputable def data : GramData where
  size := 4
  den := 309485009821345068724781056
  c := 1
  scale := 1461501637330902918203684832716283019655932542976
  lo := 2531395091202226821444082793948437699496376808652
  hi := 2531395091202226821444082793948437699496376808653
  a := a
  b := b
  factor := factor
end Certificate.Generated.H2B011
