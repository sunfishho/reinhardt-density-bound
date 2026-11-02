import Certificate.FastGram

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Certificate.Generated.H2B020
noncomputable def a_0 : List ℤ := [Int.ofNat 60908494622358557949952, Int.ofNat 32256949858873001377792, Int.ofNat 20398736163976001880064, Int.negSucc 60670457708478820515839]
noncomputable def a_1 : List ℤ := [Int.ofNat 32256949858873001377792, Int.ofNat 21063522919546299088896, Int.ofNat 6399701201836348276736, Int.negSucc 32348087797157214552063]
noncomputable def a_2 : List ℤ := [Int.ofNat 20398736163976001880064, Int.ofNat 6399701201836348276736, Int.ofNat 16106324115406767259648, Int.negSucc 20527152929650751045631]
noncomputable def a_3 : List ℤ := [Int.negSucc 60670457708478820515839, Int.negSucc 32348087797157214552063, Int.negSucc 20527152929650751045631, Int.ofNat 60708225176428926205952]
noncomputable def a : List (List ℤ) := [a_0, a_1, a_2, a_3]
noncomputable def b_0 : List ℤ := [Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0]
noncomputable def b_1 : List ℤ := [Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0]
noncomputable def b_2 : List ℤ := [Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0]
noncomputable def b_3 : List ℤ := [Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0]
noncomputable def b : List (List ℤ) := [b_0, b_1, b_2, b_3]
noncomputable def factor_0 : List ℤ := [Int.ofNat 246759088745, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0]
noncomputable def factor_1 : List ℤ := [Int.ofNat 130722438727, Int.ofNat 62902465680, Int.ofNat 0, Int.ofNat 0]
noncomputable def factor_2 : List ℤ := [Int.ofNat 82666605180, Int.negSucc 70055743935, Int.ofNat 65926493163, Int.ofNat 0]
noncomputable def factor_3 : List ℤ := [Int.negSucc 245869191756, Int.negSucc 3298240227, Int.negSucc 6568561145, Int.ofNat 13568146259]
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
end Certificate.Generated.H2B020
