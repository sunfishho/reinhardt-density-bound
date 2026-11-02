import Certificate.FastGram

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Certificate.Generated.H2B003
noncomputable def a_0 : List ℤ := [Int.ofNat 3990035865987952148480, Int.ofNat 266101376432673390592, Int.ofNat 154686262301201268736, Int.negSucc 3965894320185432604671]
noncomputable def a_1 : List ℤ := [Int.ofNat 266101376432673390592, Int.ofNat 244072018855390609408, Int.negSucc 29076365094210764799, Int.negSucc 266263506019258728447]
noncomputable def a_2 : List ℤ := [Int.ofNat 154686262301201268736, Int.negSucc 29076365094210764799, Int.ofNat 286869163164339011584, Int.negSucc 156967616987441135615]
noncomputable def a_3 : List ℤ := [Int.negSucc 3965894320185432604671, Int.negSucc 266263506019258728447, Int.negSucc 156967616987441135615, Int.ofNat 3973363540167426572288]
noncomputable def a : List (List ℤ) := [a_0, a_1, a_2, a_3]
noncomputable def b_0 : List ℤ := [Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0]
noncomputable def b_1 : List ℤ := [Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0]
noncomputable def b_2 : List ℤ := [Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0]
noncomputable def b_3 : List ℤ := [Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0]
noncomputable def b : List (List ℤ) := [b_0, b_1, b_2, b_3]
noncomputable def factor_0 : List ℤ := [Int.ofNat 63148476015, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0]
noncomputable def factor_1 : List ℤ := [Int.ofNat 4213900211, Int.ofNat 14966937591, Int.ofNat 0, Int.ofNat 0]
noncomputable def factor_2 : List ℤ := [Int.ofNat 2449564456, Int.negSucc 2632374527, Int.ofNat 16481309368, Int.ofNat 0]
noncomputable def factor_3 : List ℤ := [Int.negSucc 62802692486, Int.negSucc 108186918, Int.negSucc 207092903, Int.ofNat 5179278100]
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
end Certificate.Generated.H2B003
