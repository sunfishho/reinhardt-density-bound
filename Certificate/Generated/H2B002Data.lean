import Certificate.FastGram

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Certificate.Generated.H2B002
noncomputable def a_0 : List ℤ := [Int.ofNat 3990037554837812412416, Int.negSucc 266086176783931015167, Int.ofNat 154714691273849044992, Int.negSucc 3965896290510269579263]
noncomputable def a_1 : List ℤ := [Int.negSucc 266086176783931015167, Int.ofNat 244053441506927706112, Int.ofNat 29064824620165627904, Int.ofNat 266248587845493063680]
noncomputable def a_2 : List ℤ := [Int.ofNat 154714691273849044992, Int.ofNat 29064824620165627904, Int.ofNat 286889147887685468160, Int.negSucc 156996327435065622527]
noncomputable def a_3 : List ℤ := [Int.negSucc 3965896290510269579263, Int.ofNat 266248587845493063680, Int.negSucc 156996327435065622527, Int.ofNat 3973365791967240257536]
noncomputable def a : List (List ℤ) := [a_0, a_1, a_2, a_3]
noncomputable def b_0 : List ℤ := [Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0]
noncomputable def b_1 : List ℤ := [Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0]
noncomputable def b_2 : List ℤ := [Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0]
noncomputable def b_3 : List ℤ := [Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0]
noncomputable def b : List (List ℤ) := [b_0, b_1, b_2, b_3]
noncomputable def factor_0 : List ℤ := [Int.ofNat 63148489387, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0]
noncomputable def factor_1 : List ℤ := [Int.negSucc 4213658621, Int.ofNat 14966384985, Int.ofNat 0, Int.ofNat 0]
noncomputable def factor_2 : List ℤ := [Int.ofNat 2450014130, Int.ofNat 2631787691, Int.ofNat 16481942519, Int.ofNat 0]
noncomputable def factor_3 : List ℤ := [Int.negSucc 62802710389, Int.ofNat 108202864, Int.negSucc 207109480, Int.ofNat 5179277407]
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
end Certificate.Generated.H2B002
