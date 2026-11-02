import Certificate.FastGram

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Certificate.Generated.H2B006
noncomputable def a_0 : List ℤ := [Int.ofNat 13751778335397758631936, Int.ofNat 0, Int.negSucc 12220799063846551551, Int.negSucc 13695416067536193585151]
noncomputable def a_1 : List ℤ := [Int.ofNat 0, Int.ofNat 45663122521816301568, Int.ofNat 0, Int.ofNat 0]
noncomputable def a_2 : List ℤ := [Int.negSucc 12220799063846551551, Int.ofNat 0, Int.ofNat 46273641746301714432, Int.ofNat 11941294411972870144]
noncomputable def a_3 : List ℤ := [Int.negSucc 13695416067536193585151, Int.ofNat 0, Int.ofNat 11941294411972870144, Int.ofNat 13670176769324502482944]
noncomputable def a : List (List ℤ) := [a_0, a_1, a_2, a_3]
noncomputable def b_0 : List ℤ := [Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0]
noncomputable def b_1 : List ℤ := [Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0]
noncomputable def b_2 : List ℤ := [Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0]
noncomputable def b_3 : List ℤ := [Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0]
noncomputable def b : List (List ℤ) := [b_0, b_1, b_2, b_3]
noncomputable def factor_0 : List ℤ := [Int.ofNat 117258144674, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0]
noncomputable def factor_1 : List ℤ := [Int.ofNat 0, Int.ofNat 6584624478, Int.ofNat 0, Int.ofNat 0]
noncomputable def factor_2 : List ℤ := [Int.negSucc 104221323, Int.ofNat 0, Int.ofNat 6630002764, Int.ofNat 0]
noncomputable def factor_3 : List ℤ := [Int.negSucc 116797141090, Int.ofNat 0, Int.negSucc 34910731, Int.ofNat 5128112769]
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
end Certificate.Generated.H2B006
