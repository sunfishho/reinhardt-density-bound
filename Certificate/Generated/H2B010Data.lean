import Certificate.FastGram

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Certificate.Generated.H2B010
noncomputable def a_0 : List ℤ := [Int.ofNat 328221777892808327168, Int.negSucc 21071779706513129471, Int.ofNat 12254857536028540928, Int.negSucc 312062018004872855551]
noncomputable def a_1 : List ℤ := [Int.negSucc 21071779706513129471, Int.ofNat 33129886233820921856, Int.ofNat 2217741341503258624, Int.ofNat 21083038705581555712]
noncomputable def a_2 : List ℤ := [Int.ofNat 12254857536028540928, Int.ofNat 2217741341503258624, Int.ofNat 36406817912686379008, Int.negSucc 12429934971542568959]
noncomputable def a_3 : List ℤ := [Int.negSucc 312062018004872855551, Int.ofNat 21083038705581555712, Int.negSucc 12429934971542568959, Int.ofNat 326901941727012061184]
noncomputable def a : List (List ℤ) := [a_0, a_1, a_2, a_3]
noncomputable def b_0 : List ℤ := [Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0]
noncomputable def b_1 : List ℤ := [Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0]
noncomputable def b_2 : List ℤ := [Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0]
noncomputable def b_3 : List ℤ := [Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0]
noncomputable def b : List (List ℤ) := [b_0, b_1, b_2, b_3]
noncomputable def factor_0 : List ℤ := [Int.ofNat 18053141967, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0]
noncomputable def factor_1 : List ℤ := [Int.negSucc 1167208441, Int.ofNat 5427860322, Int.ofNat 0, Int.ofNat 0]
noncomputable def factor_2 : List ℤ := [Int.ofNat 678821313, Int.ofNat 554558727, Int.ofNat 5773442746, Int.ofNat 0]
noncomputable def factor_3 : List ℤ := [Int.negSucc 17285745526, Int.ofNat 167095420, Int.negSucc 136602500, Int.ofNat 5074693998]
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
end Certificate.Generated.H2B010
