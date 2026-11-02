import Certificate.FastGram

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Certificate.Generated.H2B015
noncomputable def a_0 : List ℤ := [Int.ofNat 55481492689990711246848, Int.negSucc 356065845538979839, Int.negSucc 34083408894601103147007, Int.negSucc 54922594850334125850623]
noncomputable def a_1 : List ℤ := [Int.negSucc 356065845538979839, Int.ofNat 11612970740138492559360, Int.ofNat 236157505460240384, Int.ofNat 355221420608847872]
noncomputable def a_2 : List ℤ := [Int.negSucc 34083408894601103147007, Int.ofNat 236157505460240384, Int.ofNat 22690520061052951986176, Int.ofNat 34022818309639390625792]
noncomputable def a_3 : List ℤ := [Int.negSucc 54922594850334125850623, Int.ofNat 355221420608847872, Int.ofNat 34022818309639390625792, Int.ofNat 54643552380372203339776]
noncomputable def a : List (List ℤ) := [a_0, a_1, a_2, a_3]
noncomputable def b_0 : List ℤ := [Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0]
noncomputable def b_1 : List ℤ := [Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0]
noncomputable def b_2 : List ℤ := [Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0]
noncomputable def b_3 : List ℤ := [Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0]
noncomputable def b : List (List ℤ) := [b_0, b_1, b_2, b_3]
noncomputable def factor_0 : List ℤ := [Int.ofNat 235505936116, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0]
noncomputable def factor_1 : List ℤ := [Int.negSucc 1511918, Int.ofNat 107677871421, Int.ofNat 0, Int.ofNat 0]
noncomputable def factor_2 : List ℤ := [Int.negSucc 144724202950, Int.ofNat 161094, Int.ofNat 41556929593, Int.ofNat 0]
noncomputable def factor_3 : List ℤ := [Int.negSucc 233211084849, Int.ofNat 24380, Int.ofNat 6533926785, Int.ofNat 13964359634]
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
end Certificate.Generated.H2B015
