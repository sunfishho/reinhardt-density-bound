import Certificate.FastGram

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Certificate.Generated.H2B016
noncomputable def a_0 : List ℤ := [Int.ofNat 26245353954749676781568, Int.negSucc 4503599627370495, Int.negSucc 135893866956091031551, Int.negSucc 26168797546158982430719]
noncomputable def a_1 : List ℤ := [Int.negSucc 4503599627370495, Int.ofNat 221929789812446855168, Int.ofNat 7881299347898368, Int.ofNat 4503599627370496]
noncomputable def a_2 : List ℤ := [Int.negSucc 135893866956091031551, Int.ofNat 7881299347898368, Int.ofNat 169939672764128428032, Int.ofNat 135257452033748238336]
noncomputable def a_3 : List ℤ := [Int.negSucc 26168797546158982430719, Int.ofNat 4503599627370496, Int.ofNat 135257452033748238336, Int.ofNat 26123738750412163907584]
noncomputable def a : List (List ℤ) := [a_0, a_1, a_2, a_3]
noncomputable def b_0 : List ℤ := [Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0]
noncomputable def b_1 : List ℤ := [Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0]
noncomputable def b_2 : List ℤ := [Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0]
noncomputable def b_3 : List ℤ := [Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0]
noncomputable def b : List (List ℤ) := [b_0, b_1, b_2, b_3]
noncomputable def factor_0 : List ℤ := [Int.ofNat 161997062047, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0]
noncomputable def factor_1 : List ℤ := [Int.negSucc 27800, Int.ofNat 14819714802, Int.ofNat 0, Int.ofNat 0]
noncomputable def factor_2 : List ℤ := [Int.negSucc 838866243, Int.ofNat 530238, Int.ofNat 12920144461, Int.ofNat 0]
noncomputable def factor_3 : List ℤ := [Int.negSucc 161538716909, Int.ofNat 860, Int.negSucc 19498594, Int.ofNat 5164829752]
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
end Certificate.Generated.H2B016
