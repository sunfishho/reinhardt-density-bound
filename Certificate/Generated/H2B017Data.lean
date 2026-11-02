import Certificate.FastGram

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Certificate.Generated.H2B017
noncomputable def a_0 : List ℤ := [Int.ofNat 25365775051826361532416, Int.negSucc 44473046320283647, Int.ofNat 1162969598325463973888, Int.negSucc 25297774075152787570687]
noncomputable def a_1 : List ℤ := [Int.negSucc 44473046320283647, Int.ofNat 370823015617966112768, Int.negSucc 20547673299877887, Int.ofNat 44473046320283648]
noncomputable def a_2 : List ℤ := [Int.ofNat 1162969598325463973888, Int.negSucc 20547673299877887, Int.ofNat 552094307994512130048, Int.negSucc 1167063088911767044095]
noncomputable def a_3 : List ℤ := [Int.negSucc 25297774075152787570687, Int.ofNat 44473046320283648, Int.negSucc 1167063088911767044095, Int.ofNat 25261918948194454077440]
noncomputable def a : List (List ℤ) := [a_0, a_1, a_2, a_3]
noncomputable def b_0 : List ℤ := [Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0]
noncomputable def b_1 : List ℤ := [Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0]
noncomputable def b_2 : List ℤ := [Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0]
noncomputable def b_3 : List ℤ := [Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0]
noncomputable def b : List (List ℤ) := [b_0, b_1, b_2, b_3]
noncomputable def factor_0 : List ℤ := [Int.ofNat 159259125983, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0]
noncomputable def factor_1 : List ℤ := [Int.negSucc 279249, Int.ofNat 19196801102, Int.ofNat 0, Int.ofNat 0]
noncomputable def factor_2 : List ℤ := [Int.ofNat 7302373356, Int.negSucc 964143, Int.ofNat 22281467802, Int.ofNat 0]
noncomputable def factor_3 : List ℤ := [Int.negSucc 158846621309, Int.ofNat 6001, Int.negSucc 318908689, Int.ofNat 5221331328]
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
end Certificate.Generated.H2B017
