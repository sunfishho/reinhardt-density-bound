import Certificate.FastGram

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Certificate.Generated.H2B021
noncomputable def a_0 : List ℤ := [Int.ofNat 26841706262182265618432, Int.ofNat 92152655575255089152, Int.ofNat 29149267113178824704, Int.negSucc 26764788158246498074623]
noncomputable def a_1 : List ℤ := [Int.ofNat 92152655575255089152, Int.ofNat 180742963845260115968, Int.negSucc 21577308764685467647, Int.negSucc 92517447145072099327]
noncomputable def a_2 : List ℤ := [Int.ofNat 29149267113178824704, Int.negSucc 21577308764685467647, Int.ofNat 212359359129307840512, Int.negSucc 31055415655463387135]
noncomputable def a_3 : List ℤ := [Int.negSucc 26764788158246498074623, Int.negSucc 92517447145072099327, Int.negSucc 31055415655463387135, Int.ofNat 26719375548453954256896]
noncomputable def a : List (List ℤ) := [a_0, a_1, a_2, a_3]
noncomputable def b_0 : List ℤ := [Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0]
noncomputable def b_1 : List ℤ := [Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0]
noncomputable def b_2 : List ℤ := [Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0]
noncomputable def b_3 : List ℤ := [Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0]
noncomputable def b : List (List ℤ) := [b_0, b_1, b_2, b_3]
noncomputable def factor_0 : List ℤ := [Int.ofNat 163827349424, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0]
noncomputable def factor_1 : List ℤ := [Int.ofNat 562498605, Int.ofNat 13346187327, Int.ofNat 0, Int.ofNat 0]
noncomputable def factor_2 : List ℤ := [Int.ofNat 177926746, Int.negSucc 1624238576, Int.ofNat 14400823144, Int.ofNat 0]
noncomputable def factor_3 : List ℤ := [Int.negSucc 163371917157, Int.negSucc 46528013, Int.negSucc 143238666, Int.ofNat 5163691258]
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
end Certificate.Generated.H2B021
