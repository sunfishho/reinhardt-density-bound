import Certificate.FastGram

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Certificate.Generated.H2B019
noncomputable def a_0 : List ℤ := [Int.ofNat 26841713299056683384832, Int.negSucc 92148433450604429311, Int.ofNat 29156866937550012416, Int.negSucc 26764795476595892551679]
noncomputable def a_1 : List ℤ := [Int.negSucc 92148433450604429311, Int.ofNat 180729453046378004480, Int.ofNat 21568864515384147968, Int.ofNat 92513225020421439488]
noncomputable def a_2 : List ℤ := [Int.ofNat 29156866937550012416, Int.ofNat 21568864515384147968, Int.ofNat 212373714353120083968, Int.negSucc 31063015479834574847]
noncomputable def a_3 : List ℤ := [Int.negSucc 26764795476595892551679, Int.ofNat 92513225020421439488, Int.negSucc 31063015479834574847, Int.ofNat 26719382866803348733952]
noncomputable def a : List (List ℤ) := [a_0, a_1, a_2, a_3]
noncomputable def b_0 : List ℤ := [Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0]
noncomputable def b_1 : List ℤ := [Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0]
noncomputable def b_2 : List ℤ := [Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0]
noncomputable def b_3 : List ℤ := [Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0]
noncomputable def b : List (List ℤ) := [b_0, b_1, b_2, b_3]
noncomputable def factor_0 : List ℤ := [Int.ofNat 163827370900, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0]
noncomputable def factor_1 : List ℤ := [Int.negSucc 562472759, Int.ofNat 13345682239, Int.ofNat 0, Int.ofNat 0]
noncomputable def factor_2 : List ℤ := [Int.ofNat 177973111, Int.ofNat 1623668926, Int.ofNat 14401385216, Int.ofNat 0]
noncomputable def factor_3 : List ℤ := [Int.negSucc 163371940411, Int.ofNat 46528817, Int.negSucc 143232771, Int.ofNat 5163664315]
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
end Certificate.Generated.H2B019
