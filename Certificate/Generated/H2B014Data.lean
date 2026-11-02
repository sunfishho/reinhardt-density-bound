import Certificate.FastGram

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Certificate.Generated.H2B014
noncomputable def a_0 : List ℤ := [Int.ofNat 28184032560092689727488, Int.ofNat 1102805447953468096512, Int.negSucc 622280937862244335615, Int.negSucc 28094849746996708769791]
noncomputable def a_1 : List ℤ := [Int.ofNat 1102805447953468096512, Int.ofNat 499562633091002400768, Int.negSucc 69596658316546670591, Int.negSucc 1102012814419050889215]
noncomputable def a_2 : List ℤ := [Int.negSucc 622280937862244335615, Int.negSucc 69596658316546670591, Int.ofNat 420711921965139492864, Int.ofNat 619066212153231933440]
noncomputable def a_3 : List ℤ := [Int.negSucc 28094849746996708769791, Int.negSucc 1102012814419050889215, Int.ofNat 619066212153231933440, Int.ofNat 28037853034537637904384]
noncomputable def a : List (List ℤ) := [a_0, a_1, a_2, a_3]
noncomputable def b_0 : List ℤ := [Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0]
noncomputable def b_1 : List ℤ := [Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0]
noncomputable def b_2 : List ℤ := [Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0]
noncomputable def b_3 : List ℤ := [Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0]
noncomputable def b : List (List ℤ) := [b_0, b_1, b_2, b_3]
noncomputable def factor_0 : List ℤ := [Int.ofNat 167874139513, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0]
noncomputable def factor_1 : List ℤ := [Int.ofNat 6569239617, Int.ofNat 21309666373, Int.ofNat 0, Int.ofNat 0]
noncomputable def factor_2 : List ℤ := [Int.negSucc 3706830245, Int.negSucc 2123243105, Int.ofNat 20003932793, Int.ofNat 0]
noncomputable def factor_3 : List ℤ := [Int.negSucc 167356626985, Int.negSucc 122340265, Int.negSucc 77792339, Int.ofNat 5223559765]
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
end Certificate.Generated.H2B014
