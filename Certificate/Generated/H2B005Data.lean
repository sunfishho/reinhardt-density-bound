import Certificate.FastGram

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Certificate.Generated.H2B005
noncomputable def a_0 : List ℤ := [Int.ofNat 74931593724682135666688, Int.ofNat 0, Int.negSucc 60630554408405434367, Int.negSucc 74676805953463370383359]
noncomputable def a_1 : List ℤ := [Int.ofNat 0, Int.ofNat 118283103563212128256, Int.ofNat 0, Int.ofNat 0]
noncomputable def a_2 : List ℤ := [Int.negSucc 60630554408405434367, Int.ofNat 0, Int.ofNat 120390788188821520384, Int.ofNat 59601481893551276032]
noncomputable def a_3 : List ℤ := [Int.negSucc 74676805953463370383359, Int.ofNat 0, Int.ofNat 59601481893551276032, Int.ofNat 74453862572259788455936]
noncomputable def a : List (List ℤ) := [a_0, a_1, a_2, a_3]
noncomputable def b_0 : List ℤ := [Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0]
noncomputable def b_1 : List ℤ := [Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0]
noncomputable def b_2 : List ℤ := [Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0]
noncomputable def b_3 : List ℤ := [Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0]
noncomputable def b : List (List ℤ) := [b_0, b_1, b_2, b_3]
noncomputable def factor_0 : List ℤ := [Int.ofNat 273732146234, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0]
noncomputable def factor_1 : List ℤ := [Int.ofNat 0, Int.ofNat 10769273910, Int.ofNat 0, Int.ofNat 0]
noncomputable def factor_2 : List ℤ := [Int.negSucc 221495922, Int.ofNat 0, Int.ofNat 10864432094, Int.ofNat 0]
noncomputable def factor_3 : List ℤ := [Int.negSucc 272809777663, Int.ofNat 0, Int.negSucc 75914840, Int.ofNat 5135774251]
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
end Certificate.Generated.H2B005
