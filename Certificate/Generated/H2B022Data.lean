import Certificate.FastGram

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Certificate.Generated.H2B022
noncomputable def a_0 : List ℤ := [Int.ofNat 16262046768572217163776, Int.ofNat 1407374883553280, Int.negSucc 227882704094900518911, Int.negSucc 16157960136934383681535]
noncomputable def a_1 : List ℤ := [Int.ofNat 1407374883553280, Int.ofNat 14828331175223377264640, Int.ofNat 18014398509481984, Int.negSucc 1407374883553279]
noncomputable def a_2 : List ℤ := [Int.negSucc 227882704094900518911, Int.ofNat 18014398509481984, Int.ofNat 14490672104311414063104, Int.ofNat 144960175955941261312]
noncomputable def a_3 : List ℤ := [Int.negSucc 16157960136934383681535, Int.negSucc 1407374883553279, Int.ofNat 144960175955941261312, Int.ofNat 16188962353819248754688]
noncomputable def a : List (List ℤ) := [a_0, a_1, a_2, a_3]
noncomputable def b_0 : List ℤ := [Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0]
noncomputable def b_1 : List ℤ := [Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0]
noncomputable def b_2 : List ℤ := [Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0]
noncomputable def b_3 : List ℤ := [Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0]
noncomputable def b : List (List ℤ) := [b_0, b_1, b_2, b_3]
noncomputable def factor_0 : List ℤ := [Int.ofNat 127486561631, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0]
noncomputable def factor_1 : List ℤ := [Int.ofNat 11039, Int.ofNat 121733757862, Int.ofNat 0, Int.ofNat 0]
noncomputable def factor_2 : List ℤ := [Int.negSucc 1787503726, Int.ofNat 148144, Int.ofNat 120325614740, Int.ofNat 0]
noncomputable def factor_3 : List ℤ := [Int.negSucc 126742457637, Int.negSucc 66, Int.negSucc 678097008, Int.ofNat 10753073893]
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
end Certificate.Generated.H2B022
