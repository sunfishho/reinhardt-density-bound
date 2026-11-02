import Certificate.FastGram

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Certificate.Generated.H2B012
noncomputable def a_0 : List ℤ := [Int.ofNat 328221777892808327168, Int.ofNat 21073187081396682752, Int.ofNat 12252605736214855680, Int.negSucc 312061736529896144895]
noncomputable def a_1 : List ℤ := [Int.ofNat 21073187081396682752, Int.ofNat 33131293608704475136, Int.negSucc 2218585766433390591, Int.negSucc 21084164605488398335]
noncomputable def a_2 : List ℤ := [Int.ofNat 12252605736214855680, Int.negSucc 2218585766433390591, Int.ofNat 36405410537802825728, Int.negSucc 12427683171728883711]
noncomputable def a_3 : List ℤ := [Int.negSucc 312061736529896144895, Int.negSucc 21084164605488398335, Int.negSucc 12427683171728883711, Int.ofNat 326901660252035350528]
noncomputable def a : List (List ℤ) := [a_0, a_1, a_2, a_3]
noncomputable def b_0 : List ℤ := [Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0]
noncomputable def b_1 : List ℤ := [Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0]
noncomputable def b_2 : List ℤ := [Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0]
noncomputable def b_3 : List ℤ := [Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0]
noncomputable def b : List (List ℤ) := [b_0, b_1, b_2, b_3]
noncomputable def factor_0 : List ℤ := [Int.ofNat 18053141967, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0]
noncomputable def factor_1 : List ℤ := [Int.ofNat 1167286399, Int.ofNat 5427973200, Int.ofNat 0, Int.ofNat 0]
noncomputable def factor_2 : List ℤ := [Int.ofNat 678696581, Int.negSucc 554685688, Int.ofNat 5773323329, Int.ofNat 0]
noncomputable def factor_3 : List ℤ := [Int.negSucc 17285729934, Int.negSucc 167054463, Int.negSucc 136590318, Int.ofNat 5074721050]
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
end Certificate.Generated.H2B012
