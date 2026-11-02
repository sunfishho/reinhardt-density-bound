import Certificate.FastGram

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Certificate.Generated.H2B007
noncomputable def a_0 : List ℤ := [Int.ofNat 2607083721738925637632, Int.negSucc 3377699720527871, Int.ofNat 152875815250998329344, Int.negSucc 2585530619822237286399]
noncomputable def a_1 : List ℤ := [Int.negSucc 3377699720527871, Int.ofNat 168662620794792181760, Int.negSucc 4503599627370495, Int.ofNat 3377699720527872]
noncomputable def a_2 : List ℤ := [Int.ofNat 152875815250998329344, Int.negSucc 4503599627370495, Int.ofNat 222135829495399055360, Int.negSucc 154698647200176537599]
noncomputable def a_3 : List ℤ := [Int.negSucc 2585530619822237286399, Int.ofNat 3377699720527872, Int.negSucc 154698647200176537599, Int.ofNat 2595427280003383951360]
noncomputable def a : List (List ℤ) := [a_0, a_1, a_2, a_3]
noncomputable def b_0 : List ℤ := [Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0]
noncomputable def b_1 : List ℤ := [Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0]
noncomputable def b_2 : List ℤ := [Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0]
noncomputable def b_3 : List ℤ := [Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0]
noncomputable def b : List (List ℤ) := [b_0, b_1, b_2, b_3]
noncomputable def factor_0 : List ℤ := [Int.ofNat 51037024587, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0]
noncomputable def factor_1 : List ℤ := [Int.negSucc 66180, Int.ofNat 12897936958, Int.ofNat 0, Int.ofNat 0]
noncomputable def factor_2 : List ℤ := [Int.ofNat 2995390434, Int.negSucc 333801, Int.ofNat 14520937384, Int.ofNat 0]
noncomputable def factor_3 : List ℤ := [Int.negSucc 50659901134, Int.ofNat 1935, Int.negSucc 203324609, Int.ofNat 5162800895]
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
end Certificate.Generated.H2B007
