import Certificate.FastGram

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Certificate.Generated.H2B004
noncomputable def a_0 : List ℤ := [Int.ofNat 4547804990987927814144, Int.ofNat 0, Int.ofNat 302659627882830102528, Int.negSucc 4279880219656122793983]
noncomputable def a_1 : List ℤ := [Int.ofNat 0, Int.ofNat 2907678167717629657088, Int.ofNat 562949953421312, Int.ofNat 0]
noncomputable def a_2 : List ℤ := [Int.ofNat 302659627882830102528, Int.ofNat 562949953421312, Int.ofNat 3289592704792879169536, Int.negSucc 320714277313981710335]
noncomputable def a_3 : List ℤ := [Int.negSucc 4279880219656122793983, Int.ofNat 0, Int.negSucc 320714277313981710335, Int.ofNat 4187671832035478994944]
noncomputable def a : List (List ℤ) := [a_0, a_1, a_2, a_3]
noncomputable def b_0 : List ℤ := [Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0]
noncomputable def b_1 : List ℤ := [Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0]
noncomputable def b_2 : List ℤ := [Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0]
noncomputable def b_3 : List ℤ := [Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0]
noncomputable def b : List (List ℤ) := [b_0, b_1, b_2, b_3]
noncomputable def factor_0 : List ℤ := [Int.ofNat 67300507033, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0]
noncomputable def factor_1 : List ℤ := [Int.ofNat 0, Int.ofNat 53751571360, Int.ofNat 0, Int.ofNat 0]
noncomputable def factor_2 : List ℤ := [Int.ofNat 4497137410, Int.ofNat 10473, Int.ofNat 57016854665, Int.ofNat 0]
noncomputable def factor_3 : List ℤ := [Int.negSucc 63593580617, Int.ofNat 0, Int.negSucc 609034066, Int.ofNat 11167393144]
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
end Certificate.Generated.H2B004
