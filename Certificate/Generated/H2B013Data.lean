import Certificate.FastGram

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Certificate.Generated.H2B013
noncomputable def a_0 : List ℤ := [Int.ofNat 28183984146396695494656, Int.negSucc 1102753093607799914495, Int.negSucc 622359750855723319295, Int.negSucc 28094801051825737826303]
noncomputable def a_1 : List ℤ := [Int.negSucc 1102753093607799914495, Int.ofNat 499528011668866990080, Int.ofNat 69615517139986284544, Int.ofNat 1101960460073382707200]
noncomputable def a_2 : List ℤ := [Int.negSucc 622359750855723319295, Int.ofNat 69615517139986284544, Int.ofNat 420747106337228324864, Int.ofNat 619144462196757495808]
noncomputable def a_3 : List ℤ := [Int.negSucc 28094801051825737826303, Int.ofNat 1101960460073382707200, Int.ofNat 619144462196757495808, Int.ofNat 28037803776416713539584]
noncomputable def a : List (List ℤ) := [a_0, a_1, a_2, a_3]
noncomputable def b_0 : List ℤ := [Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0]
noncomputable def b_1 : List ℤ := [Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0]
noncomputable def b_2 : List ℤ := [Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0]
noncomputable def b_3 : List ℤ := [Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0]
noncomputable def b : List (List ℤ) := [b_0, b_1, b_2, b_3]
noncomputable def factor_0 : List ℤ := [Int.ofNat 167873995316, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0]
noncomputable def factor_1 : List ℤ := [Int.negSucc 6568933392, Int.ofNat 21308948419, Int.ofNat 0, Int.ofNat 0]
noncomputable def factor_2 : List ℤ := [Int.negSucc 3707302906, Int.ofNat 2124107224, Int.ofNat 20004632888, Int.ofNat 0]
noncomputable def factor_3 : List ℤ := [Int.negSucc 167356480667, Int.ofNat 122337605, Int.negSucc 77810139, Int.ofNat 5223532409]
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
end Certificate.Generated.H2B013
