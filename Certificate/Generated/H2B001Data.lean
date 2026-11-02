import Certificate.FastGram

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Certificate.Generated.H2B001
noncomputable def a_0 : List ℤ := [Int.ofNat 4760259488659363856384, Int.negSucc 15481123719086079, Int.negSucc 312966397105044193279, Int.negSucc 4730477747273516187647]
noncomputable def a_1 : List ℤ := [Int.negSucc 15481123719086079, Int.ofNat 299756494973036396544, Int.ofNat 10696049115004928, Int.ofNat 15199648742375424]
noncomputable def a_2 : List ℤ := [Int.negSucc 312966397105044193279, Int.ofNat 10696049115004928, Int.ofNat 229703565719241752576, Int.ofNat 311799683326578524160]
noncomputable def a_3 : List ℤ := [Int.negSucc 4730477747273516187647, Int.ofNat 15199648742375424, Int.ofNat 311799683326578524160, Int.ofNat 4732313808546599796736]
noncomputable def a : List (List ℤ) := [a_0, a_1, a_2, a_3]
noncomputable def b_0 : List ℤ := [Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0]
noncomputable def b_1 : List ℤ := [Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0]
noncomputable def b_2 : List ℤ := [Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0]
noncomputable def b_3 : List ℤ := [Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0]
noncomputable def b : List (List ℤ) := [b_0, b_1, b_2, b_3]
noncomputable def factor_0 : List ℤ := [Int.ofNat 68977921436, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0]
noncomputable def factor_1 : List ℤ := [Int.negSucc 224435, Int.ofNat 17246757722, Int.ofNat 0, Int.ofNat 0]
noncomputable def factor_2 : List ℤ := [Int.negSucc 4537196693, Int.ofNat 561134, Int.ofNat 14380944634, Int.ofNat 0]
noncomputable def factor_3 : List ℤ := [Int.negSucc 68579592552, Int.negSucc 11136, Int.ofNat 44543855, Int.ofNat 5181261100]
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
end Certificate.Generated.H2B001
