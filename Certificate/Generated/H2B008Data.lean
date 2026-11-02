import Certificate.FastGram

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Certificate.Generated.H2B008
noncomputable def a_0 : List ℤ := [Int.ofNat 1337218934458009255936, Int.negSucc 159690324437163311103, Int.ofNat 72135844081453498368, Int.negSucc 1318668889067846893567]
noncomputable def a_1 : List ℤ := [Int.negSucc 159690324437163311103, Int.ofNat 148751925367210508288, Int.ofNat 11899917590396403712, Int.ofNat 159577452971502338048]
noncomputable def a_2 : List ℤ := [Int.ofNat 72135844081453498368, Int.ofNat 11899917590396403712, Int.ofNat 154935649130566909952, Int.negSucc 73105806851198418943]
noncomputable def a_3 : List ℤ := [Int.negSucc 1318668889067846893567, Int.ofNat 159577452971502338048, Int.negSucc 73105806851198418943, Int.ofNat 1331435749586512117760]
noncomputable def a : List (List ℤ) := [a_0, a_1, a_2, a_3]
noncomputable def b_0 : List ℤ := [Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0]
noncomputable def b_1 : List ℤ := [Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0]
noncomputable def b_2 : List ℤ := [Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0]
noncomputable def b_3 : List ℤ := [Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0]
noncomputable def b : List (List ℤ) := [b_0, b_1, b_2, b_3]
noncomputable def factor_0 : List ℤ := [Int.ofNat 36536462492, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0]
noncomputable def factor_1 : List ℤ := [Int.negSucc 4370711161, Int.ofNat 11284634079, Int.ofNat 0, Int.ofNat 0]
noncomputable def factor_2 : List ℤ := [Int.ofNat 1974352172, Int.ofNat 1819220767, Int.ofNat 12059111718, Int.ofNat 0]
noncomputable def factor_3 : List ℤ := [Int.negSucc 36091859996, Int.ofNat 162199112, Int.negSucc 177694734, Int.ofNat 5142923735]
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
end Certificate.Generated.H2B008
