import Certificate.FastGram

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Certificate.Generated.H2B009
noncomputable def a_0 : List ℤ := [Int.ofNat 1337222593632706494464, Int.ofNat 159696235411674234880, Int.ofNat 72129370156989153280, Int.negSucc 1318672266767567421439]
noncomputable def a_1 : List ℤ := [Int.ofNat 159696235411674234880, Int.ofNat 148758117816698142720, Int.negSucc 11901887915233378303, Int.negSucc 159583363946013261823]
noncomputable def a_2 : List ℤ := [Int.ofNat 72129370156989153280, Int.negSucc 11901887915233378303, Int.ofNat 154930019631032696832, Int.negSucc 73099332926734073855]
noncomputable def a_3 : List ℤ := [Int.negSucc 1318672266767567421439, Int.negSucc 159583363946013261823, Int.negSucc 73099332926734073855, Int.ofNat 1331439127286232645632]
noncomputable def a : List (List ℤ) := [a_0, a_1, a_2, a_3]
noncomputable def b_0 : List ℤ := [Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0]
noncomputable def b_1 : List ℤ := [Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0]
noncomputable def b_2 : List ℤ := [Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0]
noncomputable def b_3 : List ℤ := [Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0]
noncomputable def b : List (List ℤ) := [b_0, b_1, b_2, b_3]
noncomputable def factor_0 : List ℤ := [Int.ofNat 36536512568, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0]
noncomputable def factor_1 : List ℤ := [Int.ofNat 4370866954, Int.ofNat 11284848110, Int.ofNat 0, Int.ofNat 0]
noncomputable def factor_2 : List ℤ := [Int.ofNat 1974172276, Int.negSucc 1819318440, Int.ofNat 12058893020, Int.ofNat 0]
noncomputable def factor_3 : List ℤ := [Int.negSucc 36091902977, Int.negSucc 162204920, Int.negSucc 177694676, Int.ofNat 5142950305]
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
end Certificate.Generated.H2B009
