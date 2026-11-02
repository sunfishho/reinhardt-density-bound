import Certificate.FastGram

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Certificate.Generated.H2B018
noncomputable def a_0 : List ℤ := [Int.ofNat 60908478859759862153216, Int.negSucc 32256576904528859758591, Int.ofNat 20399374549223181647872, Int.negSucc 60670447575379658932223]
noncomputable def a_1 : List ℤ := [Int.negSucc 32256576904528859758591, Int.ofNat 21063110277230441267200, Int.negSucc 6399927789192600354815, Int.ofNat 32347716813137909907456]
noncomputable def a_2 : List ℤ := [Int.ofNat 20399374549223181647872, Int.negSucc 6399927789192600354815, Int.ofNat 16106785734368572735488, Int.negSucc 20527795537022581473279]
noncomputable def a_3 : List ℤ := [Int.negSucc 60670447575379658932223, Int.ofNat 32347716813137909907456, Int.negSucc 20527795537022581473279, Int.ofNat 60708220391354322124800]
noncomputable def a : List (List ℤ) := [a_0, a_1, a_2, a_3]
noncomputable def b_0 : List ℤ := [Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0]
noncomputable def b_1 : List ℤ := [Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0]
noncomputable def b_2 : List ℤ := [Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0]
noncomputable def b_3 : List ℤ := [Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0]
noncomputable def b : List (List ℤ) := [b_0, b_1, b_2, b_3]
noncomputable def factor_0 : List ℤ := [Int.ofNat 246759056806, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0]
noncomputable def factor_1 : List ℤ := [Int.negSucc 130720944235, Int.ofNat 62902291462, Int.ofNat 0, Int.ofNat 0]
noncomputable def factor_2 : List ℤ := [Int.ofNat 82669202960, Int.ofNat 70055770284, Int.ofNat 65926708717, Int.ofNat 0]
noncomputable def factor_3 : List ℤ := [Int.negSucc 245869182515, Int.ofNat 3298212373, Int.negSucc 6568582032, Int.ofNat 13568134035]
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
end Certificate.Generated.H2B018
