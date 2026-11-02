import Certificate.BenchmarkDataLite
import Certificate.GramSoundness

namespace Certificate.BenchmarkLite
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable def A : Matrix (Fin 104) (Fin 104) ℤ := fun i j => (gramA[i.val]!)[j.val]!
noncomputable def B : Matrix (Fin 104) (Fin 104) ℤ := fun i j => (gramB[i.val]!)[j.val]!
noncomputable def L : Matrix (Fin 104) (Fin 104) ℤ := fun i j => (factor[i.val]!)[j.val]!
noncomputable def c : ℤ := denominator / (factorDenominator * factorDenominator)

noncomputable def rowCondition (i : Fin 104) : Prop :=
  ∑ j ∈ Finset.univ.erase i, radiusEntry A B L c sqrtScale sqrtLo sqrtHi i j ≤
    lowerEntry A B L c sqrtScale sqrtLo sqrtHi i i

end Certificate.BenchmarkLite
