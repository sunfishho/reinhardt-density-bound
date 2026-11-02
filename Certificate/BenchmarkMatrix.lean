import Certificate.BenchmarkData
import Certificate.GramSoundness

namespace Certificate.Benchmark
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def A : Matrix (Fin 104) (Fin 104) ℤ := fun i j => (gramA[i.val]!)[j.val]!
def B : Matrix (Fin 104) (Fin 104) ℤ := fun i j => (gramB[i.val]!)[j.val]!
def L : Matrix (Fin 104) (Fin 104) ℤ := fun i j => (factor[i.val]!)[j.val]!
def c : ℤ := denominator / (factorDenominator * factorDenominator)

def rowCondition (i : Fin 104) : Prop :=
  ∑ j ∈ Finset.univ.erase i, radiusEntry A B L c sqrtScale sqrtLo sqrtHi i j ≤
    lowerEntry A B L c sqrtScale sqrtLo sqrtHi i i

end Certificate.Benchmark
