import Certificate.BenchmarkMatrixLite
import Certificate.ListDotSoundness
namespace Certificate.BenchmarkLite
set_option maxHeartbeats 0
set_option maxRecDepth 100000

noncomputable def factorRows (i : Fin 104) : List ℤ := factor[i.val]!

theorem factorRows_length : ∀ i : Fin 104, (factorRows i).length = 104 := by
  decide +kernel

theorem gramDot_fast (i j : Fin 104) : gramDot L i j = dot (factorRows i) (factorRows j) := by
  exact gramDot_eq_listDot factorRows factorRows_length i j

noncomputable def fastLower (i j : Fin 104) : ℤ :=
  (A i j - c * dot (factorRows i) (factorRows j)) * sqrtScale +
    min (B i j * sqrtLo) (B i j * sqrtHi)
noncomputable def fastUpper (i j : Fin 104) : ℤ :=
  (A i j - c * dot (factorRows i) (factorRows j)) * sqrtScale +
    max (B i j * sqrtLo) (B i j * sqrtHi)
noncomputable def fastRadius (i j : Fin 104) : ℤ := max |fastLower i j| |fastUpper i j|
noncomputable def fastRowCondition (i : Fin 104) : Prop :=
  ∑ j ∈ Finset.univ.erase i, fastRadius i j ≤ fastLower i i

theorem rowCondition_iff_fast (i : Fin 104) : rowCondition i ↔ fastRowCondition i := by
  simp only [rowCondition, radiusEntry, lowerEntry, upperEntry, gramDot_fast,
    fastRowCondition, fastRadius, fastLower, fastUpper]

#print axioms rowCondition_iff_fast
end Certificate.BenchmarkLite
