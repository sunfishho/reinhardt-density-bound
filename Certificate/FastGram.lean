import Certificate.ListDotSoundness

namespace Certificate

/-- Finite integer data for a real Gram matrix and an approximate factor witness. -/
structure GramData where
  size : ℕ
  den : ℤ
  c : ℤ
  scale : ℤ
  lo : ℤ
  hi : ℤ
  a : List (List ℤ)
  b : List (List ℤ)
  factor : List (List ℤ)

namespace GramData
noncomputable def A (d : GramData) : Matrix (Fin d.size) (Fin d.size) ℤ :=
  fun i j => (d.a[min i.val j.val]!)[max i.val j.val]!
noncomputable def B (d : GramData) : Matrix (Fin d.size) (Fin d.size) ℤ :=
  fun i j => (d.b[min i.val j.val]!)[max i.val j.val]!
/-- Matrices are stored by their upper triangles, as in the original Gram proposals. -/
theorem symmetric_A (d : GramData) (i j : Fin d.size) : d.A j i = d.A i j := by
  simp only [A, min_comm, max_comm]
theorem symmetric_B (d : GramData) (i j : Fin d.size) : d.B j i = d.B i j := by
  simp only [B, min_comm, max_comm]

noncomputable def factorRow (d : GramData) (i : Fin d.size) : List ℤ := d.factor[i.val]!
noncomputable def L (d : GramData) : Matrix (Fin d.size) (Fin d.size) ℤ :=
  fun i j => (d.factorRow i)[j.val]!
noncomputable def lower (d : GramData) (i j : Fin d.size) : ℤ :=
  (d.A i j-d.c*dot (d.factorRow i) (d.factorRow j))*d.scale +
    min (d.B i j*d.lo) (d.B i j*d.hi)
noncomputable def upper (d : GramData) (i j : Fin d.size) : ℤ :=
  (d.A i j-d.c*dot (d.factorRow i) (d.factorRow j))*d.scale +
    max (d.B i j*d.lo) (d.B i j*d.hi)
noncomputable def radius (d : GramData) (i j : Fin d.size) : ℤ :=
  max |d.lower i j| |d.upper i j|
noncomputable def RowCondition (d : GramData) (i : Fin d.size) : Prop :=
  ∑ j ∈ Finset.univ.erase i, d.radius i j ≤ d.lower i i

def ScalarConditions (d : GramData) : Prop :=
  0 < d.den ∧ 0 ≤ d.c ∧ 0 < d.scale ∧ 0 ≤ d.lo ∧
  d.lo*d.lo ≤ 3*d.scale*d.scale ∧ 3*d.scale*d.scale ≤ d.hi*d.hi ∧ d.lo ≤ d.hi

/-- The finite checks below imply positivity of precisely the supplied real matrix. -/
theorem sound (d : GramData) (hscalar : d.ScalarConditions)
    (hshape : ∀ i, (d.factorRow i).length = d.size)
    (hA : ∀ i j, d.A j i = d.A i j) (hB : ∀ i j, d.B j i = d.B i j)
    (hrow : ∀ i, d.RowCondition i) : (realGram d.A d.B d.den).PosSemidef := by
  obtain ⟨hd,hc,hs,hl,hls,hus,hlu⟩ := hscalar
  apply gram_certificate_sound d.A d.B d.L d.den d.c d.scale d.lo d.hi
    hd hc hs hl hls hus hlu hA hB
  intro i
  have hdot (i j : Fin d.size) : gramDot d.L i j = dot (d.factorRow i) (d.factorRow j) :=
    gramDot_eq_listDot d.factorRow hshape i j
  simpa only [radiusEntry, lowerEntry, upperEntry, hdot,
    RowCondition, radius, lower, upper] using hrow i

#print axioms sound
end GramData
end Certificate
