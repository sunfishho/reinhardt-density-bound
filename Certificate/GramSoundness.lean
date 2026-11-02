import Certificate.IntervalSoundness

namespace Certificate
open Matrix
open scoped ComplexOrder

-- The checker uses an integer Gram factor; arbitrary dimensions are allowed.
def gramDot {n k : Type*} [Fintype k] (L : Matrix n k ℤ) (i j : n) : ℤ :=
  ∑ t, L i t * L j t

def lowerEntry {n k : Type*} [Fintype k] (A B : Matrix n n ℤ)
    (L : Matrix n k ℤ) (c s l u : ℤ) (i j : n) : ℤ :=
  (A i j - c * gramDot L i j) * s + min (B i j * l) (B i j * u)

def upperEntry {n k : Type*} [Fintype k] (A B : Matrix n n ℤ)
    (L : Matrix n k ℤ) (c s l u : ℤ) (i j : n) : ℤ :=
  (A i j - c * gramDot L i j) * s + max (B i j * l) (B i j * u)

def radiusEntry {n k : Type*} [Fintype k] (A B : Matrix n n ℤ)
    (L : Matrix n k ℤ) (c s l u : ℤ) (i j : n) : ℤ :=
  max |lowerEntry A B L c s l u i j| |upperEntry A B L c s l u i j|

/-- Real matrix denoted by the exact coefficient data. -/
noncomputable def realGram {n : Type*} (A B : Matrix n n ℤ) (den : ℤ) : Matrix n n ℝ :=
  fun i j => ((A i j : ℝ) + (B i j : ℝ) * Real.sqrt 3) / (den : ℝ)

/-- Soundness of a finite integer certificate for Gram-matrix positivity. -/
theorem gram_certificate_sound {n k : Type*} [Fintype n] [DecidableEq n] [Fintype k]
    (A B : Matrix n n ℤ) (L : Matrix n k ℤ) (den c s l u : ℤ)
    (hden : 0 < den) (hc : 0 ≤ c) (hs : 0 < s) (hl : 0 ≤ l)
    (hls : l*l ≤ 3*s*s) (hus : 3*s*s ≤ u*u) (hlu : l ≤ u)
    (hA : ∀ i j, A j i = A i j) (hB : ∀ i j, B j i = B i j)
    (hrows : ∀ i, ∑ j ∈ Finset.univ.erase i, radiusEntry A B L c s l u i j ≤
      lowerEntry A B L c s l u i i) : (realGram A B den).PosSemidef := by
  let T : Matrix n n ℝ := fun i j => (A i j : ℝ) + (B i j : ℝ) * Real.sqrt 3
  let F : Matrix n k ℝ := fun i j => (L i j : ℝ)
  let E : Matrix n n ℝ := T - (c : ℝ) • (F * Fᴴ)
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  have hc' : (0 : ℝ) ≤ c := by exact_mod_cast hc
  have hd' : (0 : ℝ) < den := by exact_mod_cast hden
  have hsqrt := sqrt_three_enclosure s l u hs hl hls hus hlu
  have hT : T.IsHermitian := by
    ext i j
    change star (T j i) = T i j
    simp only [T, star_trivial, hA, hB]
  have hE : E.IsHermitian := hT.sub
    ((Matrix.posSemidef_self_mul_conjTranspose F).smul hc').isHermitian
  have hSE : ((s : ℝ) • E).IsHermitian :=
    IsSelfAdjoint.smul (IsSelfAdjoint.of_nonneg hs'.le) hE
  have hbounds (i j : n) :
      (lowerEntry A B L c s l u i j : ℝ) ≤ ((s : ℝ) • E) i j ∧
      ((s : ℝ) • E) i j ≤ (upperEntry A B L c s l u i j : ℝ) := by
    have h := linear_enclosure
      (((A i j : ℝ) - (c : ℝ) * (gramDot L i j : ℝ)) * (s : ℝ))
      (B i j : ℝ) (l : ℝ) (u : ℝ) ((s : ℝ) * Real.sqrt 3) hsqrt.1 hsqrt.2
    have heq : ((s : ℝ) • E) i j =
        ((A i j : ℝ) - (c : ℝ) * (gramDot L i j : ℝ)) * (s : ℝ) +
        (B i j : ℝ) * ((s : ℝ) * Real.sqrt 3) := by
      change (s : ℝ) * (((A i j : ℝ) + (B i j : ℝ) * Real.sqrt 3) -
        (c : ℝ) * ∑ t, (L i t : ℝ) * star (L j t : ℝ)) = _
      simp only [gramDot, Int.cast_sum, Int.cast_mul, star_trivial]
      ring
    rw [heq]
    simpa [lowerEntry, upperEntry] using h
  have hradius (i j : n) : ‖((s : ℝ) • E) i j‖ ≤
      (radiusEntry A B L c s l u i j : ℝ) := by
    have h := abs_le_endpoint_radius _ _ _ (hbounds i j).1 (hbounds i j).2
    simpa [radiusEntry, Real.norm_eq_abs] using h
  have hscaled : ((s : ℝ) • E).PosSemidef := by
    apply posSemidef_of_row_dominance _ hSE
    intro i
    calc
      _ ≤ ∑ j ∈ Finset.univ.erase i, (radiusEntry A B L c s l u i j : ℝ) :=
        Finset.sum_le_sum (fun j _ => hradius i j)
      _ ≤ (lowerEntry A B L c s l u i i : ℝ) := by exact_mod_cast hrows i
      _ ≤ _ := (hbounds i i).1
  have hEpsd : E.PosSemidef := by
    have h := hscaled.smul (inv_nonneg.mpr hs'.le)
    simpa only [smul_smul, inv_mul_cancel₀ hs'.ne', one_smul] using h
  have hTpsd : T.PosSemidef := by
    have h := hEpsd.add ((Matrix.posSemidef_self_mul_conjTranspose F).smul hc')
    simpa only [E, sub_add_cancel] using h
  have h := hTpsd.smul (inv_nonneg.mpr hd'.le)
  have heq : (den : ℝ)⁻¹ • T = realGram A B den := by
    ext i j
    change (den : ℝ)⁻¹ * ((A i j : ℝ) + (B i j : ℝ) * Real.sqrt 3) = _
    simp only [realGram, div_eq_mul_inv, mul_comm]
  rw [heq] at h
  exact h

#print axioms gram_certificate_sound
end Certificate
