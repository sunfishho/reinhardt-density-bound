import Certificate.MultiplierSoundness

namespace Certificate.Sparse
set_option maxHeartbeats 0

def power (p : Polynomial) : ℕ → Polynomial
  | 0 => one
  | n+1 => mulFast (power p n) p

theorem eval_one {R : Type*} [CommRing R] (x : Fin 8 → R) : eval x one = 1 := by
  simp [one,eval,Exponent.eval]

theorem eval_power {R : Type*} [CommRing R] (x : Fin 8 → R) (p : Polynomial) (n : ℕ) :
    eval x (power p n) = eval x p ^ n := by
  induction n with
  | zero => simp [power,eval_one]
  | succ n ih => simp only [power,eval_mulFast,ih,pow_succ]

def Exponent.totalDegree (e : Exponent) : ℕ :=
  e.g11+e.g12+e.g21+e.g22+e.a+e.p+e.h+e.t

def monomialSubstitute (e : Exponent) (σ : Fin 8 → Polynomial) : Polynomial :=
  mulFast (mulFast (mulFast (mulFast (mulFast (mulFast (mulFast
    (power (σ 0) e.g11) (power (σ 1) e.g12)) (power (σ 2) e.g21))
    (power (σ 3) e.g22)) (power (σ 4) e.a)) (power (σ 5) e.p))
    (power (σ 6) e.h)) (power (σ 7) e.t)

theorem eval_monomialSubstitute {R : Type*} [CommRing R] (x : Fin 8 → R)
    (e : Exponent) (σ : Fin 8 → Polynomial) :
    eval x (monomialSubstitute e σ) = e.eval (fun i => eval x (σ i)) := by
  simp only [monomialSubstitute,eval_mulFast,eval_power,Exponent.eval]

theorem Exponent.eval_scaled {R : Type*} [CommRing R] (e : Exponent)
    (d : R) (x : Fin 8 → R) :
    e.eval (fun i => d*x i) = d^e.totalDegree * e.eval x := by
  simp only [eval,totalDegree,mul_pow,pow_add]
  ring

/-- Substitute rational coordinates while retaining integral polynomial data.
The common denominator is raised to a checked total-degree bound. -/
def scaledSubstitute (p : Polynomial) (σ : Fin 8 → Polynomial) (den : ℤ) (degree : ℕ) : Polynomial :=
  normalize ((p.map fun (c,e) => scale (c*den^(degree-e.totalDegree))
    (monomialSubstitute e σ)).flatten)

theorem eval_scaledSubstitute {R : Type*} [CommRing R] (x y : Fin 8 → R)
    (p : Polynomial) (σ : Fin 8 → Polynomial) (den : ℤ) (degree : ℕ)
    (hdegree : ∀ term ∈ p, term.2.totalDegree ≤ degree)
    (hσ : ∀ i, eval x (σ i) = (den : R)*y i) :
    eval x (scaledSubstitute p σ den degree) = (den : R)^degree*eval y p := by
  simp only [scaledSubstitute,eval_normalize,eval_flatten]
  induction p with
  | nil => simp [eval,evalMany]
  | cons term p ih =>
    rcases term with ⟨c,e⟩
    have he : e.totalDegree ≤ degree := hdegree (c,e) (by simp)
    have hp : ∀ term ∈ p, term.2.totalDegree ≤ degree := fun term h => hdegree term (by simp [h])
    simp only [List.map_cons,evalMany,eval_scale,eval_monomialSubstitute,hσ,
      Exponent.eval_scaled,Int.cast_mul,Int.cast_pow,ih hp,eval]
    have hpow : (den : R)^(degree-e.totalDegree)*(den : R)^e.totalDegree = (den : R)^degree := by
      rw [← pow_add,Nat.sub_add_cancel he]
    calc
      _ = (c : R)*((den : R)^(degree-e.totalDegree)*(den : R)^e.totalDegree)*e.eval y +
          (den : R)^degree*eval y p := by ring
      _ = _ := by rw [hpow]; ring

#print axioms eval_scaledSubstitute
end Certificate.Sparse
