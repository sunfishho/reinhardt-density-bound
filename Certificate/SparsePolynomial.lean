import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FunProp

namespace Certificate.Sparse

/-- Exponents in the seven state coordinates and an eighth indeterminate for sqrt(3). -/
structure Exponent where
  g11 : ℕ
  g12 : ℕ
  g21 : ℕ
  g22 : ℕ
  a : ℕ
  p : ℕ
  h : ℕ
  t : ℕ
  deriving DecidableEq, Repr

namespace Exponent

def add (e f : Exponent) : Exponent :=
  ⟨e.g11+f.g11,e.g12+f.g12,e.g21+f.g21,e.g22+f.g22,
   e.a+f.a,e.p+f.p,e.h+f.h,e.t+f.t⟩

/-- A sorting key only. Soundness never assumes this encoding is injective. -/
def key (e : Exponent) : ℕ :=
  e.g11+16*(e.g12+16*(e.g21+16*(e.g22+16*(e.a+16*(e.p+16*(e.h+16*e.t))))))

def eval {R : Type*} [CommRing R] (x : Fin 8 → R) (e : Exponent) : R :=
  x 0^e.g11 * x 1^e.g12 * x 2^e.g21 * x 3^e.g22 *
  x 4^e.a * x 5^e.p * x 6^e.h * x 7^e.t

theorem eval_add {R : Type*} [CommRing R] (x : Fin 8 → R) (e f : Exponent) :
    (e.add f).eval x = e.eval x * f.eval x := by
  simp only [add, eval, pow_add]
  ring
end Exponent

abbrev Term := ℤ × Exponent
abbrev Polynomial := List Term

def eval {R : Type*} [CommRing R] (x : Fin 8 → R) : Polynomial → R
  | [] => 0
  | (c,e)::p => (c : R)*e.eval x + eval x p

theorem eval_append {R : Type*} [CommRing R] (x : Fin 8 → R) (p q : Polynomial) :
    eval x (p++q) = eval x p + eval x q := by
  induction p with
  | nil => simp [eval]
  | cons term p ih =>
    rcases term with ⟨c,e⟩
    simp only [List.cons_append,eval,ih,add_assoc]

/-- Structural recursion avoids repeatedly computing list lengths in the kernel.
The fallback preserves evaluation for every fuel value. -/
def mergeAux : ℕ → Polynomial → Polynomial → Polynomial
  | 0,p,q => p++q
  | _+1,[],q => q
  | _+1,p,[] => p
  | fuel+1,(c,e)::p,(d,f)::q =>
    if e=f then (c+d,e)::mergeAux fuel p q
    else if e.key < f.key then (c,e)::mergeAux fuel p ((d,f)::q)
    else (d,f)::mergeAux fuel ((c,e)::p) q

theorem eval_mergeAux {R : Type*} [CommRing R] (x : Fin 8 → R) (fuel : ℕ)
    (p q : Polynomial) : eval x (mergeAux fuel p q) = eval x p + eval x q := by
  induction fuel generalizing p q with
  | zero => exact eval_append x p q
  | succ fuel ih =>
    cases p with
    | nil => simp [mergeAux,eval]
    | cons term p =>
      rcases term with ⟨c,e⟩
      cases q with
      | nil => simp [mergeAux,eval]
      | cons term q =>
        rcases term with ⟨d,f⟩
        by_cases he : e=f
        · subst f
          simp only [mergeAux,ite_true,eval,Int.cast_add,ih]
          ring
        · by_cases hk : e.key < f.key
          · simp only [mergeAux,if_neg he,if_pos hk,eval,ih]
            ring
          · simp only [mergeAux,if_neg he,if_neg hk,eval,ih]
            ring

/-- Equality of exponents is checked independently of the sorting key. -/
def merge (p q : Polynomial) : Polynomial := mergeAux (p.length+q.length) p q

theorem eval_merge {R : Type*} [CommRing R] (x : Fin 8 → R) (p q : Polynomial) :
    eval x (merge p q) = eval x p + eval x q := eval_mergeAux x _ p q

def scale (c : ℤ) (p : Polynomial) : Polynomial := p.map (fun (d,e) => (c*d,e))

theorem eval_scale {R : Type*} [CommRing R] (x : Fin 8 → R) (c : ℤ) (p : Polynomial) :
    eval x (scale c p) = (c : R)*eval x p := by
  induction p with
  | nil => simp [scale,eval]
  | cons term p ih =>
    rcases term with ⟨d,e⟩
    simp only [scale, List.map_cons, eval, Int.cast_mul] at *
    rw [ih]
    ring

def termMul (t : Term) (p : Polynomial) : Polynomial :=
  p.map (fun (d,f) => (t.1*d,t.2.add f))

theorem eval_termMul {R : Type*} [CommRing R] (x : Fin 8 → R) (t : Term) (p : Polynomial) :
    eval x (termMul t p) = (t.1 : R)*t.2.eval x * eval x p := by
  induction p with
  | nil => simp [termMul,eval]
  | cons term p ih =>
    rcases term with ⟨d,e⟩
    simp only [termMul, List.map_cons, eval, Int.cast_mul, Exponent.eval_add] at *
    rw [ih]
    ring

def mul (p q : Polynomial) : Polynomial :=
  p.foldr (fun t acc => merge (termMul t q) acc) []

theorem eval_mul {R : Type*} [CommRing R] (x : Fin 8 → R) (p q : Polynomial) :
    eval x (mul p q) = eval x p * eval x q := by
  induction p with
  | nil => simp [mul,eval]
  | cons term p ih =>
    rcases term with ⟨c,e⟩
    simp only [mul,List.foldr_cons,eval_merge,eval_termMul] at *
    rw [ih]
    simp only [eval]
    ring

def isZero (p : Polynomial) : Bool := p.all (fun t => decide (t.1=0))

theorem eval_eq_zero_of_check {R : Type*} [CommRing R] (x : Fin 8 → R)
    (p : Polynomial) (hcheck : isZero p = true) : eval x p = 0 := by
  induction p with
  | nil => rfl
  | cons term p ih =>
    rcases term with ⟨c,e⟩
    simp only [isZero,List.all_cons,Bool.and_eq_true,decide_eq_true_eq] at hcheck
    rcases hcheck with ⟨hc,hp⟩
    simp [eval,hc,ih hp]

#print axioms eval_merge
#print axioms eval_mul
#print axioms eval_eq_zero_of_check


def evalMany {R : Type*} [CommRing R] (x : Fin 8 → R) : List Polynomial → R
  | [] => 0
  | p::ps => eval x p + evalMany x ps

theorem eval_flatten {R : Type*} [CommRing R] (x : Fin 8 → R) (ps : List Polynomial) :
    eval x ps.flatten = evalMany x ps := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [List.flatten_cons,eval_append,evalMany,ih]

def mergePairs : List Polynomial → List Polynomial
  | p::q::ps => merge p q :: mergePairs ps
  | ps => ps

theorem evalMany_mergePairs {R : Type*} [CommRing R] (x : Fin 8 → R) (ps : List Polynomial) :
    evalMany x (mergePairs ps) = evalMany x ps := by
  fun_induction mergePairs ps <;> simp_all [evalMany,eval_merge,add_assoc]

/-- Fuel affects normalization efficiency, never the value of the polynomial. -/
def collapse : ℕ → List Polynomial → Polynomial
  | _, [] => []
  | _, [p] => p
  | 0, ps => ps.flatten
  | n+1, ps => collapse n (mergePairs ps)

theorem eval_collapse {R : Type*} [CommRing R] (x : Fin 8 → R) (fuel : ℕ)
    (ps : List Polynomial) : eval x (collapse fuel ps) = evalMany x ps := by
  induction fuel generalizing ps with
  | zero =>
    cases ps with
    | nil => rfl
    | cons p ps =>
      cases ps with
      | nil => simp [collapse,evalMany]
      | cons q ps => exact eval_flatten x _
  | succ fuel ih =>
    cases ps with
    | nil => rfl
    | cons p ps =>
      cases ps with
      | nil => simp [collapse,evalMany]
      | cons q ps =>
        rw [collapse,ih,evalMany_mergePairs] <;> simp

def normalize (p : Polynomial) : Polynomial := collapse 20 (p.map (fun t => [t]))

theorem eval_normalize {R : Type*} [CommRing R] (x : Fin 8 → R) (p : Polynomial) :
    eval x (normalize p) = eval x p := by
  unfold normalize
  rw [eval_collapse]
  induction p with
  | nil => rfl
  | cons term p ih =>
    rcases term with ⟨c,e⟩
    simp [evalMany,eval,ih]

def mulFast (p q : Polynomial) : Polynomial := normalize (p.flatMap (fun t => termMul t q))

theorem eval_mulFast {R : Type*} [CommRing R] (x : Fin 8 → R) (p q : Polynomial) :
    eval x (mulFast p q) = eval x p * eval x q := by
  unfold mulFast
  rw [eval_normalize]
  induction p with
  | nil => simp [eval]
  | cons term p ih =>
    rcases term with ⟨c,e⟩
    simp only [List.flatMap_cons,eval_append,eval_termMul,ih,eval]
    ring

def checkEqual (p q : Polynomial) : Bool := isZero (normalize (p++scale (-1) q))

theorem eq_of_check {R : Type*} [CommRing R] (x : Fin 8 → R) (p q : Polynomial)
    (hcheck : checkEqual p q = true) : eval x p = eval x q := by
  have hz := eval_eq_zero_of_check x _ hcheck
  rw [eval_normalize,eval_append,eval_scale] at hz
  apply sub_eq_zero.mp
  simpa only [Int.cast_neg,Int.cast_one,neg_one_mul,sub_eq_add_neg] using hz

#print axioms eval_normalize
#print axioms eq_of_check
end Certificate.Sparse

