import Certificate.ConfinementMatrixNorm
import Certificate.ConfinementSector
import Certificate.ConfinementRegularity

namespace Certificate.Confinement
open MeasureTheory Set
set_option maxHeartbeats 0

theorem state_ext {x y : State} (h11 : x.g11=y.g11) (h12 : x.g12=y.g12)
    (h21 : x.g21=y.g21) (h22 : x.g22=y.g22) (ha : x.a=y.a) (hp : x.p=y.p)
    (hh : x.h=y.h) : x=y := by
  cases x
  cases y
  congr <;> assumption

structure GroupDerivative (x : ℝ → State) (t : ℝ) : Prop where
  g11 : HasDerivAt (fun s => (x s).g11) ((x t).g11*(x t).a+(x t).g12*((x t).p+(x t).h)) t
  g12 : HasDerivAt (fun s => (x s).g12) ((x t).g11*((x t).p-(x t).h)-(x t).g12*(x t).a) t
  g21 : HasDerivAt (fun s => (x s).g21) ((x t).g21*(x t).a+(x t).g22*((x t).p+(x t).h)) t
  g22 : HasDerivAt (fun s => (x s).g22) ((x t).g21*((x t).p-(x t).h)-(x t).g22*(x t).a) t

/-- Data used only for the new elementary confinement deductions. No angular
sector or norm constraint is included among these hypotheses. -/
structure RegularPath where
  state : ℝ → State
  duration : ℝ
  duration_nonneg : 0 ≤ duration
  c11 : ContinuousOn (fun t => (state t).g11) (Icc 0 duration)
  c12 : ContinuousOn (fun t => (state t).g12) (Icc 0 duration)
  c21 : ContinuousOn (fun t => (state t).g21) (Icc 0 duration)
  c22 : ContinuousOn (fun t => (state t).g22) (Icc 0 duration)
  ca : ContinuousOn (fun t => (state t).a) (Icc 0 duration)
  cp : ContinuousOn (fun t => (state t).p) (Icc 0 duration)
  ch : ContinuousOn (fun t => (state t).h) (Icc 0 duration)
  ode : ∀ t ∈ Ioo 0 duration, GroupDerivative state t
  determinant : ∀ t ∈ Icc 0 duration, (state t).determinantConstraints
  height : ∀ t ∈ Icc 0 duration, 0 ≤ (state t).h ∧ (state t).h ≤ 12/5
  initial : state 0=initialState (state 0)
  terminal : state duration=rotateState (state 0)
  cost_le : (∫ t in 0..duration, (state t).cost) ≤ 311/100

theorem RegularPath.base_sector (path : RegularPath) :
    ∀ t ∈ Icc 0 path.duration,
      0 ≤ (path.state t).g21 ∧ 0 ≤ Real.sqrt 3*(path.state t).g22-(path.state t).g21 := by
  apply row_sector (fun t => (path.state t).g21) (fun t => (path.state t).g22)
    (fun t => (path.state t).a) (fun t => (path.state t).p) (fun t => (path.state t).h)
    path.duration path.duration_nonneg path.c21 path.c22 path.ca path.cp path.ch
  · intro t ht; convert! (path.ode t ht).g21 using 1 <;> ring
  · intro t ht; convert! (path.ode t ht).g22 using 1 <;> ring
  · intro t ht
    have hd := (path.determinant t ht).1
    have hnn := add_nonneg (sq_nonneg (path.state t).g21) (sq_nonneg (path.state t).g22)
    by_contra hn
    have he1 : (path.state t).g21=0 := by nlinarith [sq_nonneg (path.state t).g22]
    have he2 : (path.state t).g22=0 := by nlinarith [sq_nonneg (path.state t).g21]
    rw [he1,he2] at hd
    norm_num at hd
  · exact fun t ht => (path.height t ht).1
  · exact fun t ht => (path.determinant t ht).2
  · exact congrArg State.g21 path.initial
  · exact congrArg State.g22 path.initial
  · exact congrArg State.g21 path.terminal
  · exact congrArg State.g22 path.terminal
  · have hc := path.cost_le
    simp only [State.cost,intervalIntegral.integral_const_mul] at hc
    linarith

theorem RegularPath.norm_bound (path : RegularPath) :
    ∀ t ∈ Icc 0 path.duration,
      (path.state t).g11^2+(path.state t).g12^2+(path.state t).g21^2+(path.state t).g22^2 ≤ 16/5 := by
  apply matrix_norm_bound path.state path.duration path.duration_nonneg
    path.c11 path.c12 path.c21 path.c22 path.ch
    (fun t ht => energy_hasDerivAt path.state t (path.ode t ht).g11 (path.ode t ht).g12
      (path.ode t ht).g21 (path.ode t ht).g22) path.determinant path.height
  · rw [path.initial]; norm_num [energy,initialState]
  · rw [path.terminal]; norm_num [energy,rotateState]; ring
  · exact path.cost_le

/-- Conjugation by R for e=sqrt(3), and by R inverse for e=-sqrt(3). -/
noncomputable def conjugate (e : ℝ) (x : State) : State where
  g11 := (x.g11+3*x.g22-e*(x.g12+x.g21))/4
  g12 := (x.g12-3*x.g21+e*(x.g11-x.g22))/4
  g21 := (x.g21-3*x.g12+e*(x.g11-x.g22))/4
  g22 := (3*x.g11+x.g22+e*(x.g12+x.g21))/4
  a := (-x.a-e*x.p)/2
  p := (e*x.a-x.p)/2
  h := x.h

theorem conjugate_determinant (e : ℝ) (he : e^2=3) (x : State) (hd : x.determinantConstraints) :
    (conjugate e x).determinantConstraints := by
  constructor
  · change _=1
    dsimp [conjugate]
    have hident :
        (x.g11+3*x.g22-e*(x.g12+x.g21))/4*(3*x.g11+x.g22+e*(x.g12+x.g21))/4-
        (x.g12-3*x.g21+e*(x.g11-x.g22))/4*(x.g21-3*x.g12+e*(x.g11-x.g22))/4 =
        x.g11*x.g22-x.g12*x.g21 := by
      ring_nf; simp only [he]; ring
    nlinarith only [hident,hd.1]
  · dsimp [conjugate]
    have hident : x.h^2-((-x.a-e*x.p)/2)^2-((e*x.a-x.p)/2)^2=x.h^2-x.a^2-x.p^2 := by
      ring_nf; simp only [he]; ring
    exact hident.trans hd.2

theorem conjugate_derivative (e : ℝ) (he : e^2=3) (x : ℝ → State) (t : ℝ)
    (hd : GroupDerivative x t) : GroupDerivative (fun s => conjugate e (x s)) t := by
  constructor
  · convert! ((hd.g11.add (hd.g22.const_mul 3)).sub ((hd.g12.add hd.g21).const_mul e)).div_const 4 using 1
    dsimp only [conjugate]; ring_nf; simp only [he]; ring
  · convert! ((hd.g12.sub (hd.g21.const_mul 3)).add ((hd.g11.sub hd.g22).const_mul e)).div_const 4 using 1
    dsimp only [conjugate]; ring_nf; simp only [he]; ring
  · convert! ((hd.g21.sub (hd.g12.const_mul 3)).add ((hd.g11.sub hd.g22).const_mul e)).div_const 4 using 1
    dsimp only [conjugate]; ring_nf; simp only [he]; ring
  · convert! (((hd.g11.const_mul 3).add hd.g22).add ((hd.g12.add hd.g21).const_mul e)).div_const 4 using 1
    dsimp only [conjugate]; ring_nf; simp only [he]; ring

noncomputable def RegularPath.conjugatePath (path : RegularPath) (e : ℝ) (he : e^2=3) : RegularPath where
  state t := conjugate e (path.state t)
  duration := path.duration
  duration_nonneg := path.duration_nonneg
  c11 := ((path.c11.add (path.c22.const_mul 3)).sub ((path.c12.add path.c21).const_mul e)).div_const 4
  c12 := ((path.c12.sub (path.c21.const_mul 3)).add ((path.c11.sub path.c22).const_mul e)).div_const 4
  c21 := ((path.c21.sub (path.c12.const_mul 3)).add ((path.c11.sub path.c22).const_mul e)).div_const 4
  c22 := (((path.c11.const_mul 3).add path.c22).add ((path.c12.add path.c21).const_mul e)).div_const 4
  ca := (path.ca.neg.sub (path.cp.const_mul e)).div_const 2
  cp := ((path.ca.const_mul e).sub path.cp).div_const 2
  ch := path.ch
  ode t ht := conjugate_derivative e he path.state t (path.ode t ht)
  determinant t ht := conjugate_determinant e he (path.state t) (path.determinant t ht)
  height := path.height
  initial := by
    have h0 := path.initial
    have hg11 : (path.state 0).g11=1 := congrArg State.g11 h0
    have hg12 : (path.state 0).g12=0 := congrArg State.g12 h0
    have hg21 : (path.state 0).g21=0 := congrArg State.g21 h0
    have hg22 : (path.state 0).g22=1 := congrArg State.g22 h0
    apply state_ext <;> norm_num [conjugate,initialState,hg11,hg12,hg21,hg22]
  terminal := by
    rw [path.terminal]
    apply state_ext <;> dsimp [conjugate,rotateState] <;> ring
  cost_le := path.cost_le

theorem RegularPath.group_bounds (path : RegularPath) :
    ∀ t ∈ Icc 0 path.duration, GroupBounds (path.state t) := by
  have hs : Real.sqrt (3:ℝ)^2=3 := Real.sq_sqrt (by norm_num)
  intro t ht
  have h0 := path.base_sector t ht
  have h1 := (path.conjugatePath (Real.sqrt 3) hs).base_sector t ht
  have h2 := (path.conjugatePath (-Real.sqrt 3) (by nlinarith only [hs])).base_sector t ht
  change 0 ≤ (conjugate (Real.sqrt 3) (path.state t)).g21 ∧
    0 ≤ Real.sqrt 3*(conjugate (Real.sqrt 3) (path.state t)).g22-
      (conjugate (Real.sqrt 3) (path.state t)).g21 at h1
  change 0 ≤ (conjugate (-Real.sqrt 3) (path.state t)).g21 ∧
    0 ≤ Real.sqrt 3*(conjugate (-Real.sqrt 3) (path.state t)).g22-
      (conjugate (-Real.sqrt 3) (path.state t)).g21 at h2
  dsimp [conjugate] at h1 h2
  have h1' := h1.2
  have h2' := h2.2
  ring_nf at h1' h2'
  simp only [hs] at h1' h2'
  constructor
  · exact h0.1
  · linarith only [h0.2]
  · nlinarith only [h1.1]
  · nlinarith only [h1']
  · nlinarith only [h2.1]
  · nlinarith only [h2']
  · exact path.norm_bound t ht

#print axioms RegularPath.group_bounds
end Certificate.Confinement
