import Certificate.GeometricCoordinates
import Mathlib.Tactic.Positivity

/-! Algebraic consequences of Hales--Vajjha's compact domain.  These proofs
replace the numerical maximization and symbolic checks in M14 section 7.
The theorem that a minimizing disc stays in this domain is not assumed here
as an axiom: membership is an explicit hypothesis of each consequence. -/
namespace Certificate.Confinement
set_option maxHeartbeats 0

noncomputable def rho0 (x : State) : ℝ := Real.sqrt 3 / 3 * (x.p + x.h) + x.a
noncomputable def rho1 (x : State) : ℝ := Real.sqrt 3 / 3 * (x.p + x.h) - x.a
noncomputable def rho2 (x : State) : ℝ := Real.sqrt 3 / 3 * (x.h - 2 * x.p)

/-- The six symmetric inequalities defining the published compact domain h**.
The pair-sum threshold is written as `4 sqrt(3)/27 = 4/(9 sqrt(3))`. -/
def HVCompact (x : State) : Prop :=
  1/15 ≤ rho0 x ∧ 1/15 ≤ rho1 x ∧ 1/15 ≤ rho2 x ∧
  4 * Real.sqrt 3 / 27 ≤ rho0 x + rho1 x ∧
  4 * Real.sqrt 3 / 27 ≤ rho0 x + rho2 x ∧
  4 * Real.sqrt 3 / 27 ≤ rho1 x + rho2 x

theorem sqrt_three_bounds : (1731 : ℝ)/1000 ≤ Real.sqrt 3 ∧ Real.sqrt 3 ≤ 7/4 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have hp := Real.sqrt_nonneg (3 : ℝ)
  constructor <;> nlinarith

theorem rho_sum (x : State) : rho0 x + rho1 x + rho2 x = Real.sqrt 3 * x.h := by
  unfold rho0 rho1 rho2
  ring

theorem rho_e2 (x : State) (hd : x.h^2-x.a^2-x.p^2=1) :
    rho0 x * rho1 x + rho1 x * rho2 x + rho2 x * rho0 x = 1 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  unfold rho0 rho1 rho2
  ring_nf
  simp only [hs]
  nlinarith only [hd]

/-- A rational bound suffices; no exact maximizer, calculus, or interval grid is needed. -/
theorem ordered_rho_sum_bound (u v w : ℝ)
    (hu : 1/15 ≤ u) (huv : u ≤ v) (hvw : v ≤ w)
    (hpair : (32 : ℝ)/125 ≤ u+v)
    (he2 : u*v+v*w+w*u=1) : u+v+w ≤ 83/20 := by
  have hv : 1/15 ≤ v := hu.trans huv
  have hprod : (u-1/15)*(v-1/15) ≥ 0 :=
    mul_nonneg (sub_nonneg.mpr hu) (sub_nonneg.mpr hv)
  have hsmall : 3*(u+v)^2 ≤ 4 := by
    have h1 : 0 ≤ (v-u)*(v+3*u) := mul_nonneg (sub_nonneg.mpr huv) (by linarith)
    have h2 : 0 ≤ (u+v)*(w-v) := mul_nonneg (by linarith) (sub_nonneg.mpr hvw)
    nlinarith only [h1,h2,he2]
  have hupper : u+v ≤ 6/5 := by nlinarith only [hsmall]
  have hinterval : 0 ≤ (u+v-32/125)*(6/5-(u+v)) :=
    mul_nonneg (sub_nonneg.mpr hpair) (sub_nonneg.mpr hupper)
  have hquad : (u+v)^2 - (253/60)*(u+v) + 226/225 < 0 := by
    nlinarith only [hinterval,hpair]
  have hmul : (u+v)*(u+v+w-83/20) < 0 := by
    nlinarith only [hprod,he2,hquad]
  by_contra hn
  have hnonneg : 0 ≤ (u+v)*(u+v+w-83/20) :=
    mul_nonneg (by linarith) (by linarith)
  linarith

theorem unordered_rho_sum_bound (u v w : ℝ)
    (hu : 1/15 ≤ u) (hv : 1/15 ≤ v) (hw : 1/15 ≤ w)
    (huv : (32 : ℝ)/125 ≤ u+v) (huw : (32 : ℝ)/125 ≤ u+w)
    (hvw : (32 : ℝ)/125 ≤ v+w)
    (he2 : u*v+v*w+w*u=1) : u+v+w ≤ 83/20 := by
  rcases le_total u v with h1 | h1
  · rcases le_total v w with h2 | h2
    · exact ordered_rho_sum_bound u v w hu h1 h2 huv he2
    · rcases le_total u w with h3 | h3
      · have hh := ordered_rho_sum_bound u w v hu h3 h2 huw (by nlinarith only [he2])
        linarith
      · have hh := ordered_rho_sum_bound w u v hw h3 h1 (by linarith) (by nlinarith only [he2])
        linarith
  · rcases le_total u w with h2 | h2
    · have hh := ordered_rho_sum_bound v u w hv h1 h2 (by linarith) (by nlinarith only [he2])
      linarith
    · rcases le_total v w with h3 | h3
      · have hh := ordered_rho_sum_bound v w u hv h3 h2 hvw (by nlinarith only [he2])
        linarith
      · have hh := ordered_rho_sum_bound w v u hw h3 h1 (by linarith) (by nlinarith only [he2])
        linarith

theorem height_bounds (x : State) (hd : x.h^2-x.a^2-x.p^2=1) (hx : HVCompact x) :
    1 ≤ x.h ∧ x.h ≤ 12/5 := by
  obtain ⟨h0,h1,h2,h01,h02,h12⟩ := hx
  obtain ⟨hslo,hshi⟩ := sqrt_three_bounds
  have hs := rho_sum x
  have he2 := rho_e2 x hd
  have he := unordered_rho_sum_bound (rho0 x) (rho1 x) (rho2 x)
    h0 h1 h2 (by linarith) (by linarith) (by linarith) he2
  have hpos : 0 < x.h := by
    have : 0 < Real.sqrt 3 * x.h := by linarith
    exact (mul_pos_iff.mp this).resolve_right (by intro h; linarith [h.1]) |>.2
  constructor
  · nlinarith [sq_nonneg x.a, sq_nonneg x.p]
  · have hh := mul_nonneg (sub_nonneg.mpr hslo) (le_of_lt hpos)
    nlinarith only [hs,he,hh]

#print axioms height_bounds
end Certificate.Confinement
