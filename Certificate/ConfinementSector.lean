import Certificate.ConfinementPolar
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

namespace Certificate.Confinement
open MeasureTheory Set
set_option maxHeartbeats 0

theorem angular_velocity_bounds (v w a p h : ℝ) (hn : 0 < v^2+w^2)
    (hh : 0 ≤ h) (hd : h^2-a^2-p^2=1) :
    0 ≤ (w*(a*v+(p+h)*w)-v*((p-h)*v-a*w))/(v^2+w^2) ∧
    (w*(a*v+(p+h)*w)-v*((p-h)*v-a*w))/(v^2+w^2) ≤ 2*h := by
  let D := p*(w^2-v^2)+2*a*v*w
  have hid : (a^2+p^2)*(v^2+w^2)^2-D^2 = (a*(w^2-v^2)-2*p*v*w)^2 := by
    dsimp [D]; ring
  have hnorm : D^2 ≤ (h*(v^2+w^2))^2 := by
    have hh2 : a^2+p^2 ≤ h^2 := by linarith
    have hmul := mul_le_mul_of_nonneg_right hh2 (sq_nonneg (v^2+w^2))
    nlinarith only [hid,hmul,sq_nonneg (a*(w^2-v^2)-2*p*v*w)]
  have hsize : |D| ≤ h*(v^2+w^2) :=
    (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hh hn.le)).mp (by simpa only [sq_abs] using hnorm)
  obtain ⟨hl,hu⟩ := abs_le.mp hsize
  constructor
  · apply div_nonneg _ hn.le
    dsimp [D] at hl
    nlinarith only [hl]
  · apply (div_le_iff₀ hn).mpr
    dsimp [D] at hu
    nlinarith only [hu]

/-- A row satisfying the matrix ODE starts at angle zero, ends at pi/3,
and cannot wind once under the stated cost bound. Hence it stays in the sector. -/
theorem row_sector (v w a p h : ℝ → ℝ) (T : ℝ) (hT : 0 ≤ T)
    (hv : ContinuousOn v (Icc 0 T)) (hw : ContinuousOn w (Icc 0 T))
    (ha : ContinuousOn a (Icc 0 T)) (hp : ContinuousOn p (Icc 0 T))
    (hh : ContinuousOn h (Icc 0 T))
    (hv' : ∀ t ∈ Ioo 0 T, HasDerivAt v (a t*v t+(p t+h t)*w t) t)
    (hw' : ∀ t ∈ Ioo 0 T, HasDerivAt w ((p t-h t)*v t-a t*w t) t)
    (hn : ∀ t ∈ Icc 0 T, 0 < (v t)^2+(w t)^2)
    (hhpos : ∀ t ∈ Icc 0 T, 0 ≤ h t)
    (hdet : ∀ t ∈ Icc 0 T, (h t)^2-(a t)^2-(p t)^2=1)
    (h0v : v 0=0) (h0w : w 0=1)
    (hTv : v T=Real.sqrt 3/2) (hTw : w T=1/2)
    (hcost : (∫ t in 0..T, h t) ≤ 311/300) :
    ∀ t ∈ Icc 0 T, 0 ≤ v t ∧ 0 ≤ Real.sqrt 3*w t-v t := by
  let dv := fun t => a t*v t+(p t+h t)*w t
  let dw := fun t => (p t-h t)*v t-a t*w t
  let q := fun t => (w t*dv t-v t*dw t)/((v t)^2+(w t)^2)
  let theta := fun t => ∫ s in 0..t, q s
  have hdv : ContinuousOn dv (Icc 0 T) := (ha.mul hv).add ((hp.add hh).mul hw)
  have hdw : ContinuousOn dw (Icc 0 T) := ((hp.sub hh).mul hv).sub (ha.mul hw)
  have hpolar := row_polar_representation v w dv dw T hT hv hw hdv hdw hv' hw' hn h0v h0w
  change ∀ t ∈ Icc 0 T,
    v t=Real.sqrt ((v t)^2+(w t)^2)*Real.sin (theta t) ∧
    w t=Real.sqrt ((v t)^2+(w t)^2)*Real.cos (theta t) at hpolar
  have hqb : ∀ t ∈ Icc 0 T, 0 ≤ q t ∧ q t ≤ 2*h t := by
    intro t ht
    exact angular_velocity_bounds (v t) (w t) (a t) (p t) (h t) (hn t ht) (hhpos t ht) (hdet t ht)
  have hq : ContinuousOn q (Icc 0 T) :=
    ((hw.mul hdv).sub (hv.mul hdw)).div ((hv.pow 2).add (hw.pow 2))
      (fun t ht => ne_of_gt (hn t ht))
  have hqi : IntervalIntegrable q volume 0 T :=
    (show ContinuousOn q (uIcc 0 T) by rwa [uIcc_of_le hT]).intervalIntegrable
  have hhi : IntervalIntegrable h volume 0 T :=
    (show ContinuousOn h (uIcc 0 T) by rwa [uIcc_of_le hT]).intervalIntegrable
  have htheta_nonneg : ∀ t ∈ Icc 0 T, 0 ≤ theta t := by
    intro t ht
    exact intervalIntegral.integral_nonneg ht.1 (fun s hs => (hqb s ⟨hs.1,hs.2.trans ht.2⟩).1)
  have htheta_upper : theta T ≤ 311/150 := by
    have hi := intervalIntegral.integral_mono_on hT hqi (hhi.const_mul 2)
      (fun t ht => (hqb t ht).2)
    rw [intervalIntegral.integral_const_mul] at hi
    change (∫ s in 0..T, q s) ≤ 311/150
    linarith
  have htheta_le_end : ∀ t ∈ Icc 0 T, theta t ≤ theta T := by
    intro t ht
    exact intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2
      (by filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs using (hqb s ⟨hs.1.le,hs.2⟩).1) hqi
  have hroot : Real.sqrt ((v T)^2+(w T)^2)=1 := by
    rw [hTv,hTw]
    have hs := Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)
    have he : (Real.sqrt (3:ℝ)/2)^2+(1/2:ℝ)^2=1 := by nlinarith only [hs]
    rw [he,Real.sqrt_one]
  have htheta_end : theta T=Real.pi/3 := by
    have hpi : (5:ℝ)/2 < Real.pi := by
      have hs := Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)
      have hp := Real.sqrt_nonneg (3:ℝ)
      have hr : (17:ℝ)/10 ≤ Real.sqrt 3 := by nlinarith
      have ht := Real.sin_le (show 0 ≤ Real.pi/3 by positivity)
      rw [Real.sin_pi_div_three] at ht
      linarith
    apply Real.injOn_cos
      ⟨htheta_nonneg T ⟨hT,le_rfl⟩,by linarith⟩
      ⟨by positivity,by linarith [Real.pi_pos]⟩
    have he := (hpolar T ⟨hT,le_rfl⟩).2
    rw [hroot,one_mul,hTw] at he
    rw [Real.cos_pi_div_three]
    exact he.symm
  intro t ht
  have hlo := htheta_nonneg t ht
  have hhi := htheta_le_end t ht
  rw [htheta_end] at hhi
  have hs : 0 ≤ Real.sin (theta t) := Real.sin_nonneg_of_nonneg_of_le_pi hlo (by linarith [Real.pi_pos])
  have hsr : 0 ≤ Real.sin (Real.pi/3-theta t) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [Real.pi_pos])
  rw [Real.sin_sub,Real.sin_pi_div_three,Real.cos_pi_div_three] at hsr
  have hc : 0 ≤ Real.sqrt 3*Real.cos (theta t)-Real.sin (theta t) := by nlinarith only [hsr]
  obtain ⟨hvval,hwval⟩ := hpolar t ht
  constructor
  · rw [hvval]; exact mul_nonneg (Real.sqrt_nonneg _) hs
  · calc
      0 ≤ Real.sqrt ((v t)^2+(w t)^2)*
          (Real.sqrt 3*Real.cos (theta t)-Real.sin (theta t)) :=
        mul_nonneg (Real.sqrt_nonneg _) hc
      _ = Real.sqrt 3*w t-v t := by
        linear_combination hvval-Real.sqrt 3*hwval

#print axioms row_sector
end Certificate.Confinement
