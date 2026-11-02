import Certificate.ConfinementEnergy
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

namespace Certificate.Confinement
open MeasureTheory Set
set_option maxHeartbeats 0

theorem constant_on_Icc_of_hasDerivAt_zero (f : ℝ → ℝ) (T : ℝ)
    (hf : ContinuousOn f (Icc 0 T))
    (hd : ∀ t ∈ Ioo 0 T, HasDerivAt f 0 t) :
    ∀ t ∈ Icc 0 T, f t=f 0 := by
  intro t ht
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1
    (hf.mono (Icc_subset_Icc le_rfl ht.2))
    (fun s hs => hd s ⟨hs.1,hs.2.trans_le ht.2⟩)
    (intervalIntegrable_const (a:=0) (b:=t) (μ:=volume) (c:=(0:ℝ)))
  simp only [intervalIntegral.integral_zero] at he
  linarith

theorem normalized_pair_derivative (v w : ℝ → ℝ) (t dv dw : ℝ)
    (hv : HasDerivAt v dv t) (hw : HasDerivAt w dw t)
    (hn : 0 < (v t)^2+(w t)^2) :
    HasDerivAt (fun s => v s/Real.sqrt ((v s)^2+(w s)^2))
      (((w t*dv-v t*dw)/((v t)^2+(w t)^2))*(w t/Real.sqrt ((v t)^2+(w t)^2))) t ∧
    HasDerivAt (fun s => w s/Real.sqrt ((v s)^2+(w s)^2))
      (-((w t*dv-v t*dw)/((v t)^2+(w t)^2))*(v t/Real.sqrt ((v t)^2+(w t)^2))) t := by
  let r := Real.sqrt ((v t)^2+(w t)^2)
  have hr : r ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hn)
  have hr2 : r^2=(v t)^2+(w t)^2 := Real.sq_sqrt hn.le
  have hdr := ((hv.pow 2).add (hw.pow 2)).sqrt (ne_of_gt hn)
  constructor
  · convert! hv.div hdr hr using 1
    norm_num only [Pi.add_apply,Pi.pow_apply,Nat.reduceSub,pow_one,Nat.cast_ofNat]
    change ((w t*dv-v t*dw)/((v t)^2+(w t)^2))*(w t/r) =
      (dv*r-v t*((2*v t*dv+2*w t*dw)/(2*r)))/r^2
    rw [← hr2]
    field_simp
    linear_combination -dv*hr2
  · convert! hw.div hdr hr using 1
    norm_num only [Pi.add_apply,Pi.pow_apply,Nat.reduceSub,pow_one,Nat.cast_ofNat]
    change -((w t*dv-v t*dw)/((v t)^2+(w t)^2))*(v t/r) =
      (dw*r-w t*((2*v t*dv+2*w t*dw)/(2*r)))/r^2
    rw [← hr2]
    field_simp
    linear_combination -dw*hr2

/-- A continuous nonvanishing row has the angle obtained by integrating its
angular velocity. This supplies the lift rather than assuming a winding number. -/
theorem row_polar_representation (v w dv dw : ℝ → ℝ) (T : ℝ) (hT : 0 ≤ T)
    (hv : ContinuousOn v (Icc 0 T)) (hw : ContinuousOn w (Icc 0 T))
    (hdv : ContinuousOn dv (Icc 0 T)) (hdw : ContinuousOn dw (Icc 0 T))
    (hv' : ∀ t ∈ Ioo 0 T, HasDerivAt v (dv t) t)
    (hw' : ∀ t ∈ Ioo 0 T, HasDerivAt w (dw t) t)
    (hn : ∀ t ∈ Icc 0 T, 0 < (v t)^2+(w t)^2)
    (h0v : v 0=0) (h0w : w 0=1) :
    let theta := fun t => ∫ s in 0..t, (w s*dv s-v s*dw s)/((v s)^2+(w s)^2)
    ∀ t ∈ Icc 0 T,
      v t=Real.sqrt ((v t)^2+(w t)^2)*Real.sin (theta t) ∧
      w t=Real.sqrt ((v t)^2+(w t)^2)*Real.cos (theta t) := by
  let q := fun t => (w t*dv t-v t*dw t)/((v t)^2+(w t)^2)
  let theta := fun t => ∫ s in 0..t, q s
  let r := fun t => Real.sqrt ((v t)^2+(w t)^2)
  let u := fun t => v t/r t
  let z := fun t => w t/r t
  have hr : ∀ t ∈ Icc 0 T, r t ≠ 0 := fun t ht => ne_of_gt (Real.sqrt_pos.mpr (hn t ht))
  have hq : ContinuousOn q (Icc 0 T) :=
    ((hw.mul hdv).sub (hv.mul hdw)).div ((hv.pow 2).add (hw.pow 2))
      (fun t ht => ne_of_gt (hn t ht))
  have hqi : IntervalIntegrable q volume 0 T :=
    (show ContinuousOn q (uIcc 0 T) by rwa [uIcc_of_le hT]).intervalIntegrable
  have htheta : ContinuousOn theta (Icc 0 T) := by
    simpa only [theta,uIcc_of_le hT] using
      intervalIntegral.continuousOn_primitive_interval
        (show IntegrableOn q (uIcc 0 T) volume by
          rw [uIcc_of_le hT]; exact hq.integrableOn_Icc)
  have htheta' : ∀ t ∈ Ioo 0 T, HasDerivAt theta (q t) t := by
    intro t ht
    exact intervalIntegral.integral_hasDerivAt_right
      (hqi.mono_set (by rw [uIcc_of_le ht.1.le,uIcc_of_le hT]; exact Icc_subset_Icc le_rfl ht.2.le))
      (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo (hq.mono Ioo_subset_Icc_self) t ht)
      ((hq.mono Ioo_subset_Icc_self).continuousAt (isOpen_Ioo.mem_nhds ht))
  have hu : ContinuousOn u (Icc 0 T) := hv.div (((hv.pow 2).add (hw.pow 2)).sqrt) hr
  have hz : ContinuousOn z (Icc 0 T) := hw.div (((hv.pow 2).add (hw.pow 2)).sqrt) hr
  have huz : ∀ t ∈ Ioo 0 T,
      HasDerivAt u (q t*z t) t ∧ HasDerivAt z (-q t*u t) t := by
    intro t ht
    exact normalized_pair_derivative v w t (dv t) (dw t) (hv' t ht) (hw' t ht)
      (hn t ⟨ht.1.le,ht.2.le⟩)
  have hA := constant_on_Icc_of_hasDerivAt_zero
    (fun t => u t*Real.cos (theta t)-z t*Real.sin (theta t)) T
    ((hu.mul (Real.continuous_cos.comp_continuousOn htheta)).sub
      (hz.mul (Real.continuous_sin.comp_continuousOn htheta))) (by
      intro t ht
      obtain ⟨hdu,hdz⟩ := huz t ht
      convert! (hdu.mul (htheta' t ht).cos).sub (hdz.mul (htheta' t ht).sin) using 1 <;> ring)
  have hB := constant_on_Icc_of_hasDerivAt_zero
    (fun t => u t*Real.sin (theta t)+z t*Real.cos (theta t)) T
    ((hu.mul (Real.continuous_sin.comp_continuousOn htheta)).add
      (hz.mul (Real.continuous_cos.comp_continuousOn htheta))) (by
      intro t ht
      obtain ⟨hdu,hdz⟩ := huz t ht
      convert! (hdu.mul (htheta' t ht).sin).add (hdz.mul (htheta' t ht).cos) using 1 <;> ring)
  change ∀ t ∈ Icc 0 T, v t=r t*Real.sin (theta t) ∧ w t=r t*Real.cos (theta t)
  intro t ht
  have ha := hA t ht
  have hb := hB t ht
  have htheta0 : theta 0=0 := by simp [theta]
  have hu0 : u 0=0 := by simp [u,h0v]
  have hz0 : z 0=1 := by norm_num [z,r,h0v,h0w]
  simp only [htheta0,hu0,hz0,Real.cos_zero,Real.sin_zero,mul_one,mul_zero,zero_sub,
    sub_zero,zero_add] at ha hb
  have htrig := Real.sin_sq_add_cos_sq (theta t)
  have huval : u t=Real.sin (theta t) := by
    linear_combination Real.cos (theta t)*ha+Real.sin (theta t)*hb-u t*htrig
  have hzval : z t=Real.cos (theta t) := by
    linear_combination -Real.sin (theta t)*ha+Real.cos (theta t)*hb-z t*htrig
  constructor
  · exact (div_eq_iff (hr t ht)).mp huval |>.trans (mul_comm _ _)
  · exact (div_eq_iff (hr t ht)).mp hzval |>.trans (mul_comm _ _)

#print axioms row_polar_representation
end Certificate.Confinement
