import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-! A scalar energy estimate for the matrix path.  Both endpoints are used.
This avoids hyperbolic distance, matrix exponentials, and numerical cosh bounds. -/
namespace Certificate.Confinement
open MeasureTheory Set
set_option maxHeartbeats 0

theorem two_endpoint_bound (f d h : ℝ → ℝ) (T t k e : ℝ)
    (ht : t ∈ Icc 0 T) (hf : ContinuousOn f (Icc 0 T))
    (hh : ContinuousOn h (Icc 0 T))
    (hd : ∀ s ∈ Ioo 0 T, HasDerivAt f (d s) s)
    (hb : ∀ s ∈ Ioo 0 T, -k*h s ≤ d s ∧ d s ≤ k*h s)
    (h0 : f 0=e) (hT : f T=e) :
    2*f t ≤ 2*e+k*(∫ s in 0..T, h s) := by
  have hl : f t-f 0 ≤ ∫ s in 0..t, k*h s := by
    apply intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le ht.1
      (hf.mono (Icc_subset_Icc le_rfl ht.2))
      (fun s hs => (hd s ⟨hs.1,hs.2.trans_le ht.2⟩).hasDerivWithinAt)
      ((continuousOn_const.mul hh).mono (Icc_subset_Icc le_rfl ht.2)).integrableOn_Icc
    exact fun s hs => (hb s ⟨hs.1,hs.2.trans_le ht.2⟩).2
  have hr : -f T-(-f t) ≤ ∫ s in t..T, k*h s := by
    apply intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le ht.2
      (hf.neg.mono (Icc_subset_Icc ht.1 le_rfl))
      (fun s hs => (hd s ⟨ht.1.trans_lt hs.1,hs.2⟩).neg.hasDerivWithinAt)
      ((continuousOn_const.mul hh).mono (Icc_subset_Icc ht.1 le_rfl)).integrableOn_Icc
    intro s hs
    change -d s ≤ k*h s
    have := (hb s ⟨ht.1.trans_lt hs.1,hs.2⟩).1
    linarith
  have hint : IntervalIntegrable h volume 0 T :=
    (show ContinuousOn h (uIcc 0 T) by rwa [uIcc_of_le (ht.1.trans ht.2)]).intervalIntegrable
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hint.mono_set (by rw [uIcc_of_le ht.1,uIcc_of_le (ht.1.trans ht.2)]; exact Icc_subset_Icc le_rfl ht.2))
    (hint.mono_set (by rw [uIcc_of_le ht.2,uIcc_of_le (ht.1.trans ht.2)]; exact Icc_subset_Icc ht.1 le_rfl))
  rw [intervalIntegral.integral_const_mul] at hl hr
  rw [h0] at hl
  rw [hT] at hr
  rw [← hsplit,mul_add]
  linarith only [hl,hr]

theorem regularized_slope_bound (E M h d : ℝ)
    (hE : 0 ≤ E) (hEM : E ≤ M) (hh : 0 ≤ h)
    (hd : d^2 ≤ (121/36)*h^2*E*(E+4)) :
    -(11/12)*h*Real.sqrt (M+4) ≤ d/(2*Real.sqrt (E+1/100000000)) ∧
    d/(2*Real.sqrt (E+1/100000000)) ≤ (11/12)*h*Real.sqrt (M+4) := by
  let r := Real.sqrt (E+1/100000000)
  let s := Real.sqrt (M+4)
  have hr : 0 < r := Real.sqrt_pos.mpr (by linarith)
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hr2 : r^2=E+1/100000000 := Real.sq_sqrt (by linarith)
  have hs2 : s^2=M+4 := Real.sq_sqrt (by linarith)
  have hmul : E*(E+4) ≤ r^2*s^2 := by
    have := mul_nonneg hE (sub_nonneg.mpr hEM)
    rw [hr2,hs2]
    nlinarith
  have hh2 : 0 ≤ (121/36:ℝ)*h^2 := by positivity
  have hd2 : d^2 ≤ ((11/6)*h*r*s)^2 := by
    have := mul_le_mul_of_nonneg_left hmul hh2
    nlinarith only [hd,this]
  have hsize : |d| ≤ (11/6)*h*r*s :=
    (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp (by simpa only [sq_abs] using hd2)
  obtain ⟨hl,hu⟩ := abs_le.mp hsize
  constructor
  · apply (le_div_iff₀ (by positivity : 0 < 2*r)).mpr
    nlinarith only [hl]
  · apply (div_le_iff₀ (by positivity : 0 < 2*r)).mpr
    nlinarith only [hu]

/-- A nonnegative energy returning to zero cannot reach 6/5 under this
derivative bound and total height budget. The regularization is a fixed exact
rational; no limiting argument or floating-point estimate is used. -/
theorem energy_bound (E d h : ℝ → ℝ) (T : ℝ) (hT : 0 ≤ T)
    (hEcont : ContinuousOn E (Icc 0 T)) (hhcont : ContinuousOn h (Icc 0 T))
    (hEnonneg : ∀ t ∈ Icc 0 T, 0 ≤ E t)
    (hhnonneg : ∀ t ∈ Icc 0 T, 0 ≤ h t)
    (hEderiv : ∀ t ∈ Ioo 0 T, HasDerivAt E (d t) t)
    (hdbound : ∀ t ∈ Ioo 0 T, (d t)^2 ≤ (121/36)*(h t)^2*E t*(E t+4))
    (hE0 : E 0=0) (hET : E T=0)
    (hcost : (∫ t in 0..T, h t) ≤ 311/300) :
    ∀ t ∈ Icc 0 T, E t ≤ 6/5 := by
  obtain ⟨t,ht,hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hT) hEcont
  let M := E t
  have hM : 0 ≤ M := hEnonneg t ht
  let f := fun s => Real.sqrt (E s+1/100000000)
  let df := fun s => d s/(2*Real.sqrt (E s+1/100000000))
  have hf : ContinuousOn f (Icc 0 T) := (hEcont.add continuousOn_const).sqrt
  have hdf : ∀ s ∈ Ioo 0 T, HasDerivAt f (df s) s := by
    intro s hs
    exact ((hEderiv s hs).add_const _).sqrt (by
      have := hEnonneg s ⟨hs.1.le,hs.2.le⟩
      linarith)
  have hb : ∀ s ∈ Ioo 0 T,
      -((11/12)*Real.sqrt (M+4))*h s ≤ df s ∧
      df s ≤ ((11/12)*Real.sqrt (M+4))*h s := by
    intro s hs
    have hh := regularized_slope_bound (E s) M (h s) (d s)
      (hEnonneg s ⟨hs.1.le,hs.2.le⟩) (hmax ⟨hs.1.le,hs.2.le⟩)
      (hhnonneg s ⟨hs.1.le,hs.2.le⟩) (hdbound s hs)
    dsimp [df]
    constructor <;> nlinarith only [hh.1,hh.2]
  have hzero : Real.sqrt (1/100000000:ℝ)=1/10000 := by norm_num
  have hp := two_endpoint_bound f df h T t ((11/12)*Real.sqrt (M+4)) (1/10000)
    ht hf hhcont hdf hb (by simp only [f,hE0,zero_add,hzero])
      (by simp only [f,hET,zero_add,hzero])
  have hs := Real.sqrt_nonneg (M+4)
  have hs2 := Real.sq_sqrt (show 0 ≤ M+4 by linarith)
  have hfpos : 0 ≤ f t := Real.sqrt_nonneg _
  have hf2 : (f t)^2=M+1/100000000 := Real.sq_sqrt (by linarith)
  have hcb := mul_le_mul_of_nonneg_left hcost (show 0 ≤ (11/12)*Real.sqrt (M+4) by positivity)
  have hsize : f t ≤ 1/10000+(12/25)*Real.sqrt (M+4) := by
    nlinarith only [hp,hcb,hs]
  have hslinear : 2*Real.sqrt (M+4) ≤ M+5 := by
    nlinarith only [sq_nonneg (Real.sqrt (M+4)-1),hs2]
  have hsize2 := mul_self_le_mul_self hfpos hsize
  have hMb : M ≤ 6/5 := by
    nlinarith only [hsize2,hf2,hs2,hslinear,hs,hM]
  intro s hs'
  exact (hmax hs').trans hMb

#print axioms energy_bound
end Certificate.Confinement
