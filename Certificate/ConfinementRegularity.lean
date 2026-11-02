import Certificate.GeometricCoordinates
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace Certificate.Confinement
open MeasureTheory Set Filter
set_option maxHeartbeats 0

/-- An absolutely continuous scalar function whose a.e. derivative has a
continuous representative has that derivative at every interior point. -/
theorem hasDerivAt_of_ac_continuous_rhs (f v : ℝ → ℝ) (T : ℝ) (hT : 0 ≤ T)
    (hf : AbsolutelyContinuousOnInterval f 0 T)
    (hv : ContinuousOn v (Icc 0 T))
    (hderiv : ∀ᵐ t ∂volume.restrict (Icc 0 T), HasDerivAt f (v t) t) :
    ∀ t ∈ Ioo 0 T, HasDerivAt f (v t) t := by
  have hprimitive : ∀ s ∈ Icc 0 T, f s = f 0+∫ t in 0..s, v t := by
    intro s hs
    have hac : AbsolutelyContinuousOnInterval f 0 s := hf.mono (by
      rw [uIcc_of_le hs.1,uIcc_of_le hT]
      exact Icc_subset_Icc le_rfl hs.2)
    have heq : (∫ t in 0..s, deriv f t) = ∫ t in 0..s, v t := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [ae_imp_of_ae_restrict hderiv] with t ht hts
      rw [uIoc_of_le hs.1] at hts
      exact (ht ⟨hts.1.le,hts.2.trans hs.2⟩).deriv
    rw [hac.integral_deriv_eq_sub] at heq
    linarith
  intro t ht
  have hint : IntervalIntegrable v volume 0 t :=
    (show ContinuousOn v (uIcc 0 t) by
      rw [uIcc_of_le ht.1.le]
      exact hv.mono (Icc_subset_Icc le_rfl ht.2.le)).intervalIntegrable
  have hv' : ContinuousOn v (Ioo 0 T) := hv.mono Ioo_subset_Icc_self
  have hp := (intervalIntegral.integral_hasDerivAt_right hint
    (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo hv' t ht)
    (hv'.continuousAt (isOpen_Ioo.mem_nhds ht))).const_add (f 0)
  apply hp.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
  exact hprimitive s ⟨hs.1.le,hs.2.le⟩

#print axioms hasDerivAt_of_ac_continuous_rhs
end Certificate.Confinement
