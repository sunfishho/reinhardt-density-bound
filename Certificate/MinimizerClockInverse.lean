import Certificate.MinimizerDeterminantClock
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Inverse

/-! The determinant clock is a global increasing C1 bijection. Positivity
and periodicity give a uniform lower speed bound, so its inverse is regular
and defines actual reparametrized balanced boundary curves. -/
namespace Certificate.Packing
open Set Filter Topology MeasureTheory
open scoped NNReal
set_option maxHeartbeats 0

theorem minimizerAngularBoundary_periodic :
    Function.Periodic minimizerAngularBoundary (2 * Real.pi) := by
  intro t
  apply Subtype.ext
  simp only [minimizerAngularBoundary, unitCirclePoint, Real.cos_add_two_pi, Real.sin_add_two_pi]

theorem minimizerAngularVelocity_periodic :
    Function.Periodic minimizerAngularVelocity (2 * Real.pi) := by
  intro t
  simp only [minimizerAngularVelocity, unitCirclePoint, unitCircleVelocity,
    Real.cos_add_two_pi, Real.sin_add_two_pi]

theorem minimizerDeterminantSpeed_periodic :
    Function.Periodic minimizerDeterminantSpeed (2 * Real.pi) := by
  intro t
  simp only [minimizerDeterminantSpeed, minimizerAngularSuccessorVelocity,
    minimizerAngularMidpoint, minimizerAngularBoundary_periodic t, minimizerAngularVelocity_periodic t]

theorem minimizerDeterminantSpeed_uniform_positive :
    ∃ m : ℝ, 0 < m ∧ ∀ t, m ≤ minimizerDeterminantSpeed t := by
  have hk := minimizerDeterminantSpeed_periodic.compact_of_continuous
    (by positivity : 2 * Real.pi ≠ 0) continuous_minimizerDeterminantSpeed
  obtain ⟨m,⟨t,ht⟩,hm⟩ := hk.exists_isMinOn (range_nonempty _) continuous_id.continuousOn
  refine ⟨m,?_,fun s => hm (mem_range_self s)⟩
  rw [← ht]
  exact minimizerDeterminantSpeed_pos t

theorem minimizerDeterminantClock_surjective : Function.Surjective minimizerDeterminantClock := by
  obtain ⟨m,hm,hbound⟩ := minimizerDeterminantSpeed_uniform_positive
  have hg : ∀ {x y : ℝ}, x ≤ y → m * (y-x) ≤
      minimizerDeterminantClock y-minimizerDeterminantClock x := by
    intro x y hxy
    exact mul_sub_le_image_sub_of_le_deriv
      (fun t => (hasDerivAt_minimizerDeterminantClock t).differentiableAt)
      (fun t => by rw [(hasDerivAt_minimizerDeterminantClock t).deriv]; exact hbound t) hxy
  intro y
  let s := (|y|+1)/m
  have hs : 0 < s := div_pos (by positivity) hm
  have he : m*s=|y|+1 := by dsimp [s]; field_simp
  have hl := hg (x := -s) (y := 0) (by linarith)
  have hr := hg (x := 0) (y := s) hs.le
  rw [minimizerDeterminantClock_zero] at hl hr
  have hy : y ∈ Icc (minimizerDeterminantClock (-s)) (minimizerDeterminantClock s) := by
    constructor <;> nlinarith [le_abs_self y, neg_abs_le y]
  obtain ⟨x,_,hx⟩ := intermediate_value_Icc (by linarith : -s ≤ s)
    contDiff_minimizerDeterminantClock.continuous.continuousOn hy
  exact ⟨x,hx⟩

noncomputable def minimizerClockOrderIso : ℝ ≃o ℝ :=
  strictMono_minimizerDeterminantClock.orderIsoOfSurjective _ minimizerDeterminantClock_surjective

noncomputable def minimizerAngularTime (t : ℝ) : ℝ := minimizerClockOrderIso.symm t

theorem minimizerDeterminantClock_angularTime (t : ℝ) :
    minimizerDeterminantClock (minimizerAngularTime t) = t :=
  minimizerClockOrderIso.apply_symm_apply t

theorem minimizerAngularTime_clock (t : ℝ) :
    minimizerAngularTime (minimizerDeterminantClock t) = t :=
  minimizerClockOrderIso.symm_apply_apply t

theorem continuous_minimizerAngularTime : Continuous minimizerAngularTime :=
  minimizerClockOrderIso.symm.continuous

theorem strictMono_minimizerAngularTime : StrictMono minimizerAngularTime :=
  minimizerClockOrderIso.symm.strictMono

theorem minimizerAngularTime_zero : minimizerAngularTime 0 = 0 := by
  simpa only [minimizerDeterminantClock_zero] using minimizerAngularTime_clock 0

theorem hasDerivAt_minimizerAngularTime (t : ℝ) :
    HasDerivAt minimizerAngularTime (minimizerDeterminantSpeed (minimizerAngularTime t))⁻¹ t :=
  HasDerivAt.of_local_left_inverse continuous_minimizerAngularTime.continuousAt
    (hasDerivAt_minimizerDeterminantClock (minimizerAngularTime t))
    (minimizerDeterminantSpeed_pos _).ne'
    (Eventually.of_forall minimizerDeterminantClock_angularTime)

theorem contDiff_minimizerAngularTime : ContDiff ℝ 1 minimizerAngularTime := by
  apply contDiff_one_iff_deriv.2
  refine ⟨fun t => (hasDerivAt_minimizerAngularTime t).differentiableAt,?_⟩
  have he : deriv minimizerAngularTime =
      fun t => (minimizerDeterminantSpeed (minimizerAngularTime t))⁻¹ :=
    funext (fun t => (hasDerivAt_minimizerAngularTime t).deriv)
  rw [he]
  exact (continuous_minimizerDeterminantSpeed.comp continuous_minimizerAngularTime).inv₀
    (fun t => (minimizerDeterminantSpeed_pos _).ne')

noncomputable def minimizerBalancedBoundary (i : Fin 6) (t : ℝ) : E :=
  minimizerAngularBalancedCurve i (minimizerAngularTime t)

noncomputable def minimizerBalancedVelocity (i : Fin 6) (t : ℝ) : E :=
  minimizerNormalizedAngularVelocity i (minimizerAngularTime t)

theorem hasDerivAt_minimizerBalancedBoundary (i : Fin 6) (t : ℝ) :
    HasDerivAt (minimizerBalancedBoundary i) (minimizerBalancedVelocity i t) t := by
  convert! (hasDerivAt_minimizerAngularBalancedCurve i (minimizerAngularTime t)).scomp t
    (hasDerivAt_minimizerAngularTime t) using 1

theorem contDiff_minimizerBalancedBoundary (i : Fin 6) :
    ContDiff ℝ 1 (minimizerBalancedBoundary i) :=
  (contDiff_minimizerAngularBalancedCurve i).comp contDiff_minimizerAngularTime

theorem minimizerBalancedBoundary_frontier (i : Fin 6) (t : ℝ) :
    minimizerBalancedBoundary i t ∈ frontier ratioMinimizingBody :=
  minimizerAngularBalancedCurve_frontier i _

theorem minimizerBalancedVelocity_det (t : ℝ) :
    det2 (minimizerBalancedVelocity 0 t) (minimizerBalancedVelocity 1 t) = Real.sqrt 3 / 2 :=
  minimizerNormalizedAngularVelocity_det _

end Certificate.Packing
