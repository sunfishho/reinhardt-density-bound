import Certificate.MinimizerBoundaryNormalContinuity
import Certificate.RadialBoundaryConstruction
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! Continuous supporting forms give a continuously differentiable gauge away
from the origin, and hence a C1 radial boundary map. No Lipschitz estimate for
the derivative or balanced critical-hexagon parametrization is claimed. -/
namespace Certificate.Packing
open Set Filter Topology
set_option maxHeartbeats 0

/-- A continuous field of supporting affine functions identifies the derivative.
The two support inequalities squeeze the first-order remainder. -/
theorem hasFDerivAt_of_continuous_support {f : E → ℝ} {F : E → E →L[ℝ] ℝ} {x : E}
    (hc : ContinuousAt F x) (hx : ∀ y, f x+F x (y-x) ≤ f y)
    (hs : ∀ᶠ y in 𝓝 x, ∀ z, f y+F y (z-y) ≤ f z) : HasFDerivAt f (F x) x := by
  apply hasFDerivAt_iff_tendsto.2
  have ht : Tendsto (fun y => ‖F y-F x‖) (𝓝 x) (𝓝 0) := by
    simpa using (hc.tendsto.sub
      (tendsto_const_nhds : Tendsto (fun _ : E => F x) (𝓝 x) (𝓝 (F x)))).norm
  apply squeeze_zero' (Eventually.of_forall (fun y => mul_nonneg (inv_nonneg.2 (norm_nonneg _))
    (norm_nonneg _))) ?_ ht
  filter_upwards [hs] with y hy
  have h0 : 0 ≤ f y-f x-F x (y-x) := by linarith [hx y]
  have h1 : f y-f x-F x (y-x) ≤ (F y-F x) (y-x) := by
    have hz := hy x
    rw [show x-y= -(y-x) by abel,map_neg] at hz
    simp only [sub_apply]
    linarith
  have h2 : f y-f x-F x (y-x) ≤ ‖F y-F x‖*‖y-x‖ :=
    h1.trans ((le_abs_self _).trans ((F y-F x).le_opNorm (y-x)))
  rw [Real.norm_eq_abs,abs_of_nonneg h0]
  by_cases he : y=x
  · simp [he]
  · have hn : 0 < ‖y-x‖ := norm_pos_iff.2 (sub_ne_zero.2 he)
    calc
      ‖y-x‖⁻¹*(f y-f x-F x (y-x)) ≤ ‖y-x‖⁻¹*(‖F y-F x‖*‖y-x‖) :=
        mul_le_mul_of_nonneg_left h2 (inv_nonneg.2 hn.le)
      _ = ‖F y-F x‖ := by field_simp

noncomputable def minimizerRadialFoot (x : E) : E :=
  (gauge ratioMinimizingBody x)⁻¹ • x

theorem minimizerRadialFoot_frontier {x : E} (hx : x ≠ 0) :
    minimizerRadialFoot x ∈ frontier ratioMinimizingBody := by
  apply (gauge_eq_one_iff_mem_frontier ratioMinimizingBody_properties.1.1
    (disc_mem_nhds_zero ratioMinimizingBody_properties.1)).1
  have hp := disc_gauge_pos ratioMinimizingBody_properties.1 hx
  rw [minimizerRadialFoot,gauge_smul_of_nonneg (inv_nonneg.2 hp.le)]
  simp [hp.ne']

lemma continuousOn_minimizerRadialFoot : ContinuousOn minimizerRadialFoot {x : E | x ≠ 0} := by
  have hg := continuous_gauge ratioMinimizingBody_properties.1.1
    (disc_mem_nhds_zero ratioMinimizingBody_properties.1)
  exact (hg.continuousOn.inv₀ (fun x hx =>
    (disc_gauge_pos ratioMinimizingBody_properties.1 hx).ne')).smul continuousOn_id

noncomputable def minimizerGaugeGradientOn (x : {x : E // x ≠ 0}) : E →L[ℝ] ℝ :=
  let p : frontier ratioMinimizingBody := ⟨minimizerRadialFoot x.val,minimizerRadialFoot_frontier x.property⟩
  (minimizerBoundaryNormal p 0) • (coord 0).toContinuousLinearMap+
    (minimizerBoundaryNormal p 1) • (coord 1).toContinuousLinearMap

lemma continuous_minimizerGaugeGradientOn : Continuous minimizerGaugeGradientOn := by
  have hf : Continuous (fun x : {x : E // x ≠ 0} =>
      (⟨minimizerRadialFoot x.val,minimizerRadialFoot_frontier x.property⟩ : frontier ratioMinimizingBody)) :=
    (continuousOn_minimizerRadialFoot.domRestrict).subtype_mk _
  have hn := continuous_minimizerBoundaryNormal.comp hf
  exact (((continuous_apply 0).comp hn).smul continuous_const).add
    (((continuous_apply 1).comp hn).smul continuous_const)

noncomputable def minimizerGaugeGradient (x : E) : E →L[ℝ] ℝ :=
  if h : x ≠ 0 then minimizerGaugeGradientOn ⟨x,h⟩ else 0

lemma minimizerGaugeGradient_support {x : E} (hx : x ≠ 0) :
    NormalizedSupportAt ratioMinimizingBody (minimizerRadialFoot x)
      (minimizerGaugeGradient x).toLinearMap := by
  simpa [minimizerGaugeGradient,minimizerGaugeGradientOn,hx] using
    minimizerBoundaryNormal_support ⟨minimizerRadialFoot x,minimizerRadialFoot_frontier hx⟩

lemma continuousOn_minimizerGaugeGradient : ContinuousOn minimizerGaugeGradient {x : E | x ≠ 0} := by
  rw [continuousOn_iff_continuous_domRestrict]
  change Continuous (fun x : {x : E // x ≠ 0} => minimizerGaugeGradient x.val)
  have he : (fun x : {x : E // x ≠ 0} => minimizerGaugeGradient x.val)=
      minimizerGaugeGradientOn := by
    funext x
    exact dif_pos x.property
  rw [he]
  exact continuous_minimizerGaugeGradientOn

lemma normalized_support_le_gauge {p : E} {φ : E →ₗ[ℝ] ℝ}
    (hφ : NormalizedSupportAt ratioMinimizingBody p φ) (x : E) :
    φ x ≤ gauge ratioMinimizingBody x := by
  by_cases hx : x=0
  · simp [hx]
  · have hg := disc_gauge_pos ratioMinimizingBody_properties.1 hx
    have hm := frontier_subset_iff_isClosed.2 ratioMinimizingBody_properties.1.2.1.isClosed
      (minimizerRadialFoot_frontier hx)
    have hs := hφ.2 _ hm
    change φ ((gauge ratioMinimizingBody x)⁻¹ • x) ≤ 1 at hs
    rw [map_smul,smul_eq_mul] at hs
    have hm := mul_le_mul_of_nonneg_left hs hg.le
    simpa [← mul_assoc,hg.ne'] using hm

lemma minimizerGaugeGradient_eval {x : E} (hx : x ≠ 0) :
    minimizerGaugeGradient x x=gauge ratioMinimizingBody x := by
  have hs := (minimizerGaugeGradient_support hx).1
  have hg := disc_gauge_pos ratioMinimizingBody_properties.1 hx
  change minimizerGaugeGradient x ((gauge ratioMinimizingBody x)⁻¹ • x)=1 at hs
  rw [map_smul,smul_eq_mul] at hs
  have hm := congrArg (fun t : ℝ => gauge ratioMinimizingBody x*t) hs
  simpa [← mul_assoc,hg.ne'] using hm

lemma minimizerGaugeGradient_affine_support {x : E} (hx : x ≠ 0) (y : E) :
    gauge ratioMinimizingBody x+minimizerGaugeGradient x (y-x) ≤ gauge ratioMinimizingBody y := by
  rw [map_sub,minimizerGaugeGradient_eval hx]
  have hs := normalized_support_le_gauge (minimizerGaugeGradient_support hx) y
  change minimizerGaugeGradient x y ≤ _ at hs
  linarith

theorem hasFDerivAt_minimizerGauge {x : E} (hx : x ≠ 0) :
    HasFDerivAt (gauge ratioMinimizingBody) (minimizerGaugeGradient x) x := by
  have ho : IsOpen {x : E | x ≠ 0} := isClosed_singleton.isOpen_compl
  have hn : {x : E | x ≠ 0} ∈ 𝓝 x := ho.mem_nhds hx
  apply hasFDerivAt_of_continuous_support
    ((continuousOn_minimizerGaugeGradient x hx).continuousAt hn)
    (minimizerGaugeGradient_affine_support hx)
  filter_upwards [hn] with y hy
  exact minimizerGaugeGradient_affine_support hy

theorem contDiffOn_minimizerGauge : ContDiffOn ℝ 1 (gauge ratioMinimizingBody) {x : E | x ≠ 0} := by
  have ho : IsOpen {x : E | x ≠ 0} := isClosed_singleton.isOpen_compl
  rw [show (1 : WithTop ℕ∞)=0+1 by rfl,
    contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn ho.uniqueDiffOn]
  refine ⟨by simp, minimizerGaugeGradient,?_,?_⟩
  · exact contDiffOn_zero.2 continuousOn_minimizerGaugeGradient
  · intro x hx; exact (hasFDerivAt_minimizerGauge hx).hasFDerivWithinAt

/-- Restrict this map to the unit circle to obtain the already constructed
radial boundary parametrization, now with C1 regularity. -/
theorem contDiffOn_minimizerRadialFoot :
    ContDiffOn ℝ 1 minimizerRadialFoot {x : E | x ≠ 0} := by
  exact (contDiffOn_minimizerGauge.inv (fun x hx =>
    (disc_gauge_pos ratioMinimizingBody_properties.1 hx).ne')).smul contDiffOn_id

theorem minimizerRadialFoot_eq_boundary {x : E} (hx : x ∈ Metric.sphere 0 1) :
    minimizerRadialFoot x=discRadialHomeomorph ratioMinimizingBody ratioMinimizingBody_properties.1 x :=
  (discRadialHomeomorph_on_sphere ratioMinimizingBody_properties.1 hx).symm

noncomputable def minimizerRadialVelocity (x v : E) : E :=
  (-(minimizerGaugeGradient x v)/(gauge ratioMinimizingBody x)^2) • x+
    (gauge ratioMinimizingBody x)⁻¹ • v

theorem hasDerivAt_minimizerRadialFoot_comp {γ : ℝ → E} {v : E} {t : ℝ}
    (hγ : HasDerivAt γ v t) (hx : γ t ≠ 0) :
    HasDerivAt (fun s => minimizerRadialFoot (γ s)) (minimizerRadialVelocity (γ t) v) t := by
  have hg := (hasFDerivAt_minimizerGauge hx).comp_hasDerivAt t hγ
  convert! (hg.inv (disc_gauge_pos ratioMinimizingBody_properties.1 hx).ne').smul hγ using 1
  simp [minimizerRadialVelocity,Function.comp_def,add_comm]

theorem minimizerRadialVelocity_det (x v : E) :
    det2 (minimizerRadialFoot x) (minimizerRadialVelocity x v)=
      (gauge ratioMinimizingBody x)⁻¹^2*det2 x v := by
  simp [minimizerRadialFoot,minimizerRadialVelocity,det2]
  ring

/-- Radial projection does not kill any direction transverse to the radius.
In particular its restriction to the unit circle is regular. -/
theorem minimizerRadialVelocity_ne_zero {x v : E} (hx : x ≠ 0) (hv : det2 x v ≠ 0) :
    minimizerRadialVelocity x v ≠ 0 := by
  have hd : det2 (minimizerRadialFoot x) (minimizerRadialVelocity x v) ≠ 0 := by
    rw [minimizerRadialVelocity_det]
    exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero (disc_gauge_pos ratioMinimizingBody_properties.1 hx).ne')) hv
  intro he
  apply hd
  simp [he,det2]

#print axioms hasFDerivAt_of_continuous_support
#print axioms hasFDerivAt_minimizerGauge
#print axioms contDiffOn_minimizerGauge
#print axioms contDiffOn_minimizerRadialFoot
#print axioms minimizerRadialFoot_eq_boundary
#print axioms hasDerivAt_minimizerRadialFoot_comp
#print axioms minimizerRadialVelocity_det
#print axioms minimizerRadialVelocity_ne_zero
end Certificate.Packing
