import Certificate.MinimizerUniformRegularity

/-! Absolute-continuity calculus used for the actual boundary velocities.
All composition bounds hold on the image of the interval; in particular,
reciprocals require a strictly positive denominator throughout that interval. -/
namespace Certificate.Packing
open Set Filter Topology MeasureTheory
open scoped NNReal
set_option maxHeartbeats 0

theorem ac_comp_lipschitzOn {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {f : ℝ → X} {g : X → Y} {a b : ℝ} {s : Set X} {L : ℝ≥0}
    (hf : AbsolutelyContinuousOnInterval f a b) (hg : LipschitzOnWith L g s)
    (hs : MapsTo f (uIcc a b) s) :
    AbsolutelyContinuousOnInterval (fun t => g (f t)) a b := by
  unfold AbsolutelyContinuousOnInterval at hf ⊢
  apply squeeze_zero' ?_ ?_ (by simpa using hf.const_mul (L : ℝ))
  · exact Eventually.of_forall (fun _ => Finset.sum_nonneg (fun _ _ => dist_nonneg))
  rw [eventually_inf_principal]
  filter_upwards with E hE
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun i hi => hg.dist_le_mul _ (hs (hE.1 i hi).1)
    _ (hs (hE.1 i hi).2))

theorem ac_comp_lipschitz {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {f : ℝ → X} {g : X → Y} {a b : ℝ} {L : ℝ≥0}
    (hf : AbsolutelyContinuousOnInterval f a b) (hg : LipschitzWith L g) :
    AbsolutelyContinuousOnInterval (fun t => g (f t)) a b :=
  ac_comp_lipschitzOn hf hg.lipschitzOnWith (fun _ _ => mem_univ _)

theorem ac_reciprocal_pos {f : ℝ → ℝ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) (hp : ∀ t ∈ uIcc a b, 0 < f t) :
    AbsolutelyContinuousOnInterval (fun t => (f t)⁻¹) a b := by
  obtain ⟨t,ht,hmin⟩ := isCompact_uIcc.exists_isMinOn nonempty_uIcc hf.continuousOn
  obtain ⟨C,hC⟩ := hf.exists_bound
  have hft : 0 < f t := hp t ht
  have hc : ContDiffOn ℝ 1 (fun x : ℝ => x⁻¹) (Icc (f t) C) :=
    contDiffOn_id.inv (fun x hx => (hft.trans_le hx.1).ne')
  obtain ⟨L,hL⟩ := hc.exists_lipschitzOnWith (by norm_num) (convex_Icc _ _) isCompact_Icc
  exact ac_comp_lipschitzOn hf hL (fun x hx => ⟨hmin hx,(le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hC x hx)⟩)

theorem ac_plane_coordinate {f : ℝ → E} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) (i : Fin 2) :
    AbsolutelyContinuousOnInterval (fun t => f t i) a b := by
  exact ac_comp_lipschitz hf (coord i).toContinuousLinearMap.lipschitz

theorem ac_plane_det {f g : ℝ → E} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hg : AbsolutelyContinuousOnInterval g a b) :
    AbsolutelyContinuousOnInterval (fun t => det2 (f t) (g t)) a b :=
  ((ac_plane_coordinate hf 0).mul (ac_plane_coordinate hg 1)).sub
    ((ac_plane_coordinate hf 1).mul (ac_plane_coordinate hg 0))

theorem ac_linear_form_eval_const {f : ℝ → E →L[ℝ] ℝ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) (x : E) :
    AbsolutelyContinuousOnInterval (fun t => f t x) a b := by
  let A : (E →L[ℝ] ℝ) →L[ℝ] ℝ := ContinuousLinearMap.apply ℝ ℝ x
  exact ac_comp_lipschitz hf A.lipschitz

theorem ac_linear_form_eval {f : ℝ → E →L[ℝ] ℝ} {g : ℝ → E} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hg : AbsolutelyContinuousOnInterval g a b) :
    AbsolutelyContinuousOnInterval (fun t => f t (g t)) a b := by
  have hh := ((ac_linear_form_eval_const hf (point 1 0)).mul (ac_plane_coordinate hg 0)).add
    ((ac_linear_form_eval_const hf (point 0 1)).mul (ac_plane_coordinate hg 1))
  convert! hh using 1
  funext t
  exact (HexParameters.form_coordinates (f t).toLinearMap (g t)).symm

end Certificate.Packing
