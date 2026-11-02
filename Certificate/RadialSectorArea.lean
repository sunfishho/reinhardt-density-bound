import Certificate.HexagonLinearTransport
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Analysis.Convex.Gauge
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Actual Lebesgue area of a radial sector of a convex boundary arc.
The area formula is proved by the Jacobian change-of-variables theorem.
No boundary-integral or area identity is assumed. -/
namespace Certificate.Packing
open MeasureTheory Set
set_option maxHeartbeats 0

noncomputable def planeCoordinates : E ≃ᵐ ℝ × ℝ :=
  (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm.trans MeasurableEquiv.finTwoArrow

lemma planeCoordinates_apply (x : E) : planeCoordinates x = (x 0,x 1) := rfl

lemma planeCoordinates_preserving : MeasurePreserving planeCoordinates :=
  (volume_preserving_finTwoArrow ℝ).comp (PiLp.volume_preserving_ofLp (Fin 2))

def radialDomain (a b : ℝ) : Set E :=
  {x | x 0 ∈ Ioo 0 1 ∧ x 1 ∈ Ioo a b}

lemma mem_radialDomain (a b : ℝ) (x : E) :
    x ∈ radialDomain a b ↔ x 0 ∈ Ioo 0 1 ∧ x 1 ∈ Ioo a b := Iff.rfl

lemma measurableSet_radialDomain (a b : ℝ) : MeasurableSet (radialDomain a b) :=
  planeCoordinates.measurable (measurableSet_Ioo.prod measurableSet_Ioo)

noncomputable def radialMap (γ : ℝ → E) (x : E) : E := x 0 • γ (x 1)

noncomputable def radialDerivative (γ γ' : ℝ → E) (x : E) : E →L[ℝ] E :=
  (coord 0).toContinuousLinearMap.smulRight (γ (x 1)) +
    (coord 1).toContinuousLinearMap.smulRight (x 0 • γ' (x 1))

lemma radialMap_hasFDerivAt {γ γ' : ℝ → E} {x : E}
    (hγ : HasDerivAt γ (γ' (x 1)) (x 1)) :
    HasFDerivAt (radialMap γ) (radialDerivative γ γ' x) x := by
  have h1 : HasFDerivAt (fun y : E => y 1) (coord 1).toContinuousLinearMap x := by
    convert (coord 1).toContinuousLinearMap.hasFDerivAt (x:=x) using 1
    ext y
    simp [coord_eval]
  have h0 : HasFDerivAt (fun y : E => y 0) (coord 0).toContinuousLinearMap x := by
    convert (coord 0).toContinuousLinearMap.hasFDerivAt (x:=x) using 1
    ext y
    simp [coord_eval]
  have h := h0.smul (hγ.hasFDerivAt.comp x h1)
  convert! h using 1
  ext v i
  simp [radialDerivative,coord_eval]
  ring

lemma det_radialDerivative (γ γ' : ℝ → E) (x : E) :
    (radialDerivative γ γ' x).det = x 0 * det2 (γ (x 1)) (γ' (x 1)) := by
  change LinearMap.det (radialDerivative γ γ' x).toLinearMap = _
  rw [det_eq_det2]
  simp [radialDerivative,point,det2,coord_eval]
  ring

/-- Boundary points on the same positive ray have the same radial coordinate.
This proves injectivity of the sector map from ordinary boundary membership. -/
lemma radialMap_injOn {K : Set E} (hc : Convex ℝ K) (h0 : K ∈ nhds (0:E))
    {γ : ℝ → E} {a b : ℝ} (hb : ∀ t ∈ Ioo a b, γ t ∈ frontier K)
    (hi : InjOn γ (Ioo a b)) : InjOn (radialMap γ) (radialDomain a b) := by
  intro x hx y hy he
  have hgx := (gauge_eq_one_iff_mem_frontier hc h0).2 (hb _ hx.2)
  have hgy := (gauge_eq_one_iff_mem_frontier hc h0).2 (hb _ hy.2)
  have hr := congrArg (gauge K) he
  simp only [radialMap,gauge_smul_of_nonneg hx.1.1.le,
    gauge_smul_of_nonneg hy.1.1.le,hgx,hgy,smul_eq_mul,mul_one] at hr
  have ht : x 1 = y 1 := hi hx.2 hy.2 (by
    unfold radialMap at he
    rw [hr] at he
    exact (smul_right_injective E hy.1.1.ne') he)
  ext i; fin_cases i <;> assumption

def radialSector (γ : ℝ → E) (a b : ℝ) : Set E := radialMap γ '' radialDomain a b

/-- Polar-sector area for any differentiable, injective convex-boundary arc.
The absolute value permits either orientation. -/
theorem radialSector_area {K : Set E} (hc : Convex ℝ K) (h0 : K ∈ nhds (0:E))
    {γ γ' : ℝ → E} {a b : ℝ}
    (hb : ∀ t ∈ Ioo a b, γ t ∈ frontier K) (hi : InjOn γ (Ioo a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivAt γ (γ' t) t) :
    (volume (radialSector γ a b)).toReal =
      (1/2:ℝ) * ∫ t in Ioo a b, |det2 (γ t) (γ' t)| := by
  have hj := integral_image_eq_integral_abs_det_fderiv_smul volume
    (measurableSet_radialDomain a b)
    (fun x hx => (radialMap_hasFDerivAt (hd _ hx.2)).hasFDerivWithinAt)
    (radialMap_injOn hc h0 hb hi) (fun _ : E => (1:ℝ))
  simp only [integral_const,measureReal_restrict_apply_univ,smul_eq_mul,mul_one,
    det_radialDerivative,abs_mul] at hj
  change (volume (radialSector γ a b)).toReal = _ at hj
  rw [hj]
  have he := planeCoordinates_preserving.setIntegral_preimage_emb
    planeCoordinates.measurableEmbedding
    (fun z : ℝ × ℝ => |z.1| * |det2 (γ z.2) (γ' z.2)|) (Ioo 0 1 ×ˢ Ioo a b)
  change (∫ x in radialDomain a b, |x 0| * |det2 (γ (x 1)) (γ' (x 1))|) = _ at he
  rw [he]
  change (∫ y in Ioo 0 1 ×ˢ Ioo a b,
    |y.1| * |det2 (γ y.2) (γ' y.2)| ∂volume.prod volume) = _
  rw [setIntegral_prod_mul (μ:=volume) (ν:=volume) (fun r : ℝ => |r|)
    (fun t : ℝ => |det2 (γ t) (γ' t)|) (Ioo 0 1) (Ioo a b)]
  have hh : (∫ r in Ioo (0:ℝ) 1, |r|) = 1/2 := by
    calc
      _ = ∫ r in Ioo (0:ℝ) 1, r := setIntegral_congr_fun measurableSet_Ioo
        (fun r hr => abs_of_pos hr.1)
      _ = ∫ r in (0:ℝ)..1, r := by
        rw [intervalIntegral.integral_of_le (by norm_num)]
        exact integral_Ioc_eq_integral_Ioo.symm
      _ = 1/2 := by rw [integral_id]; norm_num
  rw [hh]

#print axioms radialSector_area
end Certificate.Packing
