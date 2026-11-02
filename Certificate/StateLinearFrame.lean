import Certificate.FrameBoundaryCalculus
import Certificate.HexagonLinearTransport

/-! The actual determinant-one frame and its inverse, constructed from state
coordinates. No additional family of area-preserving maps is supplied. -/
namespace Certificate.Packing
open MeasureTheory Set Confinement HVGeometry
set_option maxHeartbeats 0

noncomputable def stateLinear (x : State) : E →ₗ[ℝ] E where
  toFun := stateAction x
  map_add' v w := by ext i; fin_cases i <;> simp [stateAction] <;> ring
  map_smul' c v := by ext i; fin_cases i <;> simp [stateAction] <;> ring

@[simp] lemma stateLinear_apply (x : State) (v : E) : stateLinear x v = stateAction x v := rfl

lemma stateLinear_det (x : State) :
    LinearMap.det (stateLinear x) = x.g11*x.g22-x.g12*x.g21 := by
  rw [det_eq_det2]
  simp [stateLinear,det2,stateAction,point]
  ring

noncomputable def stateFrame (x : State) (hd : x.g11*x.g22-x.g12*x.g21=1) : E ≃ₗ[ℝ] E :=
  (stateLinear x).equivOfDetNeZero (by rw [stateLinear_det,hd]; exact one_ne_zero)

@[simp] lemma stateFrame_apply (x : State) (hd : x.g11*x.g22-x.g12*x.g21=1) (v : E) :
    stateFrame x hd v = stateAction x v := rfl

lemma stateFrame_det (x : State) (hd : x.g11*x.g22-x.g12*x.g21=1) :
    LinearMap.det (stateFrame x hd : E →ₗ[ℝ] E) = 1 := by
  change LinearMap.det (stateLinear x) = 1
  rw [stateLinear_det,hd]

lemma inverse_stateFrame_det (x : State) (hd : x.g11*x.g22-x.g12*x.g21=1) :
    |LinearMap.det ((stateFrame x hd).symm : E →ₗ[ℝ] E)| = 1 := by
  rw [LinearEquiv.det_coe_symm,stateFrame_det,inv_one,abs_one]

lemma inverse_stateFrame_contact {K : Set E} (hclosed : IsClosed K)
    (x : State) (hd : x.g11*x.g22-x.g12*x.g21=1) (v : E)
    (hv : stateAction x v ∈ frontier K) : v ∈ (stateFrame x hd).symm '' K := by
  refine ⟨stateFrame x hd v,hclosed.closure_eq ▸ frontier_subset_closure hv,?_⟩
  exact (stateFrame x hd).symm_apply_apply v

lemma stateAction_sub (x : State) (v w : E) :
    stateAction x (v-w) = stateAction x v-stateAction x w :=
  (stateLinear x).map_sub v w

#print axioms stateFrame_det
#print axioms inverse_stateFrame_contact
end Certificate.Packing
