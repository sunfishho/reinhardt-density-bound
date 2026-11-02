import Certificate.PackingGeometry
import Certificate.RegularHexagonArea
import Certificate.AreaControlledTrajectory
import Mathlib.Analysis.Calculus.Deriv.Mul

/-! Differentiation of the six frame arcs and their signed area integrands. -/
namespace Certificate.Packing
open MeasureTheory Set Confinement HVGeometry Potential
set_option maxHeartbeats 0

noncomputable def stateTangent (x : State) (v : E) : E :=
  point (x.a*v 0+(x.p-x.h)*v 1) ((x.p+x.h)*v 0-x.a*v 1)

lemma stateAction_hasDerivAt {x : ℝ → State} {t : ℝ} (hd : GroupDerivative x t) (v : E) :
    HasDerivAt (fun s => stateAction (x s) v)
      (stateAction (x t) (stateTangent (x t) v)) t := by
  have h := (((hd.g11.mul_const (v 0)).add (hd.g12.mul_const (v 1))).smul_const
    (point 1 0)).add
    (((hd.g21.mul_const (v 0)).add (hd.g22.mul_const (v 1))).smul_const (point 0 1))
  convert! h using 1
  · ext s i; fin_cases i <;> simp [stateAction,point]
  · ext i; fin_cases i <;> simp [stateAction,stateTangent,point] <;> ring

lemma root_area_integrands (x : State) :
    (fun i => det2 (root i) (stateTangent x (root i))) =
      ![x.p+x.h,x.h-x.p/2-Real.sqrt 3*x.a/2,x.h-x.p/2+Real.sqrt 3*x.a/2,
        x.p+x.h,x.h-x.p/2-Real.sqrt 3*x.a/2,x.h-x.p/2+Real.sqrt 3*x.a/2] := by
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)
  ext i
  fin_cases i <;> dsimp [root,s0,s1,s2,pt,det2,stateTangent,point] <;>
    ring_nf <;> (try simp only [hs]) <;> ring

lemma root_area_integrands_nonneg (x : State)
    (h0 : 0 ≤ rho0 x) (h1 : 0 ≤ rho1 x) (h2 : 0 ≤ rho2 x) :
    ∀ i, 0 ≤ det2 (root i) (stateTangent x (root i)) := by
  have hs : 0 < Real.sqrt (3:ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hs2 := Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)
  have hu := mul_nonneg hs.le h0
  have hv := mul_nonneg hs.le h1
  have hw := mul_nonneg hs.le h2
  dsimp [rho0,rho1,rho2] at hu hv hw
  ring_nf at hu hv hw
  simp only [hs2] at hu hv hw
  intro i
  have he := congrFun (root_area_integrands x) i
  rw [he]
  fin_cases i <;> dsimp <;> linarith

lemma frame_area_integrand_sum (x : State) (hdet : x.g11*x.g22-x.g12*x.g21=1) :
    (1/2:ℝ) * ∑ i : Fin 6, det2 (stateAction x (root i))
      (stateAction x (stateTangent x (root i))) = x.cost := by
  simp_rw [det2_stateAction,hdet,one_mul]
  have he := root_area_integrands x
  simp_rw [congrFun he]
  simp [Fin.sum_univ_succ,State.cost]
  ring

theorem normalized_group_derivative_ae (path : NormalizedTrajectory) :
    ∀ᵐ t ∂volume.restrict (Icc 0 path.duration), GroupDerivative path.state t := by
  filter_upwards [path.matrix_ode] with t ht
  constructor
  · simpa [State.coordinates,coordinateTangent,State.g,State.X,Matrix.mul_apply,
      Fin.sum_univ_two,sub_eq_add_neg] using ht 0
  · simpa [State.coordinates,coordinateTangent,State.g,State.X,Matrix.mul_apply,
      Fin.sum_univ_two,sub_eq_add_neg] using ht 1
  · simpa [State.coordinates,coordinateTangent,State.g,State.X,Matrix.mul_apply,
      Fin.sum_univ_two,sub_eq_add_neg] using ht 2
  · simpa [State.coordinates,coordinateTangent,State.g,State.X,Matrix.mul_apply,
      Fin.sum_univ_two,sub_eq_add_neg] using ht 3

theorem normalized_group_derivative (path : NormalizedTrajectory) :
    ∀ t ∈ Ioo 0 path.duration, GroupDerivative path.state t := by
  let x := path.state
  let T := path.duration
  have hT : 0 ≤ T := path.duration_nonneg
  have hac := path.coordinates_ac
  have hode := normalized_group_derivative_ae path
  have hc : ∀ i, ContinuousOn (fun t => (x t).coordinates i) (Icc 0 T) := by
    intro i
    simpa only [uIcc_of_le path.duration_nonneg] using (hac i).continuousOn
  have c11 : ContinuousOn (fun t => (x t).g11) (Icc 0 T) := by
    simpa [State.coordinates] using hc 0
  have c12 : ContinuousOn (fun t => (x t).g12) (Icc 0 T) := by
    simpa [State.coordinates] using hc 1
  have c21 : ContinuousOn (fun t => (x t).g21) (Icc 0 T) := by
    simpa [State.coordinates] using hc 2
  have c22 : ContinuousOn (fun t => (x t).g22) (Icc 0 T) := by
    simpa [State.coordinates] using hc 3
  have ca : ContinuousOn (fun t => (x t).a) (Icc 0 T) := by
    simpa [State.coordinates] using hc 4
  have cp : ContinuousOn (fun t => (x t).p) (Icc 0 T) := by
    simpa [State.coordinates] using hc 5
  have ch : ContinuousOn (fun t => (x t).h) (Icc 0 T) := by
    simpa [State.coordinates] using hc 6
  have d11 := hasDerivAt_of_ac_continuous_rhs (fun t => (x t).g11)
    (fun t => (x t).g11*(x t).a+(x t).g12*((x t).p+(x t).h)) T hT
    (by simpa [State.coordinates] using hac 0)
    ((c11.mul ca).add (c12.mul (cp.add ch))) (by
      filter_upwards [hode] with t ht using ht.g11)
  have d12 := hasDerivAt_of_ac_continuous_rhs (fun t => (x t).g12)
    (fun t => (x t).g11*((x t).p-(x t).h)-(x t).g12*(x t).a) T hT
    (by simpa [State.coordinates] using hac 1)
    ((c11.mul (cp.sub ch)).sub (c12.mul ca)) (by
      filter_upwards [hode] with t ht using ht.g12)
  have d21 := hasDerivAt_of_ac_continuous_rhs (fun t => (x t).g21)
    (fun t => (x t).g21*(x t).a+(x t).g22*((x t).p+(x t).h)) T hT
    (by simpa [State.coordinates] using hac 2)
    ((c21.mul ca).add (c22.mul (cp.add ch))) (by
      filter_upwards [hode] with t ht using ht.g21)
  have d22 := hasDerivAt_of_ac_continuous_rhs (fun t => (x t).g22)
    (fun t => (x t).g21*((x t).p-(x t).h)-(x t).g22*(x t).a) T hT
    (by simpa [State.coordinates] using hac 3)
    ((c21.mul (cp.sub ch)).sub (c22.mul ca)) (by
      filter_upwards [hode] with t ht using ht.g22)
  exact fun t ht => ⟨d11 t ht,d12 t ht,d21 t ht,d22 t ht⟩

#print axioms stateAction_hasDerivAt
#print axioms frame_area_integrand_sum
#print axioms normalized_group_derivative
end Certificate.Packing
