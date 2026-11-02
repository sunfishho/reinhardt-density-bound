import Certificate.CurvatureTrajectory
import Certificate.FrameBoundaryCalculus

/-! A frame path without an assumed curvature sign or controls.
Convexity will provide curvature before constructing the control trajectory. -/
namespace Certificate
open MeasureTheory Set Filter Confinement Packing HVGeometry
set_option maxHeartbeats 0

structure FrameTrajectory where
  state : ℝ → State
  duration : ℝ
  duration_nonneg : 0 ≤ duration
  coordinates_ac : ∀ i, AbsolutelyContinuousOnInterval
    (fun t => (state t).coordinates i) 0 duration
  determinant : ∀ t ∈ Icc 0 duration, (state t).determinantConstraints
  star_nonneg : ∀ t ∈ Icc 0 duration,
    0 ≤ rho0 (state t) ∧ 0 ≤ rho1 (state t) ∧ 0 ≤ rho2 (state t)
  group_ode : ∀ᵐ t ∂volume.restrict (Icc 0 duration), GroupDerivative state t
  initial : state 0=initialState (state 0)
  terminal : state duration=rotateState (state 0)


namespace FrameTrajectory

theorem derivatives_ae (path : FrameTrajectory) :
    ∀ᵐ t ∂volume.restrict (Icc 0 path.duration),
      HasDerivAt (fun s => (path.state s).a) (stateDa path.state t) t ∧
      HasDerivAt (fun s => (path.state s).p) (stateDp path.state t) t ∧
      HasDerivAt (fun s => (path.state s).h) (stateDh path.state t) t := by
  rw [ae_restrict_iff' measurableSet_Icc]
  have ha : AbsolutelyContinuousOnInterval (fun s => (path.state s).a) 0 path.duration := by
    simpa [State.coordinates] using path.coordinates_ac 4
  have hp : AbsolutelyContinuousOnInterval (fun s => (path.state s).p) 0 path.duration := by
    simpa [State.coordinates] using path.coordinates_ac 5
  have hh : AbsolutelyContinuousOnInterval (fun s => (path.state s).h) 0 path.duration := by
    simpa [State.coordinates] using path.coordinates_ac 6
  filter_upwards [ha.ae_differentiableAt,hp.ae_differentiableAt,hh.ae_differentiableAt]
    with t hat hpt hht ht
  have ht' : t ∈ uIcc 0 path.duration := by rwa [uIcc_of_le path.duration_nonneg]
  exact ⟨(hat ht').hasDerivAt,(hpt ht').hasDerivAt,(hht ht').hasDerivAt⟩

theorem group_derivative (path : FrameTrajectory) :
    ∀ t ∈ Ioo 0 path.duration, GroupDerivative path.state t := by
  let x := path.state
  let T := path.duration
  have hT : 0 ≤ T := path.duration_nonneg
  have hac := path.coordinates_ac
  have hode := path.group_ode
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

end FrameTrajectory

/-- Six frame arcs describe the boundary once. No curvature condition is included. -/
structure FrameTrace (path : FrameTrajectory) (K : Set Packing.E) : Prop where
  boundary : ∀ i : Fin 6, ∀ t ∈ Icc 0 path.duration,
    stateAction (path.state t) (root i) ∈ frontier K
  covers : ∀ p ∈ frontier K, ∃ i : Fin 6, ∃ t ∈ Icc 0 path.duration,
    stateAction (path.state t) (root i) = p
  simple : ∀ i j : Fin 6, ∀ s t, s ∈ Ioo 0 path.duration → t ∈ Ioo 0 path.duration →
    stateAction (path.state s) (root i) = stateAction (path.state t) (root j) →
      i = j ∧ s = t

#print axioms FrameTrajectory.derivatives_ae
#print axioms FrameTrajectory.group_derivative
end Certificate
