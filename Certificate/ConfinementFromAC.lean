import Certificate.ConfinementGroupPath

namespace Certificate.Confinement
open MeasureTheory Set
set_option maxHeartbeats 0

/-- Build the regular group path from exactly the absolute-continuity and a.e.
ODE hypotheses used by the certificate integration theorem. -/
noncomputable def RegularPath.ofAC (x : ℝ → State) (T : ℝ) (hT : 0 ≤ T)
    (hac : ∀ i, AbsolutelyContinuousOnInterval (fun t => (x t).coordinates i) 0 T)
    (hode : ∀ᵐ t ∂volume.restrict (Icc 0 T), GroupDerivative x t)
    (hdet : ∀ t ∈ Icc 0 T, (x t).determinantConstraints)
    (hh : ∀ t ∈ Icc 0 T, 0 ≤ (x t).h ∧ (x t).h ≤ 12/5)
    (h0 : x 0=initialState (x 0)) (hEnd : x T=rotateState (x 0))
    (hcost : (∫ t in 0..T, (x t).cost) ≤ 311/100) : RegularPath := by
  have hc : ∀ i, ContinuousOn (fun t => (x t).coordinates i) (Icc 0 T) := by
    intro i
    simpa only [uIcc_of_le hT] using (hac i).continuousOn
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
  exact {
    state := x, duration := T, duration_nonneg := hT,
    c11 := c11, c12 := c12, c21 := c21, c22 := c22, ca := ca, cp := cp, ch := ch,
    ode := fun t ht => ⟨d11 t ht,d12 t ht,d21 t ht,d22 t ht⟩,
    determinant := hdet, height := hh, initial := h0, terminal := hEnd, cost_le := hcost }

theorem group_bounds_of_ac (x : ℝ → State) (T : ℝ) (hT : 0 ≤ T)
    (hac : ∀ i, AbsolutelyContinuousOnInterval (fun t => (x t).coordinates i) 0 T)
    (hode : ∀ᵐ t ∂volume.restrict (Icc 0 T), GroupDerivative x t)
    (hdet : ∀ t ∈ Icc 0 T, (x t).determinantConstraints)
    (hh : ∀ t ∈ Icc 0 T, 0 ≤ (x t).h ∧ (x t).h ≤ 12/5)
    (h0 : x 0=initialState (x 0)) (hEnd : x T=rotateState (x 0))
    (hcost : (∫ t in 0..T, (x t).cost) ≤ 311/100) :
    ∀ t ∈ Icc 0 T, GroupBounds (x t) :=
  (RegularPath.ofAC x T hT hac hode hdet hh h0 hEnd hcost).group_bounds

#print axioms group_bounds_of_ac
end Certificate.Confinement
