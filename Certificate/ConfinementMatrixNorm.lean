import Certificate.ConfinementState
import Certificate.ConfinementEnergy

namespace Certificate.Confinement
open MeasureTheory Set
set_option maxHeartbeats 0

noncomputable def energy (x : State) : ℝ := (x.g11-x.g22)^2+(x.g12+x.g21)^2
noncomputable def energyVelocity (x : State) : ℝ :=
  2*(x.g11-x.g22)*(x.a*(x.g11+x.g22)+x.p*(x.g12-x.g21))+
  2*(x.g12+x.g21)*(x.p*(x.g11+x.g22)-x.a*(x.g12-x.g21))

theorem energy_nonneg (x : State) : 0 ≤ energy x := by unfold energy; positivity

theorem energy_eq (x : State) (hd : x.g11*x.g22-x.g12*x.g21=1) :
    energy x = x.g11^2+x.g12^2+x.g21^2+x.g22^2-2 := by
  unfold energy
  nlinarith only [hd]

theorem energy_complement (x : State) (hd : x.g11*x.g22-x.g12*x.g21=1) :
    (x.g11+x.g22)^2+(x.g12-x.g21)^2=energy x+4 := by
  unfold energy
  nlinarith only [hd]

theorem energy_velocity_bound (x : State) (hd : x.determinantConstraints)
    (hh : 0 ≤ x.h) (hu : x.h ≤ 12/5) :
    (energyVelocity x)^2 ≤ (121/36)*x.h^2*energy x*(energy x+4) := by
  have he := energy_nonneg x
  have heq := energy_complement x hd.1
  have hid : 4*energy x*(x.a^2+x.p^2)*
      ((x.g11+x.g22)^2+(x.g12-x.g21)^2)-(energyVelocity x)^2 =
      4*(((x.g11-x.g22)*x.a+(x.g12+x.g21)*x.p)*(x.g12-x.g21)-
        ((x.g11-x.g22)*x.p-(x.g12+x.g21)*x.a)*(x.g11+x.g22))^2 := by
    unfold energy energyVelocity
    ring
  rw [heq] at hid
  have hfirst : (energyVelocity x)^2 ≤ 4*energy x*(x.a^2+x.p^2)*(energy x+4) := by
    nlinarith only [hid,sq_nonneg (((x.g11-x.g22)*x.a+(x.g12+x.g21)*x.p)*(x.g12-x.g21)-
        ((x.g11-x.g22)*x.p-(x.g12+x.g21)*x.a)*(x.g11+x.g22))]
  have hq : x.a^2+x.p^2 ≤ (121/144)*x.h^2 := by
    have := mul_nonneg hh (sub_nonneg.mpr hu)
    nlinarith only [hd.2,this,hu,hh]
  have hhq := mul_le_mul_of_nonneg_left hq (show 0 ≤ 4*energy x*(energy x+4) by positivity)
  nlinarith only [hfirst,hhq]

theorem energy_hasDerivAt (x : ℝ → State) (t : ℝ)
    (h11 : HasDerivAt (fun s => (x s).g11) ((x t).g11*(x t).a+(x t).g12*((x t).p+(x t).h)) t)
    (h12 : HasDerivAt (fun s => (x s).g12) ((x t).g11*((x t).p-(x t).h)-(x t).g12*(x t).a) t)
    (h21 : HasDerivAt (fun s => (x s).g21) ((x t).g21*(x t).a+(x t).g22*((x t).p+(x t).h)) t)
    (h22 : HasDerivAt (fun s => (x s).g22) ((x t).g21*((x t).p-(x t).h)-(x t).g22*(x t).a) t) :
    HasDerivAt (fun s => energy (x s)) (energyVelocity (x t)) t := by
  unfold energy energyVelocity
  convert! ((h11.sub h22).pow 2).add ((h12.add h21).pow 2) using 1 <;>
    (try simp only [Pi.add_apply,Pi.sub_apply]) <;> ring

/-- The norm confinement follows from the matrix equation and both orthogonal
endpoints whenever cost is at most 3.11. This rational threshold exceeds gamma. -/
theorem matrix_norm_bound (x : ℝ → State) (T : ℝ) (hT : 0 ≤ T)
    (h11 : ContinuousOn (fun t => (x t).g11) (Icc 0 T))
    (h12 : ContinuousOn (fun t => (x t).g12) (Icc 0 T))
    (h21 : ContinuousOn (fun t => (x t).g21) (Icc 0 T))
    (h22 : ContinuousOn (fun t => (x t).g22) (Icc 0 T))
    (hh : ContinuousOn (fun t => (x t).h) (Icc 0 T))
    (hderiv : ∀ t ∈ Ioo 0 T, HasDerivAt (fun s => energy (x s)) (energyVelocity (x t)) t)
    (hdet : ∀ t ∈ Icc 0 T, (x t).determinantConstraints)
    (hheight : ∀ t ∈ Icc 0 T, 0 ≤ (x t).h ∧ (x t).h ≤ 12/5)
    (h0 : energy (x 0)=0) (hEnd : energy (x T)=0)
    (hcost : (∫ t in 0..T, (x t).cost) ≤ 311/100) :
    ∀ t ∈ Icc 0 T, (x t).g11^2+(x t).g12^2+(x t).g21^2+(x t).g22^2 ≤ 16/5 := by
  have hE := energy_bound (fun t => energy (x t)) (fun t => energyVelocity (x t))
    (fun t => (x t).h) T hT
    (((h11.sub h22).pow 2).add ((h12.add h21).pow 2)) hh
    (fun t _ => energy_nonneg (x t)) (fun t ht => (hheight t ht).1) hderiv
    (fun t ht => energy_velocity_bound (x t) (hdet t ⟨ht.1.le,ht.2.le⟩)
      (hheight t ⟨ht.1.le,ht.2.le⟩).1 (hheight t ⟨ht.1.le,ht.2.le⟩).2)
    h0 hEnd (by
      simp only [State.cost,intervalIntegral.integral_const_mul] at hcost
      linarith)
  intro t ht
  have he := energy_eq (x t) (hdet t ht).1
  linarith [hE t ht]

#print axioms matrix_norm_bound
end Certificate.Confinement
