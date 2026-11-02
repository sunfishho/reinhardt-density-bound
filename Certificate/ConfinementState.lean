import Certificate.ConfinementRho
import Certificate.PrimitiveData

namespace Certificate.Confinement
open Sparse
set_option maxHeartbeats 0

theorem sqrt_mul_rho (x : State) :
    Real.sqrt 3 * rho0 x = x.p+x.h+Real.sqrt 3*x.a ∧
    Real.sqrt 3 * rho1 x = x.p+x.h-Real.sqrt 3*x.a ∧
    Real.sqrt 3 * rho2 x = x.h-2*x.p := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  unfold rho0 rho1 rho2
  constructor
  · ring_nf; simp only [hs]; ring
  constructor <;> (ring_nf; simp only [hs]; ring)

theorem scaled_pair_bounds (x : State) (hx : HVCompact x) :
    2/9 ≤ x.p+x.h ∧
    4/9 ≤ 2*x.h-x.p+Real.sqrt 3*x.a ∧
    4/9 ≤ 2*x.h-x.p-Real.sqrt 3*x.a := by
  obtain ⟨h0,h1,h2,h01,h02,h12⟩ := hx
  obtain ⟨e0,e1,e2⟩ := sqrt_mul_rho x
  have hs : Real.sqrt (3:ℝ) * (4*Real.sqrt 3/27) = 4/9 := by
    have hs := Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)
    nlinarith only [hs]
  have h01' := mul_le_mul_of_nonneg_left h01 (Real.sqrt_nonneg 3)
  have h02' := mul_le_mul_of_nonneg_left h02 (Real.sqrt_nonneg 3)
  have h12' := mul_le_mul_of_nonneg_left h12 (Real.sqrt_nonneg 3)
  rw [hs,mul_add,e0,e1] at h01'
  rw [hs,mul_add,e0,e2] at h02'
  rw [hs,mul_add,e1,e2] at h12'
  exact ⟨by linarith,by linarith,by linarith⟩

/-- All twelve X-dependent polynomial inequalities follow from the six
published compact-domain inequalities and determinant one. -/
structure StateBounds (x : State) : Prop where
  denominator0 : 0 ≤ -2307-40000*x.p+20000*x.h
  denominator1 : 0 ≤ -2307+20000*x.p+20000*x.h-20000*x.a*Real.sqrt 3
  denominator2 : 0 ≤ -2307+20000*x.p+20000*x.h+20000*x.a*Real.sqrt 3
  hLower : 0 ≤ x.h-1
  hUpper : 0 ≤ 12-5*x.h
  xNorm : 0 ≤ 119-25*x.a^2-25*x.p^2
  horoballY : 0 ≤ 9*(x.p+x.h)-2
  horoballPlus : 0 ≤ 27+27*x.a^2-8*(x.p+x.h)+9*(x.p+x.h)^2-
    18*x.a*(x.p+x.h)*Real.sqrt 3
  horoballMinus : 0 ≤ 27+27*x.a^2-8*(x.p+x.h)+9*(x.p+x.h)^2+
    18*x.a*(x.p+x.h)*Real.sqrt 3
  halfplane0 : 0 ≤ -1-15*x.a+5*Real.sqrt 3*(x.p+x.h)
  halfplane1 : 0 ≤ -1-10*Real.sqrt 3*x.p+5*Real.sqrt 3*x.h
  halfplane2 : 0 ≤ -1+15*x.a+5*Real.sqrt 3*(x.p+x.h)

theorem state_bounds (x : State) (hd : x.h^2-x.a^2-x.p^2=1) (hx : HVCompact x) :
    StateBounds x := by
  obtain ⟨hlo,hhi⟩ := height_bounds x hd hx
  obtain ⟨hp,hplus,hminus⟩ := scaled_pair_bounds x hx
  obtain ⟨e0,e1,e2⟩ := sqrt_mul_rho x
  obtain ⟨h0,h1,h2,h01,h02,h12⟩ := hx
  have hslo := sqrt_three_bounds.1
  have s0 := mul_le_mul_of_nonneg_left h0 (Real.sqrt_nonneg 3)
  have s1 := mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg 3)
  have s2 := mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg 3)
  rw [e0] at s0
  rw [e1] at s1
  rw [e2] at s2
  have hc : 0 ≤ x.p+x.h := by linarith
  have hbplus := mul_nonneg hc (sub_nonneg.mpr hminus)
  have hbminus := mul_nonneg hc (sub_nonneg.mpr hplus)
  have hnorm := xNorm_constraint x hd (by linarith) hhi
  dsimp [rho0] at h0
  dsimp [rho1] at h1
  dsimp [rho2] at h2
  constructor
  · nlinarith only [s2,hslo]
  · nlinarith only [s1,hslo]
  · nlinarith only [s0,hslo]
  · linarith
  · linarith
  · nlinarith only [hnorm]
  · linarith
  · nlinarith only [hd,hbplus]
  · nlinarith only [hd,hbminus]
  · nlinarith only [h1]
  · nlinarith only [h2]
  · nlinarith only [h0]

/-- The seven remaining constraints concern g and must be established from
the matrix path, rather than inferred from compactness of X. -/
structure GroupBounds (x : State) : Prop where
  sector1 : 0 ≤ x.g21
  sector2 : 0 ≤ -x.g21+Real.sqrt 3*x.g22
  sector1Rot1 : 0 ≤ -3*x.g12+x.g21+Real.sqrt 3*x.g11-Real.sqrt 3*x.g22
  sector2Rot1 : 0 ≤ 3*x.g12+x.g21+Real.sqrt 3*x.g11+Real.sqrt 3*x.g22
  sector1Rot2 : 0 ≤ -3*x.g12+x.g21-Real.sqrt 3*x.g11+Real.sqrt 3*x.g22
  sector2Rot2 : 0 ≤ -x.g21+Real.sqrt 3*x.g11
  gNorm : x.g11^2+x.g12^2+x.g21^2+x.g22^2 ≤ 16/5

theorem region_of_bounds (x : State) (hg : GroupBounds x) (hs : StateBounds x) :
    PrimitiveData.Region x.coordinates := by
  obtain ⟨g1,g2,g3,g4,g5,g6,gn⟩ := hg
  obtain ⟨d0,d1,d2,hl,hu,xn,hy,hp,hm,p0,p1,p2⟩ := hs
  intro label
  cases label <;>
    norm_num [PrimitiveData.polynomial, PrimitiveData.sector1, PrimitiveData.sector2,
      PrimitiveData.sector1Rot1, PrimitiveData.sector2Rot1,
      PrimitiveData.sector1Rot2, PrimitiveData.sector2Rot2, PrimitiveData.gNorm,
      PrimitiveData.denominator0, PrimitiveData.denominator1, PrimitiveData.denominator2,
      PrimitiveData.hLower, PrimitiveData.hUpper, PrimitiveData.xNorm,
      PrimitiveData.horoballY, PrimitiveData.horoballPlus, PrimitiveData.horoballMinus,
      PrimitiveData.halfplane0, PrimitiveData.halfplane1, PrimitiveData.halfplane2,
      State.coordinates, eval, Exponent.eval, Matrix.cons_val] <;>
    simp only [Matrix.cons_val] <;> norm_num <;> nlinarith

theorem region_of_hvCompact (x : State) (hd : x.h^2-x.a^2-x.p^2=1)
    (hx : HVCompact x) (hg : GroupBounds x) : PrimitiveData.Region x.coordinates :=
  region_of_bounds x hg (state_bounds x hd hx)

#print axioms state_bounds
#print axioms region_of_hvCompact
end Certificate.Confinement
