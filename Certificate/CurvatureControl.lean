import Certificate.GeometricCoordinates
import Mathlib.Tactic

/-! Pointwise reconstruction of simplex controls from boundary curvature.
The three directions are 0, 120, and 60 degrees, in that order; this agrees
with the existing control vertex convention. This is an algebraic part of
the published geometric/control reduction, not an assumption about an ODE. -/
namespace Certificate.Curvature
open scoped BigOperators
set_option maxHeartbeats 0
abbrev Mat := Matrix (Fin 2) (Fin 2) ℝ

noncomputable def direction (k : Fin 3) : Fin 2 → ℝ :=
  ![![1,0], ![-1/2,Real.sqrt 3/2], ![1/2,Real.sqrt 3/2]] k

noncomputable def detPair (v w : Fin 2 → ℝ) : ℝ := v 0*w 1-v 1*w 0

noncomputable def form (Y : Mat) (k : Fin 3) : ℝ :=
  detPair (direction k) (Y.mulVec (direction k))

noncomputable def total (Y : Mat) : ℝ := ∑ k, form Y k

theorem form_values (Y : Mat) :
    form Y = ![Y 1 0,
      Y 1 0/4 - 3*Y 0 1/4 + Real.sqrt 3*(Y 0 0-Y 1 1)/4,
      Y 1 0/4 - 3*Y 0 1/4 - Real.sqrt 3*(Y 0 0-Y 1 1)/4] := by
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)
  ext k
  fin_cases k <;> norm_num [form,detPair,direction,Matrix.mulVec,
      dotProduct,Matrix.vecHead,Matrix.vecTail,Fin.sum_univ_two]
    <;> ring_nf <;> simp only [hs] <;> ring

@[simp] theorem form_zero (Y : Mat) : form Y 0=Y 1 0 := congrFun (form_values Y) 0
@[simp] theorem form_one (Y : Mat) :
    form Y 1=Y 1 0/4-3*Y 0 1/4+Real.sqrt 3*(Y 0 0-Y 1 1)/4 := congrFun (form_values Y) 1
@[simp] theorem form_two (Y : Mat) :
    form Y 2=Y 1 0/4-3*Y 0 1/4-Real.sqrt 3*(Y 0 0-Y 1 1)/4 := congrFun (form_values Y) 2

theorem total_eq (Y : Mat) : total Y=3/2*(Y 1 0-Y 0 1) := by
  rw [total,Fin.sum_univ_three,form_zero,form_one,form_two]
  ring

theorem total_pos (Y : Mat) (htrace : Matrix.trace Y=0) (hne : Y ≠ 0)
    (hn : ∀ k, 0 ≤ form Y k) : 0 < total Y := by
  have ht : 0 ≤ total Y := Finset.sum_nonneg (fun k _ => hn k)
  by_contra hp
  have hz : total Y=0 := by linarith
  have hall : ∀ k, form Y k=0 := by
    intro k
    have hle : form Y k ≤ total Y :=
      Finset.single_le_sum (fun i _ => hn i) (Finset.mem_univ k)
    linarith [hn k]
  have h0 := hall 0
  have h1 := hall 1
  have h2 := hall 2
  rw [form_zero] at h0
  rw [form_one] at h1
  rw [form_two] at h2
  have hs : 0 < Real.sqrt (3:ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hd : Y 0 0-Y 1 1=0 := by nlinarith only [h1,h2,hs]
  have htr : Y 0 0+Y 1 1=0 := by simpa [Matrix.trace,Fin.sum_univ_two] using htrace
  apply hne
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num <;> linarith

noncomputable def controls (Y : Mat) : Fin 3 → ℝ := fun k => form Y k / total Y

theorem controls_nonneg (Y : Mat) (ht : 0 < total Y) (hn : ∀ k, 0 ≤ form Y k) :
    ∀ k, 0 ≤ controls Y k := fun k => div_nonneg (hn k) ht.le

theorem controls_sum (Y : Mat) (ht : 0 < total Y) : ∑ k, controls Y k=1 := by
  simp only [controls,← Finset.sum_div]
  exact div_self ht.ne'

theorem controls_matrix (Y : Mat) (htrace : Matrix.trace Y=0) (ht : 0 < total Y) :
    Z (controls Y) = (total Y)⁻¹ • Y := by
  have htr : Y 0 0+Y 1 1=0 := by simpa [Matrix.trace,Fin.sum_univ_two] using htrace
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)
  have htne := ht.ne'
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Z,controls,Matrix.vecHead,Matrix.vecTail,Matrix.smul_apply,smul_eq_mul] <;>
    field_simp <;> ring_nf <;> simp only [hs] <;> nlinarith only [htr]

noncomputable def tangent (da dp dh : ℝ) : Mat := !![da,dp-dh;dp+dh,-da]

noncomputable def curvatureMatrix (x : State) (da dp dh : ℝ) : Mat :=
  -(x.X*(tangent da dp dh-1))

theorem curvatureMatrix_trace (x : State) (da dp dh : ℝ)
    (ht : x.h*dh-x.a*da-x.p*dp=0) :
    Matrix.trace (curvatureMatrix x da dp dh)=0 := by
  simp [curvatureMatrix,State.X,tangent,Matrix.trace,Matrix.vecMul,dotProduct,Fin.sum_univ_two]
  nlinarith only [ht]

theorem X_mul_curvatureMatrix (x : State) (da dp dh : ℝ)
    (hd : x.h^2-x.a^2-x.p^2=1) :
    x.X*curvatureMatrix x da dp dh=tangent da dp dh-1 := by
  rw [curvatureMatrix,mul_neg,← mul_assoc,x.X_sq hd]
  simp

theorem curvatureMatrix_ne_zero (x : State) (da dp dh : ℝ)
    (hd : x.h^2-x.a^2-x.p^2=1) : curvatureMatrix x da dp dh ≠ 0 := by
  intro hz
  have hh := X_mul_curvatureMatrix x da dp dh hd
  rw [hz,mul_zero] at hh
  have htr := congrArg Matrix.trace hh
  simp [tangent,Matrix.trace,Fin.sum_univ_two] at htr

/-- The form being normalized is exactly det(sigma', sigma'') in the
area-preserving frame, using g'=gX and X^2=-I. -/
theorem boundary_curvature_eq (x : State) (da dp dh : ℝ) (k : Fin 3) :
    detPair (x.X.mulVec (direction k))
      ((tangent da dp dh-1).mulVec (direction k)) =
      form (curvatureMatrix x da dp dh) k := by
  simp [form,detPair,curvatureMatrix,State.X,tangent,Matrix.mulVec,Matrix.vecMul,dotProduct,Fin.sum_univ_two]
  ring

/-- Nonnegative curvature and the determinant tangent identity produce the
actual simplex controls and the exact rational matrix ODE. -/
theorem controls_of_nonnegative_curvature (x : State) (da dp dh : ℝ)
    (hd : x.h^2-x.a^2-x.p^2=1) (ht : x.h*dh-x.a*da-x.p*dp=0)
    (hc : ∀ k, 0 ≤ detPair (x.X.mulVec (direction k))
      ((tangent da dp dh-1).mulVec (direction k))) :
    ∃ u : Fin 3 → ℝ, (∀ k, 0 ≤ u k) ∧ (∑ k, u k=1) ∧
      0 < denominatorAt x u ∧ controlField x u=tangent da dp dh := by
  let Y := curvatureMatrix x da dp dh
  have htrace : Matrix.trace Y=0 := curvatureMatrix_trace x da dp dh ht
  have hn : ∀ k, 0 ≤ form Y k := by intro k; simpa only [boundary_curvature_eq] using hc k
  have hpos : 0 < total Y := total_pos Y htrace (curvatureMatrix_ne_zero x da dp dh hd) hn
  have hmatrix := controls_matrix Y htrace hpos
  have hxy : x.X*Y=tangent da dp dh-1 := X_mul_curvatureMatrix x da dp dh hd
  have hden : denominatorAt x (controls Y)=2/total Y := by
    simp only [denominatorAt,hmatrix,Matrix.mul_smul,Matrix.trace_smul,hxy,smul_eq_mul]
    simp [tangent,Matrix.trace,Fin.sum_univ_two,div_eq_mul_inv]
    ring
  refine ⟨controls Y,controls_nonneg Y hpos hn,controls_sum Y hpos,?_,?_⟩
  · rw [hden]; positivity
  · rw [controlField,hden,hmatrix,Matrix.mul_smul,hxy,smul_smul]
    have hs : (2/(2/total Y))*(total Y)⁻¹=1 := by field_simp
    rw [hs,one_smul]
    abel

#print axioms controls_of_nonnegative_curvature
end Certificate.Curvature
