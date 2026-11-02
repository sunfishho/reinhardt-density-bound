import Certificate.FrameBoundaryCalculus
import Certificate.HVCornerCoordinates

/-! The supporting-strip forms of the normalized hexagon are precisely the
normal forms of the three boundary tangents. -/
namespace Certificate.Packing
open MeasureTheory Set Confinement HVGeometry
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false

lemma positive_pair_sum {u v w : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v)
    (he : u*v+v*w+w*u=1) : 0 < u+v := by
  by_contra h
  have hu0 : u=0 := by linarith
  have hv0 : v=0 := by linarith
  simp [hu0,hv0] at he

lemma root_area_integrands_pos_of_normalized (x : State)
    (hdet : x.h^2-x.a^2-x.p^2=1)
    (h0 : 0 ≤ rho0 x) (h1 : 0 ≤ rho1 x) (h2 : 0 ≤ rho2 x) :
    ∀ i, 0 < det2 (root i) (stateTangent x (root i)) := by
  have he := rho_e2 x hdet
  have h01 := positive_pair_sum h0 h1 he
  have h12 := positive_pair_sum (w:=rho0 x) h1 h2 (by nlinarith only [he])
  have h02 := positive_pair_sum (w:=rho1 x) h0 h2 (by nlinarith only [he])
  have hs : 0 < Real.sqrt (3:ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hs2 := Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)
  have hu := mul_pos hs h01
  have hv := mul_pos hs h12
  have hw := mul_pos hs h02
  dsimp [rho0,rho1,rho2] at hu hv hw
  ring_nf at hu hv hw
  simp only [hs2] at hu hv hw
  intro i
  rw [congrFun (root_area_integrands x) i]
  fin_cases i <;> dsimp <;> linarith

lemma stateTangent_det (x : State) (v w : E) :
    det2 (stateTangent x v) (stateTangent x w) =
      (x.h^2-x.a^2-x.p^2)*det2 v w := by
  simp [det2,stateTangent,point]
  ring

lemma adjacent_tangent_contacts (x : State) :
    det2 (stateTangent x s0) (s1-s0) = Real.sqrt 3/2*rho0 x ∧
    det2 (stateTangent x s1) (s2-s1) = Real.sqrt 3/2*rho1 x ∧
    det2 (stateTangent x s2) (-s0-s2) = Real.sqrt 3/2*rho2 x := by
  have hs2 := Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)
  refine ⟨?_,?_,?_⟩ <;>
    dsimp [det2,stateTangent,s0,s1,s2,pt,point,rho0,rho1,rho2] <;>
    ring_nf <;> simp only [hs2] <;> ring

lemma root_area_integrands_pos (x : State)
    (h0 : 0 < rho0 x) (h1 : 0 < rho1 x) (h2 : 0 < rho2 x) :
    ∀ i, 0 < det2 (root i) (stateTangent x (root i)) := by
  have hs : 0 < Real.sqrt (3:ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hs2 := Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)
  have hu := mul_pos hs h0
  have hv := mul_pos hs h1
  have hw := mul_pos hs h2
  dsimp [rho0,rho1,rho2] at hu hv hw
  ring_nf at hu hv hw
  simp only [hs2] at hu hv hw
  intro i
  rw [congrFun (root_area_integrands x) i]
  fin_cases i <;> dsimp <;> linarith

theorem tangent_side_identities (x : State) (z : E)
    (h0 : 0 < rho0 x) (h1 : 0 < rho1 x) (h2 : 0 < rho2 x) :
    (Real.sqrt 3*(rho1 x+rho2 x)) *
        (1-sideA (rho0 x) (rho1 x) (rho2 x) z) = 2*det2 (stateTangent x s1) (z-s1) ∧
    (Real.sqrt 3*(rho0 x+rho2 x)) *
        (1-sideB (rho0 x) (rho1 x) (rho2 x) z) = 2*det2 (stateTangent x s2) (z-s2) ∧
    (Real.sqrt 3*(rho0 x+rho1 x)) *
        (1+sideC (rho0 x) (rho1 x) (rho2 x) z) = 2*det2 (stateTangent x s0) (z-s0) := by
  have hs : Real.sqrt (3:ℝ) ≠ 0 := (Real.sqrt_pos.2 (by norm_num)).ne'
  have hs2 := Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)
  have h01 : rho0 x+rho1 x ≠ 0 := (add_pos h0 h1).ne'
  have h02 : rho0 x+rho2 x ≠ 0 := (add_pos h0 h2).ne'
  have h12 : rho1 x+rho2 x ≠ 0 := (add_pos h1 h2).ne'
  refine ⟨?_,?_,?_⟩ <;>
    simp only [sideA,sideB,sideC,LinearMap.add_apply,LinearMap.smul_apply,
      LinearMap.neg_apply,coord_eval,smul_eq_mul] <;>
    field_simp <;>
    dsimp [rho0,rho1,rho2,det2,stateTangent,s0,s1,s2,pt,point] <;>
    ring_nf <;> simp only [hs2] <;> ring

/-- Three supporting tangents and central symmetry imply all six side
inequalities of the explicitly constructed hexagon. -/
theorem inHexagon_of_tangent_support {K : Set E} (hsym : IsSymmetricSet K)
    (x : State) (h0 : 0 < rho0 x) (h1 : 0 < rho1 x) (h2 : 0 < rho2 x)
    (hs0 : ∀ z ∈ K, 0 ≤ det2 (stateTangent x s0) (z-s0))
    (hs1 : ∀ z ∈ K, 0 ≤ det2 (stateTangent x s1) (z-s1))
    (hs2 : ∀ z ∈ K, 0 ≤ det2 (stateTangent x s2) (z-s2)) :
    ∀ z ∈ K, |sideA (rho0 x) (rho1 x) (rho2 x) z| ≤ 1 ∧
      |sideB (rho0 x) (rho1 x) (rho2 x) z| ≤ 1 ∧
      |sideC (rho0 x) (rho1 x) (rho2 x) z| ≤ 1 := by
  have hsq : 0 < Real.sqrt (3:ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hupper : ∀ z ∈ K, sideA (rho0 x) (rho1 x) (rho2 x) z ≤ 1 ∧
      sideB (rho0 x) (rho1 x) (rho2 x) z ≤ 1 ∧
      -1 ≤ sideC (rho0 x) (rho1 x) (rho2 x) z := by
    intro z hz
    obtain ⟨he0,he1,he2⟩ := tangent_side_identities x z h0 h1 h2
    have ha := nonneg_of_mul_nonneg_right (he0.symm ▸ mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (hs1 z hz))
      (mul_pos hsq (add_pos h1 h2))
    have hb := nonneg_of_mul_nonneg_right (he1.symm ▸ mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (hs2 z hz))
      (mul_pos hsq (add_pos h0 h2))
    have hc := nonneg_of_mul_nonneg_right (he2.symm ▸ mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (hs0 z hz))
      (mul_pos hsq (add_pos h0 h1))
    exact ⟨by linarith,by linarith,by linarith⟩
  intro z hz
  obtain ⟨ha,hb,hc⟩ := hupper z hz
  obtain ⟨ha',hb',hc'⟩ := hupper (-z) ((hsym z).1 hz)
  simp only [map_neg] at ha' hb' hc'
  exact ⟨abs_le.2 ⟨by linarith,ha⟩,abs_le.2 ⟨by linarith,hb⟩,abs_le.2 ⟨hc,by linarith⟩⟩

#print axioms tangent_side_identities
#print axioms inHexagon_of_tangent_support
end Certificate.Packing
