import Certificate.ConfinementGroupPath

namespace Certificate.Confinement
set_option maxHeartbeats 0

/-- The unrotated cusp and wall inequalities in HV Definition 5.0.1,
written in X coordinates (c=p+h, x=a/c, y=1/c). -/
def CuspAndWall (x : State) : Prop := 2/9 ≤ x.p+x.h ∧ 1/15 ≤ rho1 x

/-- Apply the two defining inequalities in the three charts related by R. -/
def RotatedCompactDomain (x : State) : Prop :=
  CuspAndWall x ∧ CuspAndWall (conjugate (Real.sqrt 3) x) ∧
    CuspAndWall (conjugate (-Real.sqrt 3) x)

theorem cuspAndWall_chart_iff (x : State) :
    CuspAndWall x ↔ 0 < x.p+x.h ∧
      1/(x.p+x.h) ≤ 9/2 ∧
      1/(x.p+x.h) ≤ 15*(Real.sqrt 3/3-x.a/(x.p+x.h)) := by
  constructor
  · rintro ⟨hc,hw⟩
    have hcpos : 0 < x.p+x.h := by linarith
    refine ⟨hcpos,(div_le_iff₀ hcpos).mpr (by linarith),?_⟩
    apply (div_le_iff₀ hcpos).mpr
    have he : 15*(Real.sqrt 3/3-x.a/(x.p+x.h))*(x.p+x.h)=15*rho1 x := by
      unfold rho1
      field_simp
    rw [he]
    linarith
  · rintro ⟨hcpos,hc,hw⟩
    have hc' := (div_le_iff₀ hcpos).mp hc
    have hw' := (div_le_iff₀ hcpos).mp hw
    have he : 15*(Real.sqrt 3/3-x.a/(x.p+x.h))*(x.p+x.h)=15*rho1 x := by
      unfold rho1
      field_simp
    rw [he] at hw'
    exact ⟨by linarith,by linarith⟩

/-- This checks the rho-coordinate reformulation of the geometric domain;
it is not an additional unverified confinement hypothesis. -/
theorem hvCompact_iff_rotated (x : State) : HVCompact x ↔ RotatedCompactDomain x := by
  have hs : Real.sqrt (3:ℝ)^2=3 := Real.sq_sqrt (by norm_num)
  have hspos : 0 < Real.sqrt (3:ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have rplus : rho1 (conjugate (Real.sqrt 3) x)=rho0 x := by
    unfold rho1 rho0 conjugate
    ring_nf; simp only [hs]; ring
  have rminus : rho1 (conjugate (-Real.sqrt 3) x)=rho2 x := by
    unfold rho1 rho2 conjugate
    ring_nf; simp only [hs]; ring
  have s01 : Real.sqrt 3*(rho0 x+rho1 x)=2*(x.p+x.h) := by
    obtain ⟨e0,e1,e2⟩ := sqrt_mul_rho x
    rw [mul_add,e0,e1]; ring
  have s02 : Real.sqrt 3*(rho0 x+rho2 x)=2*((conjugate (Real.sqrt 3) x).p+x.h) := by
    obtain ⟨e0,e1,e2⟩ := sqrt_mul_rho x
    rw [mul_add,e0,e2]; dsimp [conjugate]; ring
  have s12 : Real.sqrt 3*(rho1 x+rho2 x)=2*((conjugate (-Real.sqrt 3) x).p+x.h) := by
    obtain ⟨e0,e1,e2⟩ := sqrt_mul_rho x
    rw [mul_add,e1,e2]; dsimp [conjugate]; ring
  have hthreshold : Real.sqrt (3:ℝ)*(4*Real.sqrt 3/27)=4/9 := by nlinarith only [hs]
  have eq01 : 4*Real.sqrt 3/27 ≤ rho0 x+rho1 x ↔ 2/9 ≤ x.p+x.h := by
    rw [← mul_le_mul_iff_right₀ hspos,s01,hthreshold]
    constructor <;> intro h <;> linarith
  have eq02 : 4*Real.sqrt 3/27 ≤ rho0 x+rho2 x ↔ 2/9 ≤ (conjugate (Real.sqrt 3) x).p+x.h := by
    rw [← mul_le_mul_iff_right₀ hspos,s02,hthreshold]
    constructor <;> intro h <;> linarith
  have eq12 : 4*Real.sqrt 3/27 ≤ rho1 x+rho2 x ↔ 2/9 ≤ (conjugate (-Real.sqrt 3) x).p+x.h := by
    rw [← mul_le_mul_iff_right₀ hspos,s12,hthreshold]
    constructor <;> intro h <;> linarith
  unfold HVCompact RotatedCompactDomain CuspAndWall
  rw [rplus,rminus,eq01,eq02,eq12]
  change (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _) ↔ ((_ ∧ _) ∧ (_ ∧ _) ∧ (_ ∧ _))
  tauto

#print axioms cuspAndWall_chart_iff
#print axioms hvCompact_iff_rotated
end Certificate.Confinement
