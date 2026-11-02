import Certificate.NewCertificateDefinitions
import Certificate.Assembly.H2Proof
import Certificate.Potential.H2
namespace Certificate.NewCertificate
open Certificate.Sparse Certificate.Potential
set_option maxHeartbeats 0
theorem boundary_gamma (x : State) :
    eval x.coordinates Identities.H2.gamma =
      (Potential.H2.scaleFactor : ℝ)*16*(Potential.denominator : ℝ)*Certificate.gamma := by
  norm_num [Identities.H2.gamma,Identities.H2.gamma_0,eval,Exponent.eval,
    Potential.H2.scaleFactor,Potential.denominator,Certificate.gamma]
  <;> ring

/-- The exact boundary improvement for the supplied potential, on its stated region. -/
theorem boundary (x : State) (hx : OnRegion x) :
    Certificate.gamma ≤ stateValue (rotateState x)-stateValue (initialState x) := by
  have h := Assembly.H2.target_lower_bound x.coordinates (by rfl) hx.1.1 hx.1.2 hx.2
  rw [boundary_gamma,Potential.H2.semantic_identity,boundary_evaluation] at h
  have hs : (0 : ℝ) < Potential.H2.scaleFactor := by exact_mod_cast Potential.H2.scale_positive
  have hd : (0 : ℝ) < Potential.denominator := by exact_mod_cast denominator_pos
  have hp : (0 : ℝ) < (Potential.H2.scaleFactor : ℝ)*16*(Potential.denominator : ℝ) :=
    mul_pos (mul_pos hs (by norm_num)) hd
  have hgap : 0 ≤ ((Potential.H2.scaleFactor : ℝ)*16*(Potential.denominator : ℝ))*
      (stateValue (rotateState x)-stateValue (initialState x)-Certificate.gamma) := by
    nlinarith only [h]
  have hnonneg := (mul_nonneg_iff_of_pos_left hp).mp hgap
  linarith only [hnonneg]

#print axioms boundary
end Certificate.NewCertificate
