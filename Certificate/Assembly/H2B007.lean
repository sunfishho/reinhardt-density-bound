import Certificate.SOS.H2B007Proof
import Certificate.Generated.H2B007Proof
import Certificate.MultiplierCertificates
namespace Certificate.Assembly.H2B007
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem multiplier_identification : Certificate.SOS.H2B007.multiplier = Certificate.MultiplierProofs.M014.certificate.polynomial := by
  decide +kernel

/-- All new algebraic obligations are discharged; the remaining hypotheses describe the domain. -/
theorem nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x (scale Certificate.SOS.H2B007.weight Certificate.SOS.H2B007.weighted) := by
  have hroot : (x 7)^2=3 := by rw [hx]; exact Real.sq_sqrt (by norm_num)
  apply Certificate.SOS.H2B007.weighted_nonnegative x hx
    Certificate.Generated.H2B007.positive_semidefinite
  rw [multiplier_identification]
  exact Certificate.MultiplierProofs.M014.nonnegative x hroot hregion
#print axioms nonnegative
end Certificate.Assembly.H2B007
