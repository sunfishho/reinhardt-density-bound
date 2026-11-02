import Certificate.SOS.H1_1B005Proof
import Certificate.Generated.H1_1B005Proof
import Certificate.MultiplierCertificates
namespace Certificate.Assembly.H1_1B005
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem multiplier_identification : Certificate.SOS.H1_1B005.multiplier = Certificate.MultiplierProofs.M005.certificate.polynomial := by
  decide +kernel

/-- All new algebraic obligations are discharged; the remaining hypotheses describe the domain. -/
theorem nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x (scale Certificate.SOS.H1_1B005.weight Certificate.SOS.H1_1B005.weighted) := by
  have hroot : (x 7)^2=3 := by rw [hx]; exact Real.sq_sqrt (by norm_num)
  apply Certificate.SOS.H1_1B005.weighted_nonnegative x hx
    Certificate.Generated.H1_1B005.positive_semidefinite
  rw [multiplier_identification]
  exact Certificate.MultiplierProofs.M005.nonnegative x hroot hregion
#print axioms nonnegative
end Certificate.Assembly.H1_1B005
