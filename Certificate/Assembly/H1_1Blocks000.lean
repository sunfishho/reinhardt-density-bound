import Certificate.Generated.H1_1B000Proof
import Certificate.Generated.H1_1B001Proof
import Certificate.Generated.H1_1B002Proof
import Certificate.Generated.H1_1B003Proof
import Certificate.Generated.H1_1B004Proof
import Certificate.Generated.H1_1B005Proof
import Certificate.Generated.H1_1B006Proof
import Certificate.Generated.H1_1B007Proof
import Certificate.Generated.H1_1B008Proof
import Certificate.Generated.H1_1B009Proof
import Certificate.Generated.H1_1B010Proof
import Certificate.Generated.H1_1B011Proof
import Certificate.Generated.H1_1B012Proof
import Certificate.Generated.H1_1B013Proof
import Certificate.Generated.H1_1B014Proof
import Certificate.Generated.H1_1B015Proof
import Certificate.Generated.H1_1B016Proof
import Certificate.Generated.H1_1B017Proof
import Certificate.Generated.H1_1B018Proof
import Certificate.Generated.H1_1B019Proof
import Certificate.Generated.H1_1B020Proof
import Certificate.Generated.H1_1B021Proof
import Certificate.Generated.H1_1B022Proof
import Certificate.Generated.H1_1B023Proof
import Certificate.Generated.H1_1B024Proof
import Certificate.MultiplierCertificates
import Certificate.SOS.H1_1B000Proof
import Certificate.SOS.H1_1B001Proof
import Certificate.SOS.H1_1B002Proof
import Certificate.SOS.H1_1B003Proof
import Certificate.SOS.H1_1B004Proof
import Certificate.SOS.H1_1B005Proof
import Certificate.SOS.H1_1B006Proof
import Certificate.SOS.H1_1B007Proof
import Certificate.SOS.H1_1B008Proof
import Certificate.SOS.H1_1B009Proof
import Certificate.SOS.H1_1B010Proof
import Certificate.SOS.H1_1B011Proof
import Certificate.SOS.H1_1B012Proof
import Certificate.SOS.H1_1B013Proof
import Certificate.SOS.H1_1B014Proof
import Certificate.SOS.H1_1B015Proof
import Certificate.SOS.H1_1B016Proof
import Certificate.SOS.H1_1B017Proof
import Certificate.SOS.H1_1B018Proof
import Certificate.SOS.H1_1B019Proof
import Certificate.SOS.H1_1B020Proof
import Certificate.SOS.H1_1B021Proof
import Certificate.SOS.H1_1B022Proof
import Certificate.SOS.H1_1B023Proof
import Certificate.SOS.H1_1B024Proof
namespace Certificate.Assembly.H1_1B000
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem multiplier_identification : Certificate.SOS.H1_1B000.multiplier = Certificate.MultiplierProofs.M000.certificate.polynomial := by
  decide +kernel

/-- All new algebraic obligations are discharged; the remaining hypotheses describe the domain. -/
theorem nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x (scale Certificate.SOS.H1_1B000.weight Certificate.SOS.H1_1B000.weighted) := by
  have hroot : (x 7)^2=3 := by rw [hx]; exact Real.sq_sqrt (by norm_num)
  apply Certificate.SOS.H1_1B000.weighted_nonnegative x hx
    Certificate.Generated.H1_1B000.positive_semidefinite
  rw [multiplier_identification]
  exact Certificate.MultiplierProofs.M000.nonnegative x hroot hregion
#print axioms nonnegative
end Certificate.Assembly.H1_1B000
namespace Certificate.Assembly.H1_1B001
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem multiplier_identification : Certificate.SOS.H1_1B001.multiplier = Certificate.MultiplierProofs.M001.certificate.polynomial := by
  decide +kernel

/-- All new algebraic obligations are discharged; the remaining hypotheses describe the domain. -/
theorem nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x (scale Certificate.SOS.H1_1B001.weight Certificate.SOS.H1_1B001.weighted) := by
  have hroot : (x 7)^2=3 := by rw [hx]; exact Real.sq_sqrt (by norm_num)
  apply Certificate.SOS.H1_1B001.weighted_nonnegative x hx
    Certificate.Generated.H1_1B001.positive_semidefinite
  rw [multiplier_identification]
  exact Certificate.MultiplierProofs.M001.nonnegative x hroot hregion
#print axioms nonnegative
end Certificate.Assembly.H1_1B001
namespace Certificate.Assembly.H1_1B002
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem multiplier_identification : Certificate.SOS.H1_1B002.multiplier = Certificate.MultiplierProofs.M002.certificate.polynomial := by
  decide +kernel

/-- All new algebraic obligations are discharged; the remaining hypotheses describe the domain. -/
theorem nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x (scale Certificate.SOS.H1_1B002.weight Certificate.SOS.H1_1B002.weighted) := by
  have hroot : (x 7)^2=3 := by rw [hx]; exact Real.sq_sqrt (by norm_num)
  apply Certificate.SOS.H1_1B002.weighted_nonnegative x hx
    Certificate.Generated.H1_1B002.positive_semidefinite
  rw [multiplier_identification]
  exact Certificate.MultiplierProofs.M002.nonnegative x hroot hregion
#print axioms nonnegative
end Certificate.Assembly.H1_1B002
namespace Certificate.Assembly.H1_1B003
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem multiplier_identification : Certificate.SOS.H1_1B003.multiplier = Certificate.MultiplierProofs.M003.certificate.polynomial := by
  decide +kernel

/-- All new algebraic obligations are discharged; the remaining hypotheses describe the domain. -/
theorem nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x (scale Certificate.SOS.H1_1B003.weight Certificate.SOS.H1_1B003.weighted) := by
  have hroot : (x 7)^2=3 := by rw [hx]; exact Real.sq_sqrt (by norm_num)
  apply Certificate.SOS.H1_1B003.weighted_nonnegative x hx
    Certificate.Generated.H1_1B003.positive_semidefinite
  rw [multiplier_identification]
  exact Certificate.MultiplierProofs.M003.nonnegative x hroot hregion
#print axioms nonnegative
end Certificate.Assembly.H1_1B003
namespace Certificate.Assembly.H1_1B004
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem multiplier_identification : Certificate.SOS.H1_1B004.multiplier = Certificate.MultiplierProofs.M004.certificate.polynomial := by
  decide +kernel

/-- All new algebraic obligations are discharged; the remaining hypotheses describe the domain. -/
theorem nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x (scale Certificate.SOS.H1_1B004.weight Certificate.SOS.H1_1B004.weighted) := by
  have hroot : (x 7)^2=3 := by rw [hx]; exact Real.sq_sqrt (by norm_num)
  apply Certificate.SOS.H1_1B004.weighted_nonnegative x hx
    Certificate.Generated.H1_1B004.positive_semidefinite
  rw [multiplier_identification]
  exact Certificate.MultiplierProofs.M004.nonnegative x hroot hregion
#print axioms nonnegative
end Certificate.Assembly.H1_1B004
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
namespace Certificate.Assembly.H1_1B006
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem multiplier_identification : Certificate.SOS.H1_1B006.multiplier = Certificate.MultiplierProofs.M006.certificate.polynomial := by
  decide +kernel

/-- All new algebraic obligations are discharged; the remaining hypotheses describe the domain. -/
theorem nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x (scale Certificate.SOS.H1_1B006.weight Certificate.SOS.H1_1B006.weighted) := by
  have hroot : (x 7)^2=3 := by rw [hx]; exact Real.sq_sqrt (by norm_num)
  apply Certificate.SOS.H1_1B006.weighted_nonnegative x hx
    Certificate.Generated.H1_1B006.positive_semidefinite
  rw [multiplier_identification]
  exact Certificate.MultiplierProofs.M006.nonnegative x hroot hregion
#print axioms nonnegative
end Certificate.Assembly.H1_1B006
namespace Certificate.Assembly.H1_1B007
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem multiplier_identification : Certificate.SOS.H1_1B007.multiplier = Certificate.MultiplierProofs.M007.certificate.polynomial := by
  decide +kernel

/-- All new algebraic obligations are discharged; the remaining hypotheses describe the domain. -/
theorem nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x (scale Certificate.SOS.H1_1B007.weight Certificate.SOS.H1_1B007.weighted) := by
  have hroot : (x 7)^2=3 := by rw [hx]; exact Real.sq_sqrt (by norm_num)
  apply Certificate.SOS.H1_1B007.weighted_nonnegative x hx
    Certificate.Generated.H1_1B007.positive_semidefinite
  rw [multiplier_identification]
  exact Certificate.MultiplierProofs.M007.nonnegative x hroot hregion
#print axioms nonnegative
end Certificate.Assembly.H1_1B007
namespace Certificate.Assembly.H1_1B008
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem multiplier_identification : Certificate.SOS.H1_1B008.multiplier = Certificate.MultiplierProofs.M008.certificate.polynomial := by
  decide +kernel

/-- All new algebraic obligations are discharged; the remaining hypotheses describe the domain. -/
theorem nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x (scale Certificate.SOS.H1_1B008.weight Certificate.SOS.H1_1B008.weighted) := by
  have hroot : (x 7)^2=3 := by rw [hx]; exact Real.sq_sqrt (by norm_num)
  apply Certificate.SOS.H1_1B008.weighted_nonnegative x hx
    Certificate.Generated.H1_1B008.positive_semidefinite
  rw [multiplier_identification]
  exact Certificate.MultiplierProofs.M008.nonnegative x hroot hregion
#print axioms nonnegative
end Certificate.Assembly.H1_1B008
namespace Certificate.Assembly.H1_1B009
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem multiplier_identification : Certificate.SOS.H1_1B009.multiplier = Certificate.MultiplierProofs.M009.certificate.polynomial := by
  decide +kernel

/-- All new algebraic obligations are discharged; the remaining hypotheses describe the domain. -/
theorem nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x (scale Certificate.SOS.H1_1B009.weight Certificate.SOS.H1_1B009.weighted) := by
  have hroot : (x 7)^2=3 := by rw [hx]; exact Real.sq_sqrt (by norm_num)
  apply Certificate.SOS.H1_1B009.weighted_nonnegative x hx
    Certificate.Generated.H1_1B009.positive_semidefinite
  rw [multiplier_identification]
  exact Certificate.MultiplierProofs.M009.nonnegative x hroot hregion
#print axioms nonnegative
end Certificate.Assembly.H1_1B009
namespace Certificate.Assembly.H1_1B010
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem multiplier_identification : Certificate.SOS.H1_1B010.multiplier = Certificate.MultiplierProofs.M010.certificate.polynomial := by
  decide +kernel

/-- All new algebraic obligations are discharged; the remaining hypotheses describe the domain. -/
theorem nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x (scale Certificate.SOS.H1_1B010.weight Certificate.SOS.H1_1B010.weighted) := by
  have hroot : (x 7)^2=3 := by rw [hx]; exact Real.sq_sqrt (by norm_num)
  apply Certificate.SOS.H1_1B010.weighted_nonnegative x hx
    Certificate.Generated.H1_1B010.positive_semidefinite
  rw [multiplier_identification]
  exact Certificate.MultiplierProofs.M010.nonnegative x hroot hregion
#print axioms nonnegative
end Certificate.Assembly.H1_1B010
namespace Certificate.Assembly.H1_1B011
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem multiplier_identification : Certificate.SOS.H1_1B011.multiplier = Certificate.MultiplierProofs.M011.certificate.polynomial := by
  decide +kernel

/-- All new algebraic obligations are discharged; the remaining hypotheses describe the domain. -/
theorem nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x (scale Certificate.SOS.H1_1B011.weight Certificate.SOS.H1_1B011.weighted) := by
  have hroot : (x 7)^2=3 := by rw [hx]; exact Real.sq_sqrt (by norm_num)
  apply Certificate.SOS.H1_1B011.weighted_nonnegative x hx
    Certificate.Generated.H1_1B011.positive_semidefinite
  rw [multiplier_identification]
  exact Certificate.MultiplierProofs.M011.nonnegative x hroot hregion
#print axioms nonnegative
end Certificate.Assembly.H1_1B011
namespace Certificate.Assembly.H1_1B012
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem multiplier_identification : Certificate.SOS.H1_1B012.multiplier = Certificate.MultiplierProofs.M012.certificate.polynomial := by
  decide +kernel

/-- All new algebraic obligations are discharged; the remaining hypotheses describe the domain. -/
theorem nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x (scale Certificate.SOS.H1_1B012.weight Certificate.SOS.H1_1B012.weighted) := by
  have hroot : (x 7)^2=3 := by rw [hx]; exact Real.sq_sqrt (by norm_num)
  apply Certificate.SOS.H1_1B012.weighted_nonnegative x hx
    Certificate.Generated.H1_1B012.positive_semidefinite
  rw [multiplier_identification]
  exact Certificate.MultiplierProofs.M012.nonnegative x hroot hregion
#print axioms nonnegative
end Certificate.Assembly.H1_1B012
namespace Certificate.Assembly.H1_1B013
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem multiplier_identification : Certificate.SOS.H1_1B013.multiplier = Certificate.MultiplierProofs.M013.certificate.polynomial := by
  decide +kernel

/-- All new algebraic obligations are discharged; the remaining hypotheses describe the domain. -/
theorem nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x (scale Certificate.SOS.H1_1B013.weight Certificate.SOS.H1_1B013.weighted) := by
  have hroot : (x 7)^2=3 := by rw [hx]; exact Real.sq_sqrt (by norm_num)
  apply Certificate.SOS.H1_1B013.weighted_nonnegative x hx
    Certificate.Generated.H1_1B013.positive_semidefinite
  rw [multiplier_identification]
  exact Certificate.MultiplierProofs.M013.nonnegative x hroot hregion
#print axioms nonnegative
end Certificate.Assembly.H1_1B013
namespace Certificate.Assembly.H1_1B014
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem multiplier_identification : Certificate.SOS.H1_1B014.multiplier = Certificate.MultiplierProofs.M014.certificate.polynomial := by
  decide +kernel

/-- All new algebraic obligations are discharged; the remaining hypotheses describe the domain. -/
theorem nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x (scale Certificate.SOS.H1_1B014.weight Certificate.SOS.H1_1B014.weighted) := by
  have hroot : (x 7)^2=3 := by rw [hx]; exact Real.sq_sqrt (by norm_num)
  apply Certificate.SOS.H1_1B014.weighted_nonnegative x hx
    Certificate.Generated.H1_1B014.positive_semidefinite
  rw [multiplier_identification]
  exact Certificate.MultiplierProofs.M014.nonnegative x hroot hregion
#print axioms nonnegative
end Certificate.Assembly.H1_1B014
namespace Certificate.Assembly.H1_1B015
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem multiplier_identification : Certificate.SOS.H1_1B015.multiplier = Certificate.MultiplierProofs.M015.certificate.polynomial := by
  decide +kernel

/-- All new algebraic obligations are discharged; the remaining hypotheses describe the domain. -/
theorem nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x (scale Certificate.SOS.H1_1B015.weight Certificate.SOS.H1_1B015.weighted) := by
  have hroot : (x 7)^2=3 := by rw [hx]; exact Real.sq_sqrt (by norm_num)
  apply Certificate.SOS.H1_1B015.weighted_nonnegative x hx
    Certificate.Generated.H1_1B015.positive_semidefinite
  rw [multiplier_identification]
  exact Certificate.MultiplierProofs.M015.nonnegative x hroot hregion
#print axioms nonnegative
end Certificate.Assembly.H1_1B015
namespace Certificate.Assembly.H1_1B016
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem multiplier_identification : Certificate.SOS.H1_1B016.multiplier = Certificate.MultiplierProofs.M016.certificate.polynomial := by
  decide +kernel

/-- All new algebraic obligations are discharged; the remaining hypotheses describe the domain. -/
theorem nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x (scale Certificate.SOS.H1_1B016.weight Certificate.SOS.H1_1B016.weighted) := by
  have hroot : (x 7)^2=3 := by rw [hx]; exact Real.sq_sqrt (by norm_num)
  apply Certificate.SOS.H1_1B016.weighted_nonnegative x hx
    Certificate.Generated.H1_1B016.positive_semidefinite
  rw [multiplier_identification]
  exact Certificate.MultiplierProofs.M016.nonnegative x hroot hregion
#print axioms nonnegative
end Certificate.Assembly.H1_1B016
namespace Certificate.Assembly.H1_1B017
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem multiplier_identification : Certificate.SOS.H1_1B017.multiplier = Certificate.MultiplierProofs.M017.certificate.polynomial := by
  decide +kernel

/-- All new algebraic obligations are discharged; the remaining hypotheses describe the domain. -/
theorem nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x (scale Certificate.SOS.H1_1B017.weight Certificate.SOS.H1_1B017.weighted) := by
  have hroot : (x 7)^2=3 := by rw [hx]; exact Real.sq_sqrt (by norm_num)
  apply Certificate.SOS.H1_1B017.weighted_nonnegative x hx
    Certificate.Generated.H1_1B017.positive_semidefinite
  rw [multiplier_identification]
  exact Certificate.MultiplierProofs.M017.nonnegative x hroot hregion
#print axioms nonnegative
end Certificate.Assembly.H1_1B017
namespace Certificate.Assembly.H1_1B018
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem multiplier_identification : Certificate.SOS.H1_1B018.multiplier = Certificate.MultiplierProofs.M018.certificate.polynomial := by
  decide +kernel

/-- All new algebraic obligations are discharged; the remaining hypotheses describe the domain. -/
theorem nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x (scale Certificate.SOS.H1_1B018.weight Certificate.SOS.H1_1B018.weighted) := by
  have hroot : (x 7)^2=3 := by rw [hx]; exact Real.sq_sqrt (by norm_num)
  apply Certificate.SOS.H1_1B018.weighted_nonnegative x hx
    Certificate.Generated.H1_1B018.positive_semidefinite
  rw [multiplier_identification]
  exact Certificate.MultiplierProofs.M018.nonnegative x hroot hregion
#print axioms nonnegative
end Certificate.Assembly.H1_1B018
namespace Certificate.Assembly.H1_1B019
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem multiplier_identification : Certificate.SOS.H1_1B019.multiplier = Certificate.MultiplierProofs.M019.certificate.polynomial := by
  decide +kernel

/-- All new algebraic obligations are discharged; the remaining hypotheses describe the domain. -/
theorem nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x (scale Certificate.SOS.H1_1B019.weight Certificate.SOS.H1_1B019.weighted) := by
  have hroot : (x 7)^2=3 := by rw [hx]; exact Real.sq_sqrt (by norm_num)
  apply Certificate.SOS.H1_1B019.weighted_nonnegative x hx
    Certificate.Generated.H1_1B019.positive_semidefinite
  rw [multiplier_identification]
  exact Certificate.MultiplierProofs.M019.nonnegative x hroot hregion
#print axioms nonnegative
end Certificate.Assembly.H1_1B019
namespace Certificate.Assembly.H1_1B020
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem multiplier_identification : Certificate.SOS.H1_1B020.multiplier = Certificate.MultiplierProofs.M020.certificate.polynomial := by
  decide +kernel

/-- All new algebraic obligations are discharged; the remaining hypotheses describe the domain. -/
theorem nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x (scale Certificate.SOS.H1_1B020.weight Certificate.SOS.H1_1B020.weighted) := by
  have hroot : (x 7)^2=3 := by rw [hx]; exact Real.sq_sqrt (by norm_num)
  apply Certificate.SOS.H1_1B020.weighted_nonnegative x hx
    Certificate.Generated.H1_1B020.positive_semidefinite
  rw [multiplier_identification]
  exact Certificate.MultiplierProofs.M020.nonnegative x hroot hregion
#print axioms nonnegative
end Certificate.Assembly.H1_1B020
namespace Certificate.Assembly.H1_1B021
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem multiplier_identification : Certificate.SOS.H1_1B021.multiplier = Certificate.MultiplierProofs.M021.certificate.polynomial := by
  decide +kernel

/-- All new algebraic obligations are discharged; the remaining hypotheses describe the domain. -/
theorem nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x (scale Certificate.SOS.H1_1B021.weight Certificate.SOS.H1_1B021.weighted) := by
  have hroot : (x 7)^2=3 := by rw [hx]; exact Real.sq_sqrt (by norm_num)
  apply Certificate.SOS.H1_1B021.weighted_nonnegative x hx
    Certificate.Generated.H1_1B021.positive_semidefinite
  rw [multiplier_identification]
  exact Certificate.MultiplierProofs.M021.nonnegative x hroot hregion
#print axioms nonnegative
end Certificate.Assembly.H1_1B021
namespace Certificate.Assembly.H1_1B022
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem multiplier_identification : Certificate.SOS.H1_1B022.multiplier = Certificate.MultiplierProofs.M022.certificate.polynomial := by
  decide +kernel

/-- All new algebraic obligations are discharged; the remaining hypotheses describe the domain. -/
theorem nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x (scale Certificate.SOS.H1_1B022.weight Certificate.SOS.H1_1B022.weighted) := by
  have hroot : (x 7)^2=3 := by rw [hx]; exact Real.sq_sqrt (by norm_num)
  apply Certificate.SOS.H1_1B022.weighted_nonnegative x hx
    Certificate.Generated.H1_1B022.positive_semidefinite
  rw [multiplier_identification]
  exact Certificate.MultiplierProofs.M022.nonnegative x hroot hregion
#print axioms nonnegative
end Certificate.Assembly.H1_1B022
namespace Certificate.Assembly.H1_1B023
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem multiplier_identification : Certificate.SOS.H1_1B023.multiplier = Certificate.MultiplierProofs.M023.certificate.polynomial := by
  decide +kernel

/-- All new algebraic obligations are discharged; the remaining hypotheses describe the domain. -/
theorem nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x (scale Certificate.SOS.H1_1B023.weight Certificate.SOS.H1_1B023.weighted) := by
  have hroot : (x 7)^2=3 := by rw [hx]; exact Real.sq_sqrt (by norm_num)
  apply Certificate.SOS.H1_1B023.weighted_nonnegative x hx
    Certificate.Generated.H1_1B023.positive_semidefinite
  rw [multiplier_identification]
  exact Certificate.MultiplierProofs.M023.nonnegative x hroot hregion
#print axioms nonnegative
end Certificate.Assembly.H1_1B023
namespace Certificate.Assembly.H1_1B024
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem multiplier_identification : Certificate.SOS.H1_1B024.multiplier = Certificate.MultiplierProofs.M024.certificate.polynomial := by
  decide +kernel

/-- All new algebraic obligations are discharged; the remaining hypotheses describe the domain. -/
theorem nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x (scale Certificate.SOS.H1_1B024.weight Certificate.SOS.H1_1B024.weighted) := by
  have hroot : (x 7)^2=3 := by rw [hx]; exact Real.sq_sqrt (by norm_num)
  apply Certificate.SOS.H1_1B024.weighted_nonnegative x hx
    Certificate.Generated.H1_1B024.positive_semidefinite
  rw [multiplier_identification]
  exact Certificate.MultiplierProofs.M024.nonnegative x hroot hregion
#print axioms nonnegative
end Certificate.Assembly.H1_1B024
