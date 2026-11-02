import Certificate.Generated.H1_1B025Proof
import Certificate.Generated.H1_1B026Proof
import Certificate.Generated.H1_1B027Proof
import Certificate.Generated.H1_1B028Proof
import Certificate.Generated.H1_1B029Proof
import Certificate.Generated.H1_1B030Proof
import Certificate.Generated.H1_1B031Proof
import Certificate.Generated.H1_1B032Proof
import Certificate.Generated.H1_1B033Proof
import Certificate.Generated.H1_1B034Proof
import Certificate.Generated.H1_1B035Proof
import Certificate.Generated.H1_1B036Proof
import Certificate.Generated.H1_1B037Proof
import Certificate.Generated.H1_1B038Proof
import Certificate.Generated.H1_1B039Proof
import Certificate.Generated.H1_1B040Proof
import Certificate.Generated.H1_1B041Proof
import Certificate.Generated.H1_1B042Proof
import Certificate.Generated.H1_1B043Proof
import Certificate.Generated.H1_1B044Proof
import Certificate.Generated.H1_1B045Proof
import Certificate.Generated.H1_1B046Proof
import Certificate.Generated.H1_1B047Proof
import Certificate.Generated.H1_1B048Proof
import Certificate.Generated.H1_1B049Proof
import Certificate.MultiplierCertificates
import Certificate.SOS.H1_1B025Proof
import Certificate.SOS.H1_1B026Proof
import Certificate.SOS.H1_1B027Proof
import Certificate.SOS.H1_1B028Proof
import Certificate.SOS.H1_1B029Proof
import Certificate.SOS.H1_1B030Proof
import Certificate.SOS.H1_1B031Proof
import Certificate.SOS.H1_1B032Proof
import Certificate.SOS.H1_1B033Proof
import Certificate.SOS.H1_1B034Proof
import Certificate.SOS.H1_1B035Proof
import Certificate.SOS.H1_1B036Proof
import Certificate.SOS.H1_1B037Proof
import Certificate.SOS.H1_1B038Proof
import Certificate.SOS.H1_1B039Proof
import Certificate.SOS.H1_1B040Proof
import Certificate.SOS.H1_1B041Proof
import Certificate.SOS.H1_1B042Proof
import Certificate.SOS.H1_1B043Proof
import Certificate.SOS.H1_1B044Proof
import Certificate.SOS.H1_1B045Proof
import Certificate.SOS.H1_1B046Proof
import Certificate.SOS.H1_1B047Proof
import Certificate.SOS.H1_1B048Proof
import Certificate.SOS.H1_1B049Proof
namespace Certificate.Assembly.H1_1B025
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem multiplier_identification : Certificate.SOS.H1_1B025.multiplier = Certificate.MultiplierProofs.M025.certificate.polynomial := by
  decide +kernel

/-- All new algebraic obligations are discharged; the remaining hypotheses describe the domain. -/
theorem nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x (scale Certificate.SOS.H1_1B025.weight Certificate.SOS.H1_1B025.weighted) := by
  have hroot : (x 7)^2=3 := by rw [hx]; exact Real.sq_sqrt (by norm_num)
  apply Certificate.SOS.H1_1B025.weighted_nonnegative x hx
    Certificate.Generated.H1_1B025.positive_semidefinite
  rw [multiplier_identification]
  exact Certificate.MultiplierProofs.M025.nonnegative x hroot hregion
#print axioms nonnegative
end Certificate.Assembly.H1_1B025
namespace Certificate.Assembly.H1_1B026
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem multiplier_identification : Certificate.SOS.H1_1B026.multiplier = Certificate.MultiplierProofs.M026.certificate.polynomial := by
  decide +kernel

/-- All new algebraic obligations are discharged; the remaining hypotheses describe the domain. -/
theorem nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x (scale Certificate.SOS.H1_1B026.weight Certificate.SOS.H1_1B026.weighted) := by
  have hroot : (x 7)^2=3 := by rw [hx]; exact Real.sq_sqrt (by norm_num)
  apply Certificate.SOS.H1_1B026.weighted_nonnegative x hx
    Certificate.Generated.H1_1B026.positive_semidefinite
  rw [multiplier_identification]
  exact Certificate.MultiplierProofs.M026.nonnegative x hroot hregion
#print axioms nonnegative
end Certificate.Assembly.H1_1B026
namespace Certificate.Assembly.H1_1B027
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem multiplier_identification : Certificate.SOS.H1_1B027.multiplier = Certificate.MultiplierProofs.M027.certificate.polynomial := by
  decide +kernel

/-- All new algebraic obligations are discharged; the remaining hypotheses describe the domain. -/
theorem nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x (scale Certificate.SOS.H1_1B027.weight Certificate.SOS.H1_1B027.weighted) := by
  have hroot : (x 7)^2=3 := by rw [hx]; exact Real.sq_sqrt (by norm_num)
  apply Certificate.SOS.H1_1B027.weighted_nonnegative x hx
    Certificate.Generated.H1_1B027.positive_semidefinite
  rw [multiplier_identification]
  exact Certificate.MultiplierProofs.M027.nonnegative x hroot hregion
#print axioms nonnegative
end Certificate.Assembly.H1_1B027
namespace Certificate.Assembly.H1_1B028
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem multiplier_identification : Certificate.SOS.H1_1B028.multiplier = Certificate.MultiplierProofs.M028.certificate.polynomial := by
  decide +kernel

/-- All new algebraic obligations are discharged; the remaining hypotheses describe the domain. -/
theorem nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x (scale Certificate.SOS.H1_1B028.weight Certificate.SOS.H1_1B028.weighted) := by
  have hroot : (x 7)^2=3 := by rw [hx]; exact Real.sq_sqrt (by norm_num)
  apply Certificate.SOS.H1_1B028.weighted_nonnegative x hx
    Certificate.Generated.H1_1B028.positive_semidefinite
  rw [multiplier_identification]
  exact Certificate.MultiplierProofs.M028.nonnegative x hroot hregion
#print axioms nonnegative
end Certificate.Assembly.H1_1B028
namespace Certificate.Assembly.H1_1B029
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem multiplier_identification : Certificate.SOS.H1_1B029.multiplier = Certificate.MultiplierProofs.M029.certificate.polynomial := by
  decide +kernel

/-- All new algebraic obligations are discharged; the remaining hypotheses describe the domain. -/
theorem nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x (scale Certificate.SOS.H1_1B029.weight Certificate.SOS.H1_1B029.weighted) := by
  have hroot : (x 7)^2=3 := by rw [hx]; exact Real.sq_sqrt (by norm_num)
  apply Certificate.SOS.H1_1B029.weighted_nonnegative x hx
    Certificate.Generated.H1_1B029.positive_semidefinite
  rw [multiplier_identification]
  exact Certificate.MultiplierProofs.M029.nonnegative x hroot hregion
#print axioms nonnegative
end Certificate.Assembly.H1_1B029
namespace Certificate.Assembly.H1_1B030
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem multiplier_identification : Certificate.SOS.H1_1B030.multiplier = Certificate.MultiplierProofs.M030.certificate.polynomial := by
  decide +kernel

/-- All new algebraic obligations are discharged; the remaining hypotheses describe the domain. -/
theorem nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x (scale Certificate.SOS.H1_1B030.weight Certificate.SOS.H1_1B030.weighted) := by
  have hroot : (x 7)^2=3 := by rw [hx]; exact Real.sq_sqrt (by norm_num)
  apply Certificate.SOS.H1_1B030.weighted_nonnegative x hx
    Certificate.Generated.H1_1B030.positive_semidefinite
  rw [multiplier_identification]
  exact Certificate.MultiplierProofs.M030.nonnegative x hroot hregion
#print axioms nonnegative
end Certificate.Assembly.H1_1B030
namespace Certificate.Assembly.H1_1B031
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem multiplier_identification : Certificate.SOS.H1_1B031.multiplier = Certificate.MultiplierProofs.M031.certificate.polynomial := by
  decide +kernel

/-- All new algebraic obligations are discharged; the remaining hypotheses describe the domain. -/
theorem nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x (scale Certificate.SOS.H1_1B031.weight Certificate.SOS.H1_1B031.weighted) := by
  have hroot : (x 7)^2=3 := by rw [hx]; exact Real.sq_sqrt (by norm_num)
  apply Certificate.SOS.H1_1B031.weighted_nonnegative x hx
    Certificate.Generated.H1_1B031.positive_semidefinite
  rw [multiplier_identification]
  exact Certificate.MultiplierProofs.M031.nonnegative x hroot hregion
#print axioms nonnegative
end Certificate.Assembly.H1_1B031
namespace Certificate.Assembly.H1_1B032
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem multiplier_identification : Certificate.SOS.H1_1B032.multiplier = Certificate.MultiplierProofs.M032.certificate.polynomial := by
  decide +kernel

/-- All new algebraic obligations are discharged; the remaining hypotheses describe the domain. -/
theorem nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x (scale Certificate.SOS.H1_1B032.weight Certificate.SOS.H1_1B032.weighted) := by
  have hroot : (x 7)^2=3 := by rw [hx]; exact Real.sq_sqrt (by norm_num)
  apply Certificate.SOS.H1_1B032.weighted_nonnegative x hx
    Certificate.Generated.H1_1B032.positive_semidefinite
  rw [multiplier_identification]
  exact Certificate.MultiplierProofs.M032.nonnegative x hroot hregion
#print axioms nonnegative
end Certificate.Assembly.H1_1B032
namespace Certificate.Assembly.H1_1B033
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem multiplier_identification : Certificate.SOS.H1_1B033.multiplier = Certificate.MultiplierProofs.M033.certificate.polynomial := by
  decide +kernel

/-- All new algebraic obligations are discharged; the remaining hypotheses describe the domain. -/
theorem nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x (scale Certificate.SOS.H1_1B033.weight Certificate.SOS.H1_1B033.weighted) := by
  have hroot : (x 7)^2=3 := by rw [hx]; exact Real.sq_sqrt (by norm_num)
  apply Certificate.SOS.H1_1B033.weighted_nonnegative x hx
    Certificate.Generated.H1_1B033.positive_semidefinite
  rw [multiplier_identification]
  exact Certificate.MultiplierProofs.M033.nonnegative x hroot hregion
#print axioms nonnegative
end Certificate.Assembly.H1_1B033
namespace Certificate.Assembly.H1_1B034
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem multiplier_identification : Certificate.SOS.H1_1B034.multiplier = Certificate.MultiplierProofs.M034.certificate.polynomial := by
  decide +kernel

/-- All new algebraic obligations are discharged; the remaining hypotheses describe the domain. -/
theorem nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x (scale Certificate.SOS.H1_1B034.weight Certificate.SOS.H1_1B034.weighted) := by
  have hroot : (x 7)^2=3 := by rw [hx]; exact Real.sq_sqrt (by norm_num)
  apply Certificate.SOS.H1_1B034.weighted_nonnegative x hx
    Certificate.Generated.H1_1B034.positive_semidefinite
  rw [multiplier_identification]
  exact Certificate.MultiplierProofs.M034.nonnegative x hroot hregion
#print axioms nonnegative
end Certificate.Assembly.H1_1B034
namespace Certificate.Assembly.H1_1B035
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem multiplier_identification : Certificate.SOS.H1_1B035.multiplier = Certificate.MultiplierProofs.M035.certificate.polynomial := by
  decide +kernel

/-- All new algebraic obligations are discharged; the remaining hypotheses describe the domain. -/
theorem nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x (scale Certificate.SOS.H1_1B035.weight Certificate.SOS.H1_1B035.weighted) := by
  have hroot : (x 7)^2=3 := by rw [hx]; exact Real.sq_sqrt (by norm_num)
  apply Certificate.SOS.H1_1B035.weighted_nonnegative x hx
    Certificate.Generated.H1_1B035.positive_semidefinite
  rw [multiplier_identification]
  exact Certificate.MultiplierProofs.M035.nonnegative x hroot hregion
#print axioms nonnegative
end Certificate.Assembly.H1_1B035
namespace Certificate.Assembly.H1_1B036
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem multiplier_identification : Certificate.SOS.H1_1B036.multiplier = Certificate.MultiplierProofs.M036.certificate.polynomial := by
  decide +kernel

/-- All new algebraic obligations are discharged; the remaining hypotheses describe the domain. -/
theorem nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x (scale Certificate.SOS.H1_1B036.weight Certificate.SOS.H1_1B036.weighted) := by
  have hroot : (x 7)^2=3 := by rw [hx]; exact Real.sq_sqrt (by norm_num)
  apply Certificate.SOS.H1_1B036.weighted_nonnegative x hx
    Certificate.Generated.H1_1B036.positive_semidefinite
  rw [multiplier_identification]
  exact Certificate.MultiplierProofs.M036.nonnegative x hroot hregion
#print axioms nonnegative
end Certificate.Assembly.H1_1B036
namespace Certificate.Assembly.H1_1B037
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem multiplier_identification : Certificate.SOS.H1_1B037.multiplier = Certificate.MultiplierProofs.M037.certificate.polynomial := by
  decide +kernel

/-- All new algebraic obligations are discharged; the remaining hypotheses describe the domain. -/
theorem nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x (scale Certificate.SOS.H1_1B037.weight Certificate.SOS.H1_1B037.weighted) := by
  have hroot : (x 7)^2=3 := by rw [hx]; exact Real.sq_sqrt (by norm_num)
  apply Certificate.SOS.H1_1B037.weighted_nonnegative x hx
    Certificate.Generated.H1_1B037.positive_semidefinite
  rw [multiplier_identification]
  exact Certificate.MultiplierProofs.M037.nonnegative x hroot hregion
#print axioms nonnegative
end Certificate.Assembly.H1_1B037
namespace Certificate.Assembly.H1_1B038
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem multiplier_identification : Certificate.SOS.H1_1B038.multiplier = Certificate.MultiplierProofs.M038.certificate.polynomial := by
  decide +kernel

/-- All new algebraic obligations are discharged; the remaining hypotheses describe the domain. -/
theorem nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x (scale Certificate.SOS.H1_1B038.weight Certificate.SOS.H1_1B038.weighted) := by
  have hroot : (x 7)^2=3 := by rw [hx]; exact Real.sq_sqrt (by norm_num)
  apply Certificate.SOS.H1_1B038.weighted_nonnegative x hx
    Certificate.Generated.H1_1B038.positive_semidefinite
  rw [multiplier_identification]
  exact Certificate.MultiplierProofs.M038.nonnegative x hroot hregion
#print axioms nonnegative
end Certificate.Assembly.H1_1B038
namespace Certificate.Assembly.H1_1B039
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem multiplier_identification : Certificate.SOS.H1_1B039.multiplier = Certificate.MultiplierProofs.M039.certificate.polynomial := by
  decide +kernel

/-- All new algebraic obligations are discharged; the remaining hypotheses describe the domain. -/
theorem nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x (scale Certificate.SOS.H1_1B039.weight Certificate.SOS.H1_1B039.weighted) := by
  have hroot : (x 7)^2=3 := by rw [hx]; exact Real.sq_sqrt (by norm_num)
  apply Certificate.SOS.H1_1B039.weighted_nonnegative x hx
    Certificate.Generated.H1_1B039.positive_semidefinite
  rw [multiplier_identification]
  exact Certificate.MultiplierProofs.M039.nonnegative x hroot hregion
#print axioms nonnegative
end Certificate.Assembly.H1_1B039
namespace Certificate.Assembly.H1_1B040
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem multiplier_identification : Certificate.SOS.H1_1B040.multiplier = Certificate.MultiplierProofs.M040.certificate.polynomial := by
  decide +kernel

/-- All new algebraic obligations are discharged; the remaining hypotheses describe the domain. -/
theorem nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x (scale Certificate.SOS.H1_1B040.weight Certificate.SOS.H1_1B040.weighted) := by
  have hroot : (x 7)^2=3 := by rw [hx]; exact Real.sq_sqrt (by norm_num)
  apply Certificate.SOS.H1_1B040.weighted_nonnegative x hx
    Certificate.Generated.H1_1B040.positive_semidefinite
  rw [multiplier_identification]
  exact Certificate.MultiplierProofs.M040.nonnegative x hroot hregion
#print axioms nonnegative
end Certificate.Assembly.H1_1B040
namespace Certificate.Assembly.H1_1B041
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem multiplier_identification : Certificate.SOS.H1_1B041.multiplier = Certificate.MultiplierProofs.M041.certificate.polynomial := by
  decide +kernel

/-- All new algebraic obligations are discharged; the remaining hypotheses describe the domain. -/
theorem nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x (scale Certificate.SOS.H1_1B041.weight Certificate.SOS.H1_1B041.weighted) := by
  have hroot : (x 7)^2=3 := by rw [hx]; exact Real.sq_sqrt (by norm_num)
  apply Certificate.SOS.H1_1B041.weighted_nonnegative x hx
    Certificate.Generated.H1_1B041.positive_semidefinite
  rw [multiplier_identification]
  exact Certificate.MultiplierProofs.M041.nonnegative x hroot hregion
#print axioms nonnegative
end Certificate.Assembly.H1_1B041
namespace Certificate.Assembly.H1_1B042
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem multiplier_identification : Certificate.SOS.H1_1B042.multiplier = Certificate.MultiplierProofs.M042.certificate.polynomial := by
  decide +kernel

/-- All new algebraic obligations are discharged; the remaining hypotheses describe the domain. -/
theorem nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x (scale Certificate.SOS.H1_1B042.weight Certificate.SOS.H1_1B042.weighted) := by
  have hroot : (x 7)^2=3 := by rw [hx]; exact Real.sq_sqrt (by norm_num)
  apply Certificate.SOS.H1_1B042.weighted_nonnegative x hx
    Certificate.Generated.H1_1B042.positive_semidefinite
  rw [multiplier_identification]
  exact Certificate.MultiplierProofs.M042.nonnegative x hroot hregion
#print axioms nonnegative
end Certificate.Assembly.H1_1B042
namespace Certificate.Assembly.H1_1B043
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem multiplier_identification : Certificate.SOS.H1_1B043.multiplier = Certificate.MultiplierProofs.M043.certificate.polynomial := by
  decide +kernel

/-- All new algebraic obligations are discharged; the remaining hypotheses describe the domain. -/
theorem nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x (scale Certificate.SOS.H1_1B043.weight Certificate.SOS.H1_1B043.weighted) := by
  have hroot : (x 7)^2=3 := by rw [hx]; exact Real.sq_sqrt (by norm_num)
  apply Certificate.SOS.H1_1B043.weighted_nonnegative x hx
    Certificate.Generated.H1_1B043.positive_semidefinite
  rw [multiplier_identification]
  exact Certificate.MultiplierProofs.M043.nonnegative x hroot hregion
#print axioms nonnegative
end Certificate.Assembly.H1_1B043
namespace Certificate.Assembly.H1_1B044
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem multiplier_identification : Certificate.SOS.H1_1B044.multiplier = Certificate.MultiplierProofs.M044.certificate.polynomial := by
  decide +kernel

/-- All new algebraic obligations are discharged; the remaining hypotheses describe the domain. -/
theorem nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x (scale Certificate.SOS.H1_1B044.weight Certificate.SOS.H1_1B044.weighted) := by
  have hroot : (x 7)^2=3 := by rw [hx]; exact Real.sq_sqrt (by norm_num)
  apply Certificate.SOS.H1_1B044.weighted_nonnegative x hx
    Certificate.Generated.H1_1B044.positive_semidefinite
  rw [multiplier_identification]
  exact Certificate.MultiplierProofs.M044.nonnegative x hroot hregion
#print axioms nonnegative
end Certificate.Assembly.H1_1B044
namespace Certificate.Assembly.H1_1B045
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem multiplier_identification : Certificate.SOS.H1_1B045.multiplier = Certificate.MultiplierProofs.M045.certificate.polynomial := by
  decide +kernel

/-- All new algebraic obligations are discharged; the remaining hypotheses describe the domain. -/
theorem nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x (scale Certificate.SOS.H1_1B045.weight Certificate.SOS.H1_1B045.weighted) := by
  have hroot : (x 7)^2=3 := by rw [hx]; exact Real.sq_sqrt (by norm_num)
  apply Certificate.SOS.H1_1B045.weighted_nonnegative x hx
    Certificate.Generated.H1_1B045.positive_semidefinite
  rw [multiplier_identification]
  exact Certificate.MultiplierProofs.M045.nonnegative x hroot hregion
#print axioms nonnegative
end Certificate.Assembly.H1_1B045
namespace Certificate.Assembly.H1_1B046
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem multiplier_identification : Certificate.SOS.H1_1B046.multiplier = Certificate.MultiplierProofs.M046.certificate.polynomial := by
  decide +kernel

/-- All new algebraic obligations are discharged; the remaining hypotheses describe the domain. -/
theorem nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x (scale Certificate.SOS.H1_1B046.weight Certificate.SOS.H1_1B046.weighted) := by
  have hroot : (x 7)^2=3 := by rw [hx]; exact Real.sq_sqrt (by norm_num)
  apply Certificate.SOS.H1_1B046.weighted_nonnegative x hx
    Certificate.Generated.H1_1B046.positive_semidefinite
  rw [multiplier_identification]
  exact Certificate.MultiplierProofs.M046.nonnegative x hroot hregion
#print axioms nonnegative
end Certificate.Assembly.H1_1B046
namespace Certificate.Assembly.H1_1B047
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem multiplier_identification : Certificate.SOS.H1_1B047.multiplier = Certificate.MultiplierProofs.M047.certificate.polynomial := by
  decide +kernel

/-- All new algebraic obligations are discharged; the remaining hypotheses describe the domain. -/
theorem nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x (scale Certificate.SOS.H1_1B047.weight Certificate.SOS.H1_1B047.weighted) := by
  have hroot : (x 7)^2=3 := by rw [hx]; exact Real.sq_sqrt (by norm_num)
  apply Certificate.SOS.H1_1B047.weighted_nonnegative x hx
    Certificate.Generated.H1_1B047.positive_semidefinite
  rw [multiplier_identification]
  exact Certificate.MultiplierProofs.M047.nonnegative x hroot hregion
#print axioms nonnegative
end Certificate.Assembly.H1_1B047
namespace Certificate.Assembly.H1_1B048
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem multiplier_identification : Certificate.SOS.H1_1B048.multiplier = Certificate.MultiplierProofs.M048.certificate.polynomial := by
  decide +kernel

/-- All new algebraic obligations are discharged; the remaining hypotheses describe the domain. -/
theorem nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x (scale Certificate.SOS.H1_1B048.weight Certificate.SOS.H1_1B048.weighted) := by
  have hroot : (x 7)^2=3 := by rw [hx]; exact Real.sq_sqrt (by norm_num)
  apply Certificate.SOS.H1_1B048.weighted_nonnegative x hx
    Certificate.Generated.H1_1B048.positive_semidefinite
  rw [multiplier_identification]
  exact Certificate.MultiplierProofs.M048.nonnegative x hroot hregion
#print axioms nonnegative
end Certificate.Assembly.H1_1B048
namespace Certificate.Assembly.H1_1B049
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem multiplier_identification : Certificate.SOS.H1_1B049.multiplier = Certificate.MultiplierProofs.M049.certificate.polynomial := by
  decide +kernel

/-- All new algebraic obligations are discharged; the remaining hypotheses describe the domain. -/
theorem nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x (scale Certificate.SOS.H1_1B049.weight Certificate.SOS.H1_1B049.weighted) := by
  have hroot : (x 7)^2=3 := by rw [hx]; exact Real.sq_sqrt (by norm_num)
  apply Certificate.SOS.H1_1B049.weighted_nonnegative x hx
    Certificate.Generated.H1_1B049.positive_semidefinite
  rw [multiplier_identification]
  exact Certificate.MultiplierProofs.M049.nonnegative x hroot hregion
#print axioms nonnegative
end Certificate.Assembly.H1_1B049
