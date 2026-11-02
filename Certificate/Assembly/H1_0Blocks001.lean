import Certificate.Generated.H1_0B025Proof
import Certificate.Generated.H1_0B026Proof
import Certificate.Generated.H1_0B027Proof
import Certificate.Generated.H1_0B028Proof
import Certificate.Generated.H1_0B029Proof
import Certificate.Generated.H1_0B030Proof
import Certificate.Generated.H1_0B031Proof
import Certificate.Generated.H1_0B032Proof
import Certificate.Generated.H1_0B033Proof
import Certificate.Generated.H1_0B034Proof
import Certificate.Generated.H1_0B035Proof
import Certificate.Generated.H1_0B036Proof
import Certificate.Generated.H1_0B037Proof
import Certificate.Generated.H1_0B038Proof
import Certificate.Generated.H1_0B039Proof
import Certificate.Generated.H1_0B040Proof
import Certificate.Generated.H1_0B041Proof
import Certificate.Generated.H1_0B042Proof
import Certificate.Generated.H1_0B043Proof
import Certificate.Generated.H1_0B044Proof
import Certificate.Generated.H1_0B045Proof
import Certificate.Generated.H1_0B046Proof
import Certificate.Generated.H1_0B047Proof
import Certificate.Generated.H1_0B048Proof
import Certificate.Generated.H1_0B049Proof
import Certificate.MultiplierCertificates
import Certificate.SOS.H1_0B025Proof
import Certificate.SOS.H1_0B026Proof
import Certificate.SOS.H1_0B027Proof
import Certificate.SOS.H1_0B028Proof
import Certificate.SOS.H1_0B029Proof
import Certificate.SOS.H1_0B030Proof
import Certificate.SOS.H1_0B031Proof
import Certificate.SOS.H1_0B032Proof
import Certificate.SOS.H1_0B033Proof
import Certificate.SOS.H1_0B034Proof
import Certificate.SOS.H1_0B035Proof
import Certificate.SOS.H1_0B036Proof
import Certificate.SOS.H1_0B037Proof
import Certificate.SOS.H1_0B038Proof
import Certificate.SOS.H1_0B039Proof
import Certificate.SOS.H1_0B040Proof
import Certificate.SOS.H1_0B041Proof
import Certificate.SOS.H1_0B042Proof
import Certificate.SOS.H1_0B043Proof
import Certificate.SOS.H1_0B044Proof
import Certificate.SOS.H1_0B045Proof
import Certificate.SOS.H1_0B046Proof
import Certificate.SOS.H1_0B047Proof
import Certificate.SOS.H1_0B048Proof
import Certificate.SOS.H1_0B049Proof
namespace Certificate.Assembly.H1_0B025
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem multiplier_identification : Certificate.SOS.H1_0B025.multiplier = Certificate.MultiplierProofs.M025.certificate.polynomial := by
  decide +kernel

/-- All new algebraic obligations are discharged; the remaining hypotheses describe the domain. -/
theorem nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x (scale Certificate.SOS.H1_0B025.weight Certificate.SOS.H1_0B025.weighted) := by
  have hroot : (x 7)^2=3 := by rw [hx]; exact Real.sq_sqrt (by norm_num)
  apply Certificate.SOS.H1_0B025.weighted_nonnegative x hx
    Certificate.Generated.H1_0B025.positive_semidefinite
  rw [multiplier_identification]
  exact Certificate.MultiplierProofs.M025.nonnegative x hroot hregion
#print axioms nonnegative
end Certificate.Assembly.H1_0B025
namespace Certificate.Assembly.H1_0B026
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem multiplier_identification : Certificate.SOS.H1_0B026.multiplier = Certificate.MultiplierProofs.M026.certificate.polynomial := by
  decide +kernel

/-- All new algebraic obligations are discharged; the remaining hypotheses describe the domain. -/
theorem nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x (scale Certificate.SOS.H1_0B026.weight Certificate.SOS.H1_0B026.weighted) := by
  have hroot : (x 7)^2=3 := by rw [hx]; exact Real.sq_sqrt (by norm_num)
  apply Certificate.SOS.H1_0B026.weighted_nonnegative x hx
    Certificate.Generated.H1_0B026.positive_semidefinite
  rw [multiplier_identification]
  exact Certificate.MultiplierProofs.M026.nonnegative x hroot hregion
#print axioms nonnegative
end Certificate.Assembly.H1_0B026
namespace Certificate.Assembly.H1_0B027
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem multiplier_identification : Certificate.SOS.H1_0B027.multiplier = Certificate.MultiplierProofs.M027.certificate.polynomial := by
  decide +kernel

/-- All new algebraic obligations are discharged; the remaining hypotheses describe the domain. -/
theorem nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x (scale Certificate.SOS.H1_0B027.weight Certificate.SOS.H1_0B027.weighted) := by
  have hroot : (x 7)^2=3 := by rw [hx]; exact Real.sq_sqrt (by norm_num)
  apply Certificate.SOS.H1_0B027.weighted_nonnegative x hx
    Certificate.Generated.H1_0B027.positive_semidefinite
  rw [multiplier_identification]
  exact Certificate.MultiplierProofs.M027.nonnegative x hroot hregion
#print axioms nonnegative
end Certificate.Assembly.H1_0B027
namespace Certificate.Assembly.H1_0B028
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem multiplier_identification : Certificate.SOS.H1_0B028.multiplier = Certificate.MultiplierProofs.M028.certificate.polynomial := by
  decide +kernel

/-- All new algebraic obligations are discharged; the remaining hypotheses describe the domain. -/
theorem nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x (scale Certificate.SOS.H1_0B028.weight Certificate.SOS.H1_0B028.weighted) := by
  have hroot : (x 7)^2=3 := by rw [hx]; exact Real.sq_sqrt (by norm_num)
  apply Certificate.SOS.H1_0B028.weighted_nonnegative x hx
    Certificate.Generated.H1_0B028.positive_semidefinite
  rw [multiplier_identification]
  exact Certificate.MultiplierProofs.M028.nonnegative x hroot hregion
#print axioms nonnegative
end Certificate.Assembly.H1_0B028
namespace Certificate.Assembly.H1_0B029
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem multiplier_identification : Certificate.SOS.H1_0B029.multiplier = Certificate.MultiplierProofs.M029.certificate.polynomial := by
  decide +kernel

/-- All new algebraic obligations are discharged; the remaining hypotheses describe the domain. -/
theorem nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x (scale Certificate.SOS.H1_0B029.weight Certificate.SOS.H1_0B029.weighted) := by
  have hroot : (x 7)^2=3 := by rw [hx]; exact Real.sq_sqrt (by norm_num)
  apply Certificate.SOS.H1_0B029.weighted_nonnegative x hx
    Certificate.Generated.H1_0B029.positive_semidefinite
  rw [multiplier_identification]
  exact Certificate.MultiplierProofs.M029.nonnegative x hroot hregion
#print axioms nonnegative
end Certificate.Assembly.H1_0B029
namespace Certificate.Assembly.H1_0B030
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem multiplier_identification : Certificate.SOS.H1_0B030.multiplier = Certificate.MultiplierProofs.M030.certificate.polynomial := by
  decide +kernel

/-- All new algebraic obligations are discharged; the remaining hypotheses describe the domain. -/
theorem nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x (scale Certificate.SOS.H1_0B030.weight Certificate.SOS.H1_0B030.weighted) := by
  have hroot : (x 7)^2=3 := by rw [hx]; exact Real.sq_sqrt (by norm_num)
  apply Certificate.SOS.H1_0B030.weighted_nonnegative x hx
    Certificate.Generated.H1_0B030.positive_semidefinite
  rw [multiplier_identification]
  exact Certificate.MultiplierProofs.M030.nonnegative x hroot hregion
#print axioms nonnegative
end Certificate.Assembly.H1_0B030
namespace Certificate.Assembly.H1_0B031
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem multiplier_identification : Certificate.SOS.H1_0B031.multiplier = Certificate.MultiplierProofs.M031.certificate.polynomial := by
  decide +kernel

/-- All new algebraic obligations are discharged; the remaining hypotheses describe the domain. -/
theorem nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x (scale Certificate.SOS.H1_0B031.weight Certificate.SOS.H1_0B031.weighted) := by
  have hroot : (x 7)^2=3 := by rw [hx]; exact Real.sq_sqrt (by norm_num)
  apply Certificate.SOS.H1_0B031.weighted_nonnegative x hx
    Certificate.Generated.H1_0B031.positive_semidefinite
  rw [multiplier_identification]
  exact Certificate.MultiplierProofs.M031.nonnegative x hroot hregion
#print axioms nonnegative
end Certificate.Assembly.H1_0B031
namespace Certificate.Assembly.H1_0B032
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem multiplier_identification : Certificate.SOS.H1_0B032.multiplier = Certificate.MultiplierProofs.M032.certificate.polynomial := by
  decide +kernel

/-- All new algebraic obligations are discharged; the remaining hypotheses describe the domain. -/
theorem nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x (scale Certificate.SOS.H1_0B032.weight Certificate.SOS.H1_0B032.weighted) := by
  have hroot : (x 7)^2=3 := by rw [hx]; exact Real.sq_sqrt (by norm_num)
  apply Certificate.SOS.H1_0B032.weighted_nonnegative x hx
    Certificate.Generated.H1_0B032.positive_semidefinite
  rw [multiplier_identification]
  exact Certificate.MultiplierProofs.M032.nonnegative x hroot hregion
#print axioms nonnegative
end Certificate.Assembly.H1_0B032
namespace Certificate.Assembly.H1_0B033
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem multiplier_identification : Certificate.SOS.H1_0B033.multiplier = Certificate.MultiplierProofs.M033.certificate.polynomial := by
  decide +kernel

/-- All new algebraic obligations are discharged; the remaining hypotheses describe the domain. -/
theorem nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x (scale Certificate.SOS.H1_0B033.weight Certificate.SOS.H1_0B033.weighted) := by
  have hroot : (x 7)^2=3 := by rw [hx]; exact Real.sq_sqrt (by norm_num)
  apply Certificate.SOS.H1_0B033.weighted_nonnegative x hx
    Certificate.Generated.H1_0B033.positive_semidefinite
  rw [multiplier_identification]
  exact Certificate.MultiplierProofs.M033.nonnegative x hroot hregion
#print axioms nonnegative
end Certificate.Assembly.H1_0B033
namespace Certificate.Assembly.H1_0B034
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem multiplier_identification : Certificate.SOS.H1_0B034.multiplier = Certificate.MultiplierProofs.M034.certificate.polynomial := by
  decide +kernel

/-- All new algebraic obligations are discharged; the remaining hypotheses describe the domain. -/
theorem nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x (scale Certificate.SOS.H1_0B034.weight Certificate.SOS.H1_0B034.weighted) := by
  have hroot : (x 7)^2=3 := by rw [hx]; exact Real.sq_sqrt (by norm_num)
  apply Certificate.SOS.H1_0B034.weighted_nonnegative x hx
    Certificate.Generated.H1_0B034.positive_semidefinite
  rw [multiplier_identification]
  exact Certificate.MultiplierProofs.M034.nonnegative x hroot hregion
#print axioms nonnegative
end Certificate.Assembly.H1_0B034
namespace Certificate.Assembly.H1_0B035
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem multiplier_identification : Certificate.SOS.H1_0B035.multiplier = Certificate.MultiplierProofs.M035.certificate.polynomial := by
  decide +kernel

/-- All new algebraic obligations are discharged; the remaining hypotheses describe the domain. -/
theorem nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x (scale Certificate.SOS.H1_0B035.weight Certificate.SOS.H1_0B035.weighted) := by
  have hroot : (x 7)^2=3 := by rw [hx]; exact Real.sq_sqrt (by norm_num)
  apply Certificate.SOS.H1_0B035.weighted_nonnegative x hx
    Certificate.Generated.H1_0B035.positive_semidefinite
  rw [multiplier_identification]
  exact Certificate.MultiplierProofs.M035.nonnegative x hroot hregion
#print axioms nonnegative
end Certificate.Assembly.H1_0B035
namespace Certificate.Assembly.H1_0B036
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem multiplier_identification : Certificate.SOS.H1_0B036.multiplier = Certificate.MultiplierProofs.M036.certificate.polynomial := by
  decide +kernel

/-- All new algebraic obligations are discharged; the remaining hypotheses describe the domain. -/
theorem nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x (scale Certificate.SOS.H1_0B036.weight Certificate.SOS.H1_0B036.weighted) := by
  have hroot : (x 7)^2=3 := by rw [hx]; exact Real.sq_sqrt (by norm_num)
  apply Certificate.SOS.H1_0B036.weighted_nonnegative x hx
    Certificate.Generated.H1_0B036.positive_semidefinite
  rw [multiplier_identification]
  exact Certificate.MultiplierProofs.M036.nonnegative x hroot hregion
#print axioms nonnegative
end Certificate.Assembly.H1_0B036
namespace Certificate.Assembly.H1_0B037
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem multiplier_identification : Certificate.SOS.H1_0B037.multiplier = Certificate.MultiplierProofs.M037.certificate.polynomial := by
  decide +kernel

/-- All new algebraic obligations are discharged; the remaining hypotheses describe the domain. -/
theorem nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x (scale Certificate.SOS.H1_0B037.weight Certificate.SOS.H1_0B037.weighted) := by
  have hroot : (x 7)^2=3 := by rw [hx]; exact Real.sq_sqrt (by norm_num)
  apply Certificate.SOS.H1_0B037.weighted_nonnegative x hx
    Certificate.Generated.H1_0B037.positive_semidefinite
  rw [multiplier_identification]
  exact Certificate.MultiplierProofs.M037.nonnegative x hroot hregion
#print axioms nonnegative
end Certificate.Assembly.H1_0B037
namespace Certificate.Assembly.H1_0B038
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem multiplier_identification : Certificate.SOS.H1_0B038.multiplier = Certificate.MultiplierProofs.M038.certificate.polynomial := by
  decide +kernel

/-- All new algebraic obligations are discharged; the remaining hypotheses describe the domain. -/
theorem nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x (scale Certificate.SOS.H1_0B038.weight Certificate.SOS.H1_0B038.weighted) := by
  have hroot : (x 7)^2=3 := by rw [hx]; exact Real.sq_sqrt (by norm_num)
  apply Certificate.SOS.H1_0B038.weighted_nonnegative x hx
    Certificate.Generated.H1_0B038.positive_semidefinite
  rw [multiplier_identification]
  exact Certificate.MultiplierProofs.M038.nonnegative x hroot hregion
#print axioms nonnegative
end Certificate.Assembly.H1_0B038
namespace Certificate.Assembly.H1_0B039
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem multiplier_identification : Certificate.SOS.H1_0B039.multiplier = Certificate.MultiplierProofs.M039.certificate.polynomial := by
  decide +kernel

/-- All new algebraic obligations are discharged; the remaining hypotheses describe the domain. -/
theorem nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x (scale Certificate.SOS.H1_0B039.weight Certificate.SOS.H1_0B039.weighted) := by
  have hroot : (x 7)^2=3 := by rw [hx]; exact Real.sq_sqrt (by norm_num)
  apply Certificate.SOS.H1_0B039.weighted_nonnegative x hx
    Certificate.Generated.H1_0B039.positive_semidefinite
  rw [multiplier_identification]
  exact Certificate.MultiplierProofs.M039.nonnegative x hroot hregion
#print axioms nonnegative
end Certificate.Assembly.H1_0B039
namespace Certificate.Assembly.H1_0B040
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem multiplier_identification : Certificate.SOS.H1_0B040.multiplier = Certificate.MultiplierProofs.M040.certificate.polynomial := by
  decide +kernel

/-- All new algebraic obligations are discharged; the remaining hypotheses describe the domain. -/
theorem nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x (scale Certificate.SOS.H1_0B040.weight Certificate.SOS.H1_0B040.weighted) := by
  have hroot : (x 7)^2=3 := by rw [hx]; exact Real.sq_sqrt (by norm_num)
  apply Certificate.SOS.H1_0B040.weighted_nonnegative x hx
    Certificate.Generated.H1_0B040.positive_semidefinite
  rw [multiplier_identification]
  exact Certificate.MultiplierProofs.M040.nonnegative x hroot hregion
#print axioms nonnegative
end Certificate.Assembly.H1_0B040
namespace Certificate.Assembly.H1_0B041
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem multiplier_identification : Certificate.SOS.H1_0B041.multiplier = Certificate.MultiplierProofs.M041.certificate.polynomial := by
  decide +kernel

/-- All new algebraic obligations are discharged; the remaining hypotheses describe the domain. -/
theorem nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x (scale Certificate.SOS.H1_0B041.weight Certificate.SOS.H1_0B041.weighted) := by
  have hroot : (x 7)^2=3 := by rw [hx]; exact Real.sq_sqrt (by norm_num)
  apply Certificate.SOS.H1_0B041.weighted_nonnegative x hx
    Certificate.Generated.H1_0B041.positive_semidefinite
  rw [multiplier_identification]
  exact Certificate.MultiplierProofs.M041.nonnegative x hroot hregion
#print axioms nonnegative
end Certificate.Assembly.H1_0B041
namespace Certificate.Assembly.H1_0B042
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem multiplier_identification : Certificate.SOS.H1_0B042.multiplier = Certificate.MultiplierProofs.M042.certificate.polynomial := by
  decide +kernel

/-- All new algebraic obligations are discharged; the remaining hypotheses describe the domain. -/
theorem nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x (scale Certificate.SOS.H1_0B042.weight Certificate.SOS.H1_0B042.weighted) := by
  have hroot : (x 7)^2=3 := by rw [hx]; exact Real.sq_sqrt (by norm_num)
  apply Certificate.SOS.H1_0B042.weighted_nonnegative x hx
    Certificate.Generated.H1_0B042.positive_semidefinite
  rw [multiplier_identification]
  exact Certificate.MultiplierProofs.M042.nonnegative x hroot hregion
#print axioms nonnegative
end Certificate.Assembly.H1_0B042
namespace Certificate.Assembly.H1_0B043
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem multiplier_identification : Certificate.SOS.H1_0B043.multiplier = Certificate.MultiplierProofs.M043.certificate.polynomial := by
  decide +kernel

/-- All new algebraic obligations are discharged; the remaining hypotheses describe the domain. -/
theorem nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x (scale Certificate.SOS.H1_0B043.weight Certificate.SOS.H1_0B043.weighted) := by
  have hroot : (x 7)^2=3 := by rw [hx]; exact Real.sq_sqrt (by norm_num)
  apply Certificate.SOS.H1_0B043.weighted_nonnegative x hx
    Certificate.Generated.H1_0B043.positive_semidefinite
  rw [multiplier_identification]
  exact Certificate.MultiplierProofs.M043.nonnegative x hroot hregion
#print axioms nonnegative
end Certificate.Assembly.H1_0B043
namespace Certificate.Assembly.H1_0B044
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem multiplier_identification : Certificate.SOS.H1_0B044.multiplier = Certificate.MultiplierProofs.M044.certificate.polynomial := by
  decide +kernel

/-- All new algebraic obligations are discharged; the remaining hypotheses describe the domain. -/
theorem nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x (scale Certificate.SOS.H1_0B044.weight Certificate.SOS.H1_0B044.weighted) := by
  have hroot : (x 7)^2=3 := by rw [hx]; exact Real.sq_sqrt (by norm_num)
  apply Certificate.SOS.H1_0B044.weighted_nonnegative x hx
    Certificate.Generated.H1_0B044.positive_semidefinite
  rw [multiplier_identification]
  exact Certificate.MultiplierProofs.M044.nonnegative x hroot hregion
#print axioms nonnegative
end Certificate.Assembly.H1_0B044
namespace Certificate.Assembly.H1_0B045
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem multiplier_identification : Certificate.SOS.H1_0B045.multiplier = Certificate.MultiplierProofs.M045.certificate.polynomial := by
  decide +kernel

/-- All new algebraic obligations are discharged; the remaining hypotheses describe the domain. -/
theorem nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x (scale Certificate.SOS.H1_0B045.weight Certificate.SOS.H1_0B045.weighted) := by
  have hroot : (x 7)^2=3 := by rw [hx]; exact Real.sq_sqrt (by norm_num)
  apply Certificate.SOS.H1_0B045.weighted_nonnegative x hx
    Certificate.Generated.H1_0B045.positive_semidefinite
  rw [multiplier_identification]
  exact Certificate.MultiplierProofs.M045.nonnegative x hroot hregion
#print axioms nonnegative
end Certificate.Assembly.H1_0B045
namespace Certificate.Assembly.H1_0B046
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem multiplier_identification : Certificate.SOS.H1_0B046.multiplier = Certificate.MultiplierProofs.M046.certificate.polynomial := by
  decide +kernel

/-- All new algebraic obligations are discharged; the remaining hypotheses describe the domain. -/
theorem nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x (scale Certificate.SOS.H1_0B046.weight Certificate.SOS.H1_0B046.weighted) := by
  have hroot : (x 7)^2=3 := by rw [hx]; exact Real.sq_sqrt (by norm_num)
  apply Certificate.SOS.H1_0B046.weighted_nonnegative x hx
    Certificate.Generated.H1_0B046.positive_semidefinite
  rw [multiplier_identification]
  exact Certificate.MultiplierProofs.M046.nonnegative x hroot hregion
#print axioms nonnegative
end Certificate.Assembly.H1_0B046
namespace Certificate.Assembly.H1_0B047
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem multiplier_identification : Certificate.SOS.H1_0B047.multiplier = Certificate.MultiplierProofs.M047.certificate.polynomial := by
  decide +kernel

/-- All new algebraic obligations are discharged; the remaining hypotheses describe the domain. -/
theorem nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x (scale Certificate.SOS.H1_0B047.weight Certificate.SOS.H1_0B047.weighted) := by
  have hroot : (x 7)^2=3 := by rw [hx]; exact Real.sq_sqrt (by norm_num)
  apply Certificate.SOS.H1_0B047.weighted_nonnegative x hx
    Certificate.Generated.H1_0B047.positive_semidefinite
  rw [multiplier_identification]
  exact Certificate.MultiplierProofs.M047.nonnegative x hroot hregion
#print axioms nonnegative
end Certificate.Assembly.H1_0B047
namespace Certificate.Assembly.H1_0B048
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem multiplier_identification : Certificate.SOS.H1_0B048.multiplier = Certificate.MultiplierProofs.M048.certificate.polynomial := by
  decide +kernel

/-- All new algebraic obligations are discharged; the remaining hypotheses describe the domain. -/
theorem nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x (scale Certificate.SOS.H1_0B048.weight Certificate.SOS.H1_0B048.weighted) := by
  have hroot : (x 7)^2=3 := by rw [hx]; exact Real.sq_sqrt (by norm_num)
  apply Certificate.SOS.H1_0B048.weighted_nonnegative x hx
    Certificate.Generated.H1_0B048.positive_semidefinite
  rw [multiplier_identification]
  exact Certificate.MultiplierProofs.M048.nonnegative x hroot hregion
#print axioms nonnegative
end Certificate.Assembly.H1_0B048
namespace Certificate.Assembly.H1_0B049
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem multiplier_identification : Certificate.SOS.H1_0B049.multiplier = Certificate.MultiplierProofs.M049.certificate.polynomial := by
  decide +kernel

/-- All new algebraic obligations are discharged; the remaining hypotheses describe the domain. -/
theorem nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x (scale Certificate.SOS.H1_0B049.weight Certificate.SOS.H1_0B049.weighted) := by
  have hroot : (x 7)^2=3 := by rw [hx]; exact Real.sq_sqrt (by norm_num)
  apply Certificate.SOS.H1_0B049.weighted_nonnegative x hx
    Certificate.Generated.H1_0B049.positive_semidefinite
  rw [multiplier_identification]
  exact Certificate.MultiplierProofs.M049.nonnegative x hroot hregion
#print axioms nonnegative
end Certificate.Assembly.H1_0B049
