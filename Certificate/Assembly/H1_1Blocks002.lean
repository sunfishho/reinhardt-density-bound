import Certificate.Generated.H1_1B050Proof
import Certificate.Generated.H1_1B051Proof
import Certificate.Generated.H1_1B052Proof
import Certificate.Generated.H1_1B053Proof
import Certificate.Generated.H1_1B054Proof
import Certificate.Generated.H1_1B055Proof
import Certificate.Generated.H1_1B056Proof
import Certificate.Generated.H1_1B057Proof
import Certificate.Generated.H1_1B058Proof
import Certificate.Generated.H1_1B059Proof
import Certificate.Generated.H1_1B060Proof
import Certificate.Generated.H1_1B061Proof
import Certificate.Generated.H1_1B062Proof
import Certificate.Generated.H1_1B063Proof
import Certificate.Generated.H1_1B064Proof
import Certificate.Generated.H1_1B065Proof
import Certificate.Generated.H1_1B066Proof
import Certificate.Generated.H1_1B067Proof
import Certificate.Generated.H1_1B068Proof
import Certificate.Generated.H1_1B069Proof
import Certificate.Generated.H1_1B070Proof
import Certificate.Generated.H1_1B071Proof
import Certificate.Generated.H1_1B072Proof
import Certificate.Generated.H1_1B073Proof
import Certificate.Generated.H1_1B074Proof
import Certificate.MultiplierCertificates
import Certificate.SOS.H1_1B050Proof
import Certificate.SOS.H1_1B051Proof
import Certificate.SOS.H1_1B052Proof
import Certificate.SOS.H1_1B053Proof
import Certificate.SOS.H1_1B054Proof
import Certificate.SOS.H1_1B055Proof
import Certificate.SOS.H1_1B056Proof
import Certificate.SOS.H1_1B057Proof
import Certificate.SOS.H1_1B058Proof
import Certificate.SOS.H1_1B059Proof
import Certificate.SOS.H1_1B060Proof
import Certificate.SOS.H1_1B061Proof
import Certificate.SOS.H1_1B062Proof
import Certificate.SOS.H1_1B063Proof
import Certificate.SOS.H1_1B064Proof
import Certificate.SOS.H1_1B065Proof
import Certificate.SOS.H1_1B066Proof
import Certificate.SOS.H1_1B067Proof
import Certificate.SOS.H1_1B068Proof
import Certificate.SOS.H1_1B069Proof
import Certificate.SOS.H1_1B070Proof
import Certificate.SOS.H1_1B071Proof
import Certificate.SOS.H1_1B072Proof
import Certificate.SOS.H1_1B073Proof
import Certificate.SOS.H1_1B074Proof
namespace Certificate.Assembly.H1_1B050
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem multiplier_identification : Certificate.SOS.H1_1B050.multiplier = Certificate.MultiplierProofs.M050.certificate.polynomial := by
  decide +kernel

/-- All new algebraic obligations are discharged; the remaining hypotheses describe the domain. -/
theorem nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x (scale Certificate.SOS.H1_1B050.weight Certificate.SOS.H1_1B050.weighted) := by
  have hroot : (x 7)^2=3 := by rw [hx]; exact Real.sq_sqrt (by norm_num)
  apply Certificate.SOS.H1_1B050.weighted_nonnegative x hx
    Certificate.Generated.H1_1B050.positive_semidefinite
  rw [multiplier_identification]
  exact Certificate.MultiplierProofs.M050.nonnegative x hroot hregion
#print axioms nonnegative
end Certificate.Assembly.H1_1B050
namespace Certificate.Assembly.H1_1B051
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem multiplier_identification : Certificate.SOS.H1_1B051.multiplier = Certificate.MultiplierProofs.M051.certificate.polynomial := by
  decide +kernel

/-- All new algebraic obligations are discharged; the remaining hypotheses describe the domain. -/
theorem nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x (scale Certificate.SOS.H1_1B051.weight Certificate.SOS.H1_1B051.weighted) := by
  have hroot : (x 7)^2=3 := by rw [hx]; exact Real.sq_sqrt (by norm_num)
  apply Certificate.SOS.H1_1B051.weighted_nonnegative x hx
    Certificate.Generated.H1_1B051.positive_semidefinite
  rw [multiplier_identification]
  exact Certificate.MultiplierProofs.M051.nonnegative x hroot hregion
#print axioms nonnegative
end Certificate.Assembly.H1_1B051
namespace Certificate.Assembly.H1_1B052
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem multiplier_identification : Certificate.SOS.H1_1B052.multiplier = Certificate.MultiplierProofs.M052.certificate.polynomial := by
  decide +kernel

/-- All new algebraic obligations are discharged; the remaining hypotheses describe the domain. -/
theorem nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x (scale Certificate.SOS.H1_1B052.weight Certificate.SOS.H1_1B052.weighted) := by
  have hroot : (x 7)^2=3 := by rw [hx]; exact Real.sq_sqrt (by norm_num)
  apply Certificate.SOS.H1_1B052.weighted_nonnegative x hx
    Certificate.Generated.H1_1B052.positive_semidefinite
  rw [multiplier_identification]
  exact Certificate.MultiplierProofs.M052.nonnegative x hroot hregion
#print axioms nonnegative
end Certificate.Assembly.H1_1B052
namespace Certificate.Assembly.H1_1B053
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem multiplier_identification : Certificate.SOS.H1_1B053.multiplier = Certificate.MultiplierProofs.M053.certificate.polynomial := by
  decide +kernel

/-- All new algebraic obligations are discharged; the remaining hypotheses describe the domain. -/
theorem nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x (scale Certificate.SOS.H1_1B053.weight Certificate.SOS.H1_1B053.weighted) := by
  have hroot : (x 7)^2=3 := by rw [hx]; exact Real.sq_sqrt (by norm_num)
  apply Certificate.SOS.H1_1B053.weighted_nonnegative x hx
    Certificate.Generated.H1_1B053.positive_semidefinite
  rw [multiplier_identification]
  exact Certificate.MultiplierProofs.M053.nonnegative x hroot hregion
#print axioms nonnegative
end Certificate.Assembly.H1_1B053
namespace Certificate.Assembly.H1_1B054
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem multiplier_identification : Certificate.SOS.H1_1B054.multiplier = Certificate.MultiplierProofs.M054.certificate.polynomial := by
  decide +kernel

/-- All new algebraic obligations are discharged; the remaining hypotheses describe the domain. -/
theorem nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x (scale Certificate.SOS.H1_1B054.weight Certificate.SOS.H1_1B054.weighted) := by
  have hroot : (x 7)^2=3 := by rw [hx]; exact Real.sq_sqrt (by norm_num)
  apply Certificate.SOS.H1_1B054.weighted_nonnegative x hx
    Certificate.Generated.H1_1B054.positive_semidefinite
  rw [multiplier_identification]
  exact Certificate.MultiplierProofs.M054.nonnegative x hroot hregion
#print axioms nonnegative
end Certificate.Assembly.H1_1B054
namespace Certificate.Assembly.H1_1B055
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem multiplier_identification : Certificate.SOS.H1_1B055.multiplier = Certificate.MultiplierProofs.M055.certificate.polynomial := by
  decide +kernel

/-- All new algebraic obligations are discharged; the remaining hypotheses describe the domain. -/
theorem nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x (scale Certificate.SOS.H1_1B055.weight Certificate.SOS.H1_1B055.weighted) := by
  have hroot : (x 7)^2=3 := by rw [hx]; exact Real.sq_sqrt (by norm_num)
  apply Certificate.SOS.H1_1B055.weighted_nonnegative x hx
    Certificate.Generated.H1_1B055.positive_semidefinite
  rw [multiplier_identification]
  exact Certificate.MultiplierProofs.M055.nonnegative x hroot hregion
#print axioms nonnegative
end Certificate.Assembly.H1_1B055
namespace Certificate.Assembly.H1_1B056
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem multiplier_identification : Certificate.SOS.H1_1B056.multiplier = Certificate.MultiplierProofs.M056.certificate.polynomial := by
  decide +kernel

/-- All new algebraic obligations are discharged; the remaining hypotheses describe the domain. -/
theorem nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x (scale Certificate.SOS.H1_1B056.weight Certificate.SOS.H1_1B056.weighted) := by
  have hroot : (x 7)^2=3 := by rw [hx]; exact Real.sq_sqrt (by norm_num)
  apply Certificate.SOS.H1_1B056.weighted_nonnegative x hx
    Certificate.Generated.H1_1B056.positive_semidefinite
  rw [multiplier_identification]
  exact Certificate.MultiplierProofs.M056.nonnegative x hroot hregion
#print axioms nonnegative
end Certificate.Assembly.H1_1B056
namespace Certificate.Assembly.H1_1B057
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem multiplier_identification : Certificate.SOS.H1_1B057.multiplier = Certificate.MultiplierProofs.M057.certificate.polynomial := by
  decide +kernel

/-- All new algebraic obligations are discharged; the remaining hypotheses describe the domain. -/
theorem nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x (scale Certificate.SOS.H1_1B057.weight Certificate.SOS.H1_1B057.weighted) := by
  have hroot : (x 7)^2=3 := by rw [hx]; exact Real.sq_sqrt (by norm_num)
  apply Certificate.SOS.H1_1B057.weighted_nonnegative x hx
    Certificate.Generated.H1_1B057.positive_semidefinite
  rw [multiplier_identification]
  exact Certificate.MultiplierProofs.M057.nonnegative x hroot hregion
#print axioms nonnegative
end Certificate.Assembly.H1_1B057
namespace Certificate.Assembly.H1_1B058
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem multiplier_identification : Certificate.SOS.H1_1B058.multiplier = Certificate.MultiplierProofs.M058.certificate.polynomial := by
  decide +kernel

/-- All new algebraic obligations are discharged; the remaining hypotheses describe the domain. -/
theorem nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x (scale Certificate.SOS.H1_1B058.weight Certificate.SOS.H1_1B058.weighted) := by
  have hroot : (x 7)^2=3 := by rw [hx]; exact Real.sq_sqrt (by norm_num)
  apply Certificate.SOS.H1_1B058.weighted_nonnegative x hx
    Certificate.Generated.H1_1B058.positive_semidefinite
  rw [multiplier_identification]
  exact Certificate.MultiplierProofs.M058.nonnegative x hroot hregion
#print axioms nonnegative
end Certificate.Assembly.H1_1B058
namespace Certificate.Assembly.H1_1B059
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem multiplier_identification : Certificate.SOS.H1_1B059.multiplier = Certificate.MultiplierProofs.M059.certificate.polynomial := by
  decide +kernel

/-- All new algebraic obligations are discharged; the remaining hypotheses describe the domain. -/
theorem nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x (scale Certificate.SOS.H1_1B059.weight Certificate.SOS.H1_1B059.weighted) := by
  have hroot : (x 7)^2=3 := by rw [hx]; exact Real.sq_sqrt (by norm_num)
  apply Certificate.SOS.H1_1B059.weighted_nonnegative x hx
    Certificate.Generated.H1_1B059.positive_semidefinite
  rw [multiplier_identification]
  exact Certificate.MultiplierProofs.M059.nonnegative x hroot hregion
#print axioms nonnegative
end Certificate.Assembly.H1_1B059
namespace Certificate.Assembly.H1_1B060
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem multiplier_identification : Certificate.SOS.H1_1B060.multiplier = Certificate.MultiplierProofs.M060.certificate.polynomial := by
  decide +kernel

/-- All new algebraic obligations are discharged; the remaining hypotheses describe the domain. -/
theorem nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x (scale Certificate.SOS.H1_1B060.weight Certificate.SOS.H1_1B060.weighted) := by
  have hroot : (x 7)^2=3 := by rw [hx]; exact Real.sq_sqrt (by norm_num)
  apply Certificate.SOS.H1_1B060.weighted_nonnegative x hx
    Certificate.Generated.H1_1B060.positive_semidefinite
  rw [multiplier_identification]
  exact Certificate.MultiplierProofs.M060.nonnegative x hroot hregion
#print axioms nonnegative
end Certificate.Assembly.H1_1B060
namespace Certificate.Assembly.H1_1B061
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem multiplier_identification : Certificate.SOS.H1_1B061.multiplier = Certificate.MultiplierProofs.M061.certificate.polynomial := by
  decide +kernel

/-- All new algebraic obligations are discharged; the remaining hypotheses describe the domain. -/
theorem nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x (scale Certificate.SOS.H1_1B061.weight Certificate.SOS.H1_1B061.weighted) := by
  have hroot : (x 7)^2=3 := by rw [hx]; exact Real.sq_sqrt (by norm_num)
  apply Certificate.SOS.H1_1B061.weighted_nonnegative x hx
    Certificate.Generated.H1_1B061.positive_semidefinite
  rw [multiplier_identification]
  exact Certificate.MultiplierProofs.M061.nonnegative x hroot hregion
#print axioms nonnegative
end Certificate.Assembly.H1_1B061
namespace Certificate.Assembly.H1_1B062
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem multiplier_identification : Certificate.SOS.H1_1B062.multiplier = Certificate.MultiplierProofs.M062.certificate.polynomial := by
  decide +kernel

/-- All new algebraic obligations are discharged; the remaining hypotheses describe the domain. -/
theorem nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x (scale Certificate.SOS.H1_1B062.weight Certificate.SOS.H1_1B062.weighted) := by
  have hroot : (x 7)^2=3 := by rw [hx]; exact Real.sq_sqrt (by norm_num)
  apply Certificate.SOS.H1_1B062.weighted_nonnegative x hx
    Certificate.Generated.H1_1B062.positive_semidefinite
  rw [multiplier_identification]
  exact Certificate.MultiplierProofs.M062.nonnegative x hroot hregion
#print axioms nonnegative
end Certificate.Assembly.H1_1B062
namespace Certificate.Assembly.H1_1B063
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem multiplier_identification : Certificate.SOS.H1_1B063.multiplier = Certificate.MultiplierProofs.M063.certificate.polynomial := by
  decide +kernel

/-- All new algebraic obligations are discharged; the remaining hypotheses describe the domain. -/
theorem nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x (scale Certificate.SOS.H1_1B063.weight Certificate.SOS.H1_1B063.weighted) := by
  have hroot : (x 7)^2=3 := by rw [hx]; exact Real.sq_sqrt (by norm_num)
  apply Certificate.SOS.H1_1B063.weighted_nonnegative x hx
    Certificate.Generated.H1_1B063.positive_semidefinite
  rw [multiplier_identification]
  exact Certificate.MultiplierProofs.M063.nonnegative x hroot hregion
#print axioms nonnegative
end Certificate.Assembly.H1_1B063
namespace Certificate.Assembly.H1_1B064
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem multiplier_identification : Certificate.SOS.H1_1B064.multiplier = Certificate.MultiplierProofs.M064.certificate.polynomial := by
  decide +kernel

/-- All new algebraic obligations are discharged; the remaining hypotheses describe the domain. -/
theorem nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x (scale Certificate.SOS.H1_1B064.weight Certificate.SOS.H1_1B064.weighted) := by
  have hroot : (x 7)^2=3 := by rw [hx]; exact Real.sq_sqrt (by norm_num)
  apply Certificate.SOS.H1_1B064.weighted_nonnegative x hx
    Certificate.Generated.H1_1B064.positive_semidefinite
  rw [multiplier_identification]
  exact Certificate.MultiplierProofs.M064.nonnegative x hroot hregion
#print axioms nonnegative
end Certificate.Assembly.H1_1B064
namespace Certificate.Assembly.H1_1B065
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem multiplier_identification : Certificate.SOS.H1_1B065.multiplier = Certificate.MultiplierProofs.M065.certificate.polynomial := by
  decide +kernel

/-- All new algebraic obligations are discharged; the remaining hypotheses describe the domain. -/
theorem nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x (scale Certificate.SOS.H1_1B065.weight Certificate.SOS.H1_1B065.weighted) := by
  have hroot : (x 7)^2=3 := by rw [hx]; exact Real.sq_sqrt (by norm_num)
  apply Certificate.SOS.H1_1B065.weighted_nonnegative x hx
    Certificate.Generated.H1_1B065.positive_semidefinite
  rw [multiplier_identification]
  exact Certificate.MultiplierProofs.M065.nonnegative x hroot hregion
#print axioms nonnegative
end Certificate.Assembly.H1_1B065
namespace Certificate.Assembly.H1_1B066
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem multiplier_identification : Certificate.SOS.H1_1B066.multiplier = Certificate.MultiplierProofs.M066.certificate.polynomial := by
  decide +kernel

/-- All new algebraic obligations are discharged; the remaining hypotheses describe the domain. -/
theorem nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x (scale Certificate.SOS.H1_1B066.weight Certificate.SOS.H1_1B066.weighted) := by
  have hroot : (x 7)^2=3 := by rw [hx]; exact Real.sq_sqrt (by norm_num)
  apply Certificate.SOS.H1_1B066.weighted_nonnegative x hx
    Certificate.Generated.H1_1B066.positive_semidefinite
  rw [multiplier_identification]
  exact Certificate.MultiplierProofs.M066.nonnegative x hroot hregion
#print axioms nonnegative
end Certificate.Assembly.H1_1B066
namespace Certificate.Assembly.H1_1B067
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem multiplier_identification : Certificate.SOS.H1_1B067.multiplier = Certificate.MultiplierProofs.M067.certificate.polynomial := by
  decide +kernel

/-- All new algebraic obligations are discharged; the remaining hypotheses describe the domain. -/
theorem nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x (scale Certificate.SOS.H1_1B067.weight Certificate.SOS.H1_1B067.weighted) := by
  have hroot : (x 7)^2=3 := by rw [hx]; exact Real.sq_sqrt (by norm_num)
  apply Certificate.SOS.H1_1B067.weighted_nonnegative x hx
    Certificate.Generated.H1_1B067.positive_semidefinite
  rw [multiplier_identification]
  exact Certificate.MultiplierProofs.M067.nonnegative x hroot hregion
#print axioms nonnegative
end Certificate.Assembly.H1_1B067
namespace Certificate.Assembly.H1_1B068
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem multiplier_identification : Certificate.SOS.H1_1B068.multiplier = Certificate.MultiplierProofs.M068.certificate.polynomial := by
  decide +kernel

/-- All new algebraic obligations are discharged; the remaining hypotheses describe the domain. -/
theorem nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x (scale Certificate.SOS.H1_1B068.weight Certificate.SOS.H1_1B068.weighted) := by
  have hroot : (x 7)^2=3 := by rw [hx]; exact Real.sq_sqrt (by norm_num)
  apply Certificate.SOS.H1_1B068.weighted_nonnegative x hx
    Certificate.Generated.H1_1B068.positive_semidefinite
  rw [multiplier_identification]
  exact Certificate.MultiplierProofs.M068.nonnegative x hroot hregion
#print axioms nonnegative
end Certificate.Assembly.H1_1B068
namespace Certificate.Assembly.H1_1B069
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem multiplier_identification : Certificate.SOS.H1_1B069.multiplier = Certificate.MultiplierProofs.M069.certificate.polynomial := by
  decide +kernel

/-- All new algebraic obligations are discharged; the remaining hypotheses describe the domain. -/
theorem nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x (scale Certificate.SOS.H1_1B069.weight Certificate.SOS.H1_1B069.weighted) := by
  have hroot : (x 7)^2=3 := by rw [hx]; exact Real.sq_sqrt (by norm_num)
  apply Certificate.SOS.H1_1B069.weighted_nonnegative x hx
    Certificate.Generated.H1_1B069.positive_semidefinite
  rw [multiplier_identification]
  exact Certificate.MultiplierProofs.M069.nonnegative x hroot hregion
#print axioms nonnegative
end Certificate.Assembly.H1_1B069
namespace Certificate.Assembly.H1_1B070
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem multiplier_identification : Certificate.SOS.H1_1B070.multiplier = Certificate.MultiplierProofs.M070.certificate.polynomial := by
  decide +kernel

/-- All new algebraic obligations are discharged; the remaining hypotheses describe the domain. -/
theorem nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x (scale Certificate.SOS.H1_1B070.weight Certificate.SOS.H1_1B070.weighted) := by
  have hroot : (x 7)^2=3 := by rw [hx]; exact Real.sq_sqrt (by norm_num)
  apply Certificate.SOS.H1_1B070.weighted_nonnegative x hx
    Certificate.Generated.H1_1B070.positive_semidefinite
  rw [multiplier_identification]
  exact Certificate.MultiplierProofs.M070.nonnegative x hroot hregion
#print axioms nonnegative
end Certificate.Assembly.H1_1B070
namespace Certificate.Assembly.H1_1B071
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem multiplier_identification : Certificate.SOS.H1_1B071.multiplier = Certificate.MultiplierProofs.M071.certificate.polynomial := by
  decide +kernel

/-- All new algebraic obligations are discharged; the remaining hypotheses describe the domain. -/
theorem nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x (scale Certificate.SOS.H1_1B071.weight Certificate.SOS.H1_1B071.weighted) := by
  have hroot : (x 7)^2=3 := by rw [hx]; exact Real.sq_sqrt (by norm_num)
  apply Certificate.SOS.H1_1B071.weighted_nonnegative x hx
    Certificate.Generated.H1_1B071.positive_semidefinite
  rw [multiplier_identification]
  exact Certificate.MultiplierProofs.M071.nonnegative x hroot hregion
#print axioms nonnegative
end Certificate.Assembly.H1_1B071
namespace Certificate.Assembly.H1_1B072
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem multiplier_identification : Certificate.SOS.H1_1B072.multiplier = Certificate.MultiplierProofs.M072.certificate.polynomial := by
  decide +kernel

/-- All new algebraic obligations are discharged; the remaining hypotheses describe the domain. -/
theorem nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x (scale Certificate.SOS.H1_1B072.weight Certificate.SOS.H1_1B072.weighted) := by
  have hroot : (x 7)^2=3 := by rw [hx]; exact Real.sq_sqrt (by norm_num)
  apply Certificate.SOS.H1_1B072.weighted_nonnegative x hx
    Certificate.Generated.H1_1B072.positive_semidefinite
  rw [multiplier_identification]
  exact Certificate.MultiplierProofs.M072.nonnegative x hroot hregion
#print axioms nonnegative
end Certificate.Assembly.H1_1B072
namespace Certificate.Assembly.H1_1B073
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem multiplier_identification : Certificate.SOS.H1_1B073.multiplier = Certificate.MultiplierProofs.M073.certificate.polynomial := by
  decide +kernel

/-- All new algebraic obligations are discharged; the remaining hypotheses describe the domain. -/
theorem nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x (scale Certificate.SOS.H1_1B073.weight Certificate.SOS.H1_1B073.weighted) := by
  have hroot : (x 7)^2=3 := by rw [hx]; exact Real.sq_sqrt (by norm_num)
  apply Certificate.SOS.H1_1B073.weighted_nonnegative x hx
    Certificate.Generated.H1_1B073.positive_semidefinite
  rw [multiplier_identification]
  exact Certificate.MultiplierProofs.M073.nonnegative x hroot hregion
#print axioms nonnegative
end Certificate.Assembly.H1_1B073
namespace Certificate.Assembly.H1_1B074
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem multiplier_identification : Certificate.SOS.H1_1B074.multiplier = Certificate.MultiplierProofs.M074.certificate.polynomial := by
  decide +kernel

/-- All new algebraic obligations are discharged; the remaining hypotheses describe the domain. -/
theorem nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x (scale Certificate.SOS.H1_1B074.weight Certificate.SOS.H1_1B074.weighted) := by
  have hroot : (x 7)^2=3 := by rw [hx]; exact Real.sq_sqrt (by norm_num)
  apply Certificate.SOS.H1_1B074.weighted_nonnegative x hx
    Certificate.Generated.H1_1B074.positive_semidefinite
  rw [multiplier_identification]
  exact Certificate.MultiplierProofs.M074.nonnegative x hroot hregion
#print axioms nonnegative
end Certificate.Assembly.H1_1B074
