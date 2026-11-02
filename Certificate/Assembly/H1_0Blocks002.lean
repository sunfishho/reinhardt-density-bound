import Certificate.Generated.H1_0B050Proof
import Certificate.Generated.H1_0B051Proof
import Certificate.Generated.H1_0B052Proof
import Certificate.Generated.H1_0B053Proof
import Certificate.Generated.H1_0B054Proof
import Certificate.Generated.H1_0B055Proof
import Certificate.Generated.H1_0B056Proof
import Certificate.Generated.H1_0B057Proof
import Certificate.Generated.H1_0B058Proof
import Certificate.Generated.H1_0B059Proof
import Certificate.Generated.H1_0B060Proof
import Certificate.Generated.H1_0B061Proof
import Certificate.Generated.H1_0B062Proof
import Certificate.Generated.H1_0B063Proof
import Certificate.Generated.H1_0B064Proof
import Certificate.Generated.H1_0B065Proof
import Certificate.Generated.H1_0B066Proof
import Certificate.Generated.H1_0B067Proof
import Certificate.Generated.H1_0B068Proof
import Certificate.Generated.H1_0B069Proof
import Certificate.Generated.H1_0B070Proof
import Certificate.Generated.H1_0B071Proof
import Certificate.Generated.H1_0B072Proof
import Certificate.Generated.H1_0B073Proof
import Certificate.Generated.H1_0B074Proof
import Certificate.MultiplierCertificates
import Certificate.SOS.H1_0B050Proof
import Certificate.SOS.H1_0B051Proof
import Certificate.SOS.H1_0B052Proof
import Certificate.SOS.H1_0B053Proof
import Certificate.SOS.H1_0B054Proof
import Certificate.SOS.H1_0B055Proof
import Certificate.SOS.H1_0B056Proof
import Certificate.SOS.H1_0B057Proof
import Certificate.SOS.H1_0B058Proof
import Certificate.SOS.H1_0B059Proof
import Certificate.SOS.H1_0B060Proof
import Certificate.SOS.H1_0B061Proof
import Certificate.SOS.H1_0B062Proof
import Certificate.SOS.H1_0B063Proof
import Certificate.SOS.H1_0B064Proof
import Certificate.SOS.H1_0B065Proof
import Certificate.SOS.H1_0B066Proof
import Certificate.SOS.H1_0B067Proof
import Certificate.SOS.H1_0B068Proof
import Certificate.SOS.H1_0B069Proof
import Certificate.SOS.H1_0B070Proof
import Certificate.SOS.H1_0B071Proof
import Certificate.SOS.H1_0B072Proof
import Certificate.SOS.H1_0B073Proof
import Certificate.SOS.H1_0B074Proof
namespace Certificate.Assembly.H1_0B050
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem multiplier_identification : Certificate.SOS.H1_0B050.multiplier = Certificate.MultiplierProofs.M050.certificate.polynomial := by
  decide +kernel

/-- All new algebraic obligations are discharged; the remaining hypotheses describe the domain. -/
theorem nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x (scale Certificate.SOS.H1_0B050.weight Certificate.SOS.H1_0B050.weighted) := by
  have hroot : (x 7)^2=3 := by rw [hx]; exact Real.sq_sqrt (by norm_num)
  apply Certificate.SOS.H1_0B050.weighted_nonnegative x hx
    Certificate.Generated.H1_0B050.positive_semidefinite
  rw [multiplier_identification]
  exact Certificate.MultiplierProofs.M050.nonnegative x hroot hregion
#print axioms nonnegative
end Certificate.Assembly.H1_0B050
namespace Certificate.Assembly.H1_0B051
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem multiplier_identification : Certificate.SOS.H1_0B051.multiplier = Certificate.MultiplierProofs.M051.certificate.polynomial := by
  decide +kernel

/-- All new algebraic obligations are discharged; the remaining hypotheses describe the domain. -/
theorem nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x (scale Certificate.SOS.H1_0B051.weight Certificate.SOS.H1_0B051.weighted) := by
  have hroot : (x 7)^2=3 := by rw [hx]; exact Real.sq_sqrt (by norm_num)
  apply Certificate.SOS.H1_0B051.weighted_nonnegative x hx
    Certificate.Generated.H1_0B051.positive_semidefinite
  rw [multiplier_identification]
  exact Certificate.MultiplierProofs.M051.nonnegative x hroot hregion
#print axioms nonnegative
end Certificate.Assembly.H1_0B051
namespace Certificate.Assembly.H1_0B052
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem multiplier_identification : Certificate.SOS.H1_0B052.multiplier = Certificate.MultiplierProofs.M052.certificate.polynomial := by
  decide +kernel

/-- All new algebraic obligations are discharged; the remaining hypotheses describe the domain. -/
theorem nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x (scale Certificate.SOS.H1_0B052.weight Certificate.SOS.H1_0B052.weighted) := by
  have hroot : (x 7)^2=3 := by rw [hx]; exact Real.sq_sqrt (by norm_num)
  apply Certificate.SOS.H1_0B052.weighted_nonnegative x hx
    Certificate.Generated.H1_0B052.positive_semidefinite
  rw [multiplier_identification]
  exact Certificate.MultiplierProofs.M052.nonnegative x hroot hregion
#print axioms nonnegative
end Certificate.Assembly.H1_0B052
namespace Certificate.Assembly.H1_0B053
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem multiplier_identification : Certificate.SOS.H1_0B053.multiplier = Certificate.MultiplierProofs.M053.certificate.polynomial := by
  decide +kernel

/-- All new algebraic obligations are discharged; the remaining hypotheses describe the domain. -/
theorem nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x (scale Certificate.SOS.H1_0B053.weight Certificate.SOS.H1_0B053.weighted) := by
  have hroot : (x 7)^2=3 := by rw [hx]; exact Real.sq_sqrt (by norm_num)
  apply Certificate.SOS.H1_0B053.weighted_nonnegative x hx
    Certificate.Generated.H1_0B053.positive_semidefinite
  rw [multiplier_identification]
  exact Certificate.MultiplierProofs.M053.nonnegative x hroot hregion
#print axioms nonnegative
end Certificate.Assembly.H1_0B053
namespace Certificate.Assembly.H1_0B054
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem multiplier_identification : Certificate.SOS.H1_0B054.multiplier = Certificate.MultiplierProofs.M054.certificate.polynomial := by
  decide +kernel

/-- All new algebraic obligations are discharged; the remaining hypotheses describe the domain. -/
theorem nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x (scale Certificate.SOS.H1_0B054.weight Certificate.SOS.H1_0B054.weighted) := by
  have hroot : (x 7)^2=3 := by rw [hx]; exact Real.sq_sqrt (by norm_num)
  apply Certificate.SOS.H1_0B054.weighted_nonnegative x hx
    Certificate.Generated.H1_0B054.positive_semidefinite
  rw [multiplier_identification]
  exact Certificate.MultiplierProofs.M054.nonnegative x hroot hregion
#print axioms nonnegative
end Certificate.Assembly.H1_0B054
namespace Certificate.Assembly.H1_0B055
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem multiplier_identification : Certificate.SOS.H1_0B055.multiplier = Certificate.MultiplierProofs.M055.certificate.polynomial := by
  decide +kernel

/-- All new algebraic obligations are discharged; the remaining hypotheses describe the domain. -/
theorem nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x (scale Certificate.SOS.H1_0B055.weight Certificate.SOS.H1_0B055.weighted) := by
  have hroot : (x 7)^2=3 := by rw [hx]; exact Real.sq_sqrt (by norm_num)
  apply Certificate.SOS.H1_0B055.weighted_nonnegative x hx
    Certificate.Generated.H1_0B055.positive_semidefinite
  rw [multiplier_identification]
  exact Certificate.MultiplierProofs.M055.nonnegative x hroot hregion
#print axioms nonnegative
end Certificate.Assembly.H1_0B055
namespace Certificate.Assembly.H1_0B056
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem multiplier_identification : Certificate.SOS.H1_0B056.multiplier = Certificate.MultiplierProofs.M056.certificate.polynomial := by
  decide +kernel

/-- All new algebraic obligations are discharged; the remaining hypotheses describe the domain. -/
theorem nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x (scale Certificate.SOS.H1_0B056.weight Certificate.SOS.H1_0B056.weighted) := by
  have hroot : (x 7)^2=3 := by rw [hx]; exact Real.sq_sqrt (by norm_num)
  apply Certificate.SOS.H1_0B056.weighted_nonnegative x hx
    Certificate.Generated.H1_0B056.positive_semidefinite
  rw [multiplier_identification]
  exact Certificate.MultiplierProofs.M056.nonnegative x hroot hregion
#print axioms nonnegative
end Certificate.Assembly.H1_0B056
namespace Certificate.Assembly.H1_0B057
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem multiplier_identification : Certificate.SOS.H1_0B057.multiplier = Certificate.MultiplierProofs.M057.certificate.polynomial := by
  decide +kernel

/-- All new algebraic obligations are discharged; the remaining hypotheses describe the domain. -/
theorem nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x (scale Certificate.SOS.H1_0B057.weight Certificate.SOS.H1_0B057.weighted) := by
  have hroot : (x 7)^2=3 := by rw [hx]; exact Real.sq_sqrt (by norm_num)
  apply Certificate.SOS.H1_0B057.weighted_nonnegative x hx
    Certificate.Generated.H1_0B057.positive_semidefinite
  rw [multiplier_identification]
  exact Certificate.MultiplierProofs.M057.nonnegative x hroot hregion
#print axioms nonnegative
end Certificate.Assembly.H1_0B057
namespace Certificate.Assembly.H1_0B058
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem multiplier_identification : Certificate.SOS.H1_0B058.multiplier = Certificate.MultiplierProofs.M058.certificate.polynomial := by
  decide +kernel

/-- All new algebraic obligations are discharged; the remaining hypotheses describe the domain. -/
theorem nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x (scale Certificate.SOS.H1_0B058.weight Certificate.SOS.H1_0B058.weighted) := by
  have hroot : (x 7)^2=3 := by rw [hx]; exact Real.sq_sqrt (by norm_num)
  apply Certificate.SOS.H1_0B058.weighted_nonnegative x hx
    Certificate.Generated.H1_0B058.positive_semidefinite
  rw [multiplier_identification]
  exact Certificate.MultiplierProofs.M058.nonnegative x hroot hregion
#print axioms nonnegative
end Certificate.Assembly.H1_0B058
namespace Certificate.Assembly.H1_0B059
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem multiplier_identification : Certificate.SOS.H1_0B059.multiplier = Certificate.MultiplierProofs.M059.certificate.polynomial := by
  decide +kernel

/-- All new algebraic obligations are discharged; the remaining hypotheses describe the domain. -/
theorem nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x (scale Certificate.SOS.H1_0B059.weight Certificate.SOS.H1_0B059.weighted) := by
  have hroot : (x 7)^2=3 := by rw [hx]; exact Real.sq_sqrt (by norm_num)
  apply Certificate.SOS.H1_0B059.weighted_nonnegative x hx
    Certificate.Generated.H1_0B059.positive_semidefinite
  rw [multiplier_identification]
  exact Certificate.MultiplierProofs.M059.nonnegative x hroot hregion
#print axioms nonnegative
end Certificate.Assembly.H1_0B059
namespace Certificate.Assembly.H1_0B060
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem multiplier_identification : Certificate.SOS.H1_0B060.multiplier = Certificate.MultiplierProofs.M060.certificate.polynomial := by
  decide +kernel

/-- All new algebraic obligations are discharged; the remaining hypotheses describe the domain. -/
theorem nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x (scale Certificate.SOS.H1_0B060.weight Certificate.SOS.H1_0B060.weighted) := by
  have hroot : (x 7)^2=3 := by rw [hx]; exact Real.sq_sqrt (by norm_num)
  apply Certificate.SOS.H1_0B060.weighted_nonnegative x hx
    Certificate.Generated.H1_0B060.positive_semidefinite
  rw [multiplier_identification]
  exact Certificate.MultiplierProofs.M060.nonnegative x hroot hregion
#print axioms nonnegative
end Certificate.Assembly.H1_0B060
namespace Certificate.Assembly.H1_0B061
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem multiplier_identification : Certificate.SOS.H1_0B061.multiplier = Certificate.MultiplierProofs.M061.certificate.polynomial := by
  decide +kernel

/-- All new algebraic obligations are discharged; the remaining hypotheses describe the domain. -/
theorem nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x (scale Certificate.SOS.H1_0B061.weight Certificate.SOS.H1_0B061.weighted) := by
  have hroot : (x 7)^2=3 := by rw [hx]; exact Real.sq_sqrt (by norm_num)
  apply Certificate.SOS.H1_0B061.weighted_nonnegative x hx
    Certificate.Generated.H1_0B061.positive_semidefinite
  rw [multiplier_identification]
  exact Certificate.MultiplierProofs.M061.nonnegative x hroot hregion
#print axioms nonnegative
end Certificate.Assembly.H1_0B061
namespace Certificate.Assembly.H1_0B062
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem multiplier_identification : Certificate.SOS.H1_0B062.multiplier = Certificate.MultiplierProofs.M062.certificate.polynomial := by
  decide +kernel

/-- All new algebraic obligations are discharged; the remaining hypotheses describe the domain. -/
theorem nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x (scale Certificate.SOS.H1_0B062.weight Certificate.SOS.H1_0B062.weighted) := by
  have hroot : (x 7)^2=3 := by rw [hx]; exact Real.sq_sqrt (by norm_num)
  apply Certificate.SOS.H1_0B062.weighted_nonnegative x hx
    Certificate.Generated.H1_0B062.positive_semidefinite
  rw [multiplier_identification]
  exact Certificate.MultiplierProofs.M062.nonnegative x hroot hregion
#print axioms nonnegative
end Certificate.Assembly.H1_0B062
namespace Certificate.Assembly.H1_0B063
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem multiplier_identification : Certificate.SOS.H1_0B063.multiplier = Certificate.MultiplierProofs.M063.certificate.polynomial := by
  decide +kernel

/-- All new algebraic obligations are discharged; the remaining hypotheses describe the domain. -/
theorem nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x (scale Certificate.SOS.H1_0B063.weight Certificate.SOS.H1_0B063.weighted) := by
  have hroot : (x 7)^2=3 := by rw [hx]; exact Real.sq_sqrt (by norm_num)
  apply Certificate.SOS.H1_0B063.weighted_nonnegative x hx
    Certificate.Generated.H1_0B063.positive_semidefinite
  rw [multiplier_identification]
  exact Certificate.MultiplierProofs.M063.nonnegative x hroot hregion
#print axioms nonnegative
end Certificate.Assembly.H1_0B063
namespace Certificate.Assembly.H1_0B064
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem multiplier_identification : Certificate.SOS.H1_0B064.multiplier = Certificate.MultiplierProofs.M064.certificate.polynomial := by
  decide +kernel

/-- All new algebraic obligations are discharged; the remaining hypotheses describe the domain. -/
theorem nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x (scale Certificate.SOS.H1_0B064.weight Certificate.SOS.H1_0B064.weighted) := by
  have hroot : (x 7)^2=3 := by rw [hx]; exact Real.sq_sqrt (by norm_num)
  apply Certificate.SOS.H1_0B064.weighted_nonnegative x hx
    Certificate.Generated.H1_0B064.positive_semidefinite
  rw [multiplier_identification]
  exact Certificate.MultiplierProofs.M064.nonnegative x hroot hregion
#print axioms nonnegative
end Certificate.Assembly.H1_0B064
namespace Certificate.Assembly.H1_0B065
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem multiplier_identification : Certificate.SOS.H1_0B065.multiplier = Certificate.MultiplierProofs.M065.certificate.polynomial := by
  decide +kernel

/-- All new algebraic obligations are discharged; the remaining hypotheses describe the domain. -/
theorem nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x (scale Certificate.SOS.H1_0B065.weight Certificate.SOS.H1_0B065.weighted) := by
  have hroot : (x 7)^2=3 := by rw [hx]; exact Real.sq_sqrt (by norm_num)
  apply Certificate.SOS.H1_0B065.weighted_nonnegative x hx
    Certificate.Generated.H1_0B065.positive_semidefinite
  rw [multiplier_identification]
  exact Certificate.MultiplierProofs.M065.nonnegative x hroot hregion
#print axioms nonnegative
end Certificate.Assembly.H1_0B065
namespace Certificate.Assembly.H1_0B066
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem multiplier_identification : Certificate.SOS.H1_0B066.multiplier = Certificate.MultiplierProofs.M066.certificate.polynomial := by
  decide +kernel

/-- All new algebraic obligations are discharged; the remaining hypotheses describe the domain. -/
theorem nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x (scale Certificate.SOS.H1_0B066.weight Certificate.SOS.H1_0B066.weighted) := by
  have hroot : (x 7)^2=3 := by rw [hx]; exact Real.sq_sqrt (by norm_num)
  apply Certificate.SOS.H1_0B066.weighted_nonnegative x hx
    Certificate.Generated.H1_0B066.positive_semidefinite
  rw [multiplier_identification]
  exact Certificate.MultiplierProofs.M066.nonnegative x hroot hregion
#print axioms nonnegative
end Certificate.Assembly.H1_0B066
namespace Certificate.Assembly.H1_0B067
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem multiplier_identification : Certificate.SOS.H1_0B067.multiplier = Certificate.MultiplierProofs.M067.certificate.polynomial := by
  decide +kernel

/-- All new algebraic obligations are discharged; the remaining hypotheses describe the domain. -/
theorem nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x (scale Certificate.SOS.H1_0B067.weight Certificate.SOS.H1_0B067.weighted) := by
  have hroot : (x 7)^2=3 := by rw [hx]; exact Real.sq_sqrt (by norm_num)
  apply Certificate.SOS.H1_0B067.weighted_nonnegative x hx
    Certificate.Generated.H1_0B067.positive_semidefinite
  rw [multiplier_identification]
  exact Certificate.MultiplierProofs.M067.nonnegative x hroot hregion
#print axioms nonnegative
end Certificate.Assembly.H1_0B067
namespace Certificate.Assembly.H1_0B068
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem multiplier_identification : Certificate.SOS.H1_0B068.multiplier = Certificate.MultiplierProofs.M068.certificate.polynomial := by
  decide +kernel

/-- All new algebraic obligations are discharged; the remaining hypotheses describe the domain. -/
theorem nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x (scale Certificate.SOS.H1_0B068.weight Certificate.SOS.H1_0B068.weighted) := by
  have hroot : (x 7)^2=3 := by rw [hx]; exact Real.sq_sqrt (by norm_num)
  apply Certificate.SOS.H1_0B068.weighted_nonnegative x hx
    Certificate.Generated.H1_0B068.positive_semidefinite
  rw [multiplier_identification]
  exact Certificate.MultiplierProofs.M068.nonnegative x hroot hregion
#print axioms nonnegative
end Certificate.Assembly.H1_0B068
namespace Certificate.Assembly.H1_0B069
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem multiplier_identification : Certificate.SOS.H1_0B069.multiplier = Certificate.MultiplierProofs.M069.certificate.polynomial := by
  decide +kernel

/-- All new algebraic obligations are discharged; the remaining hypotheses describe the domain. -/
theorem nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x (scale Certificate.SOS.H1_0B069.weight Certificate.SOS.H1_0B069.weighted) := by
  have hroot : (x 7)^2=3 := by rw [hx]; exact Real.sq_sqrt (by norm_num)
  apply Certificate.SOS.H1_0B069.weighted_nonnegative x hx
    Certificate.Generated.H1_0B069.positive_semidefinite
  rw [multiplier_identification]
  exact Certificate.MultiplierProofs.M069.nonnegative x hroot hregion
#print axioms nonnegative
end Certificate.Assembly.H1_0B069
namespace Certificate.Assembly.H1_0B070
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem multiplier_identification : Certificate.SOS.H1_0B070.multiplier = Certificate.MultiplierProofs.M070.certificate.polynomial := by
  decide +kernel

/-- All new algebraic obligations are discharged; the remaining hypotheses describe the domain. -/
theorem nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x (scale Certificate.SOS.H1_0B070.weight Certificate.SOS.H1_0B070.weighted) := by
  have hroot : (x 7)^2=3 := by rw [hx]; exact Real.sq_sqrt (by norm_num)
  apply Certificate.SOS.H1_0B070.weighted_nonnegative x hx
    Certificate.Generated.H1_0B070.positive_semidefinite
  rw [multiplier_identification]
  exact Certificate.MultiplierProofs.M070.nonnegative x hroot hregion
#print axioms nonnegative
end Certificate.Assembly.H1_0B070
namespace Certificate.Assembly.H1_0B071
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem multiplier_identification : Certificate.SOS.H1_0B071.multiplier = Certificate.MultiplierProofs.M071.certificate.polynomial := by
  decide +kernel

/-- All new algebraic obligations are discharged; the remaining hypotheses describe the domain. -/
theorem nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x (scale Certificate.SOS.H1_0B071.weight Certificate.SOS.H1_0B071.weighted) := by
  have hroot : (x 7)^2=3 := by rw [hx]; exact Real.sq_sqrt (by norm_num)
  apply Certificate.SOS.H1_0B071.weighted_nonnegative x hx
    Certificate.Generated.H1_0B071.positive_semidefinite
  rw [multiplier_identification]
  exact Certificate.MultiplierProofs.M071.nonnegative x hroot hregion
#print axioms nonnegative
end Certificate.Assembly.H1_0B071
namespace Certificate.Assembly.H1_0B072
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem multiplier_identification : Certificate.SOS.H1_0B072.multiplier = Certificate.MultiplierProofs.M072.certificate.polynomial := by
  decide +kernel

/-- All new algebraic obligations are discharged; the remaining hypotheses describe the domain. -/
theorem nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x (scale Certificate.SOS.H1_0B072.weight Certificate.SOS.H1_0B072.weighted) := by
  have hroot : (x 7)^2=3 := by rw [hx]; exact Real.sq_sqrt (by norm_num)
  apply Certificate.SOS.H1_0B072.weighted_nonnegative x hx
    Certificate.Generated.H1_0B072.positive_semidefinite
  rw [multiplier_identification]
  exact Certificate.MultiplierProofs.M072.nonnegative x hroot hregion
#print axioms nonnegative
end Certificate.Assembly.H1_0B072
namespace Certificate.Assembly.H1_0B073
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem multiplier_identification : Certificate.SOS.H1_0B073.multiplier = Certificate.MultiplierProofs.M073.certificate.polynomial := by
  decide +kernel

/-- All new algebraic obligations are discharged; the remaining hypotheses describe the domain. -/
theorem nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x (scale Certificate.SOS.H1_0B073.weight Certificate.SOS.H1_0B073.weighted) := by
  have hroot : (x 7)^2=3 := by rw [hx]; exact Real.sq_sqrt (by norm_num)
  apply Certificate.SOS.H1_0B073.weighted_nonnegative x hx
    Certificate.Generated.H1_0B073.positive_semidefinite
  rw [multiplier_identification]
  exact Certificate.MultiplierProofs.M073.nonnegative x hroot hregion
#print axioms nonnegative
end Certificate.Assembly.H1_0B073
namespace Certificate.Assembly.H1_0B074
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem multiplier_identification : Certificate.SOS.H1_0B074.multiplier = Certificate.MultiplierProofs.M074.certificate.polynomial := by
  decide +kernel

/-- All new algebraic obligations are discharged; the remaining hypotheses describe the domain. -/
theorem nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x (scale Certificate.SOS.H1_0B074.weight Certificate.SOS.H1_0B074.weighted) := by
  have hroot : (x 7)^2=3 := by rw [hx]; exact Real.sq_sqrt (by norm_num)
  apply Certificate.SOS.H1_0B074.weighted_nonnegative x hx
    Certificate.Generated.H1_0B074.positive_semidefinite
  rw [multiplier_identification]
  exact Certificate.MultiplierProofs.M074.nonnegative x hroot hregion
#print axioms nonnegative
end Certificate.Assembly.H1_0B074
