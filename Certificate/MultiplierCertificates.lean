import Certificate.PrimitiveData
namespace Certificate.MultiplierProofs
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
namespace M000
noncomputable def certificate : MultiplierCertificate where
  labels := []
  polynomial := [(Int.ofNat 1, ⟨0, 0, 0, 0, 0, 0, 0, 0⟩)]
  productDenominator := 1
  multiplierDenominator := 1
  sqrtCorrection := []
theorem checked : certificate.check PrimitiveData.polynomial = true := by
  unfold MultiplierCertificate.check
  decide +kernel

theorem nonnegative (x : Fin 8 → ℝ) (hroot : (x 7)^2=3) (hregion : PrimitiveData.Region x) :
    0 ≤ eval x certificate.polynomial :=
  MultiplierCertificate.nonnegative certificate PrimitiveData.polynomial checked
    (by decide +kernel) (by decide +kernel) x hroot hregion
#print axioms nonnegative
end M000
namespace M001
noncomputable def certificate : MultiplierCertificate where
  labels := [.sector1]
  polynomial := [(Int.ofNat 1, ⟨0, 0, 1, 0, 0, 0, 0, 0⟩)]
  productDenominator := 1
  multiplierDenominator := 1
  sqrtCorrection := []
theorem checked : certificate.check PrimitiveData.polynomial = true := by
  unfold MultiplierCertificate.check
  decide +kernel

theorem nonnegative (x : Fin 8 → ℝ) (hroot : (x 7)^2=3) (hregion : PrimitiveData.Region x) :
    0 ≤ eval x certificate.polynomial :=
  MultiplierCertificate.nonnegative certificate PrimitiveData.polynomial checked
    (by decide +kernel) (by decide +kernel) x hroot hregion
#print axioms nonnegative
end M001
namespace M002
noncomputable def certificate : MultiplierCertificate where
  labels := [.sector2]
  polynomial := [(Int.negSucc 0, ⟨0, 0, 1, 0, 0, 0, 0, 0⟩), (Int.ofNat 1, ⟨0, 0, 0, 1, 0, 0, 0, 1⟩)]
  productDenominator := 1
  multiplierDenominator := 1
  sqrtCorrection := []
theorem checked : certificate.check PrimitiveData.polynomial = true := by
  unfold MultiplierCertificate.check
  decide +kernel

theorem nonnegative (x : Fin 8 → ℝ) (hroot : (x 7)^2=3) (hregion : PrimitiveData.Region x) :
    0 ≤ eval x certificate.polynomial :=
  MultiplierCertificate.nonnegative certificate PrimitiveData.polynomial checked
    (by decide +kernel) (by decide +kernel) x hroot hregion
#print axioms nonnegative
end M002
namespace M003
noncomputable def certificate : MultiplierCertificate where
  labels := [.sector1Rot1]
  polynomial := [(Int.negSucc 2, ⟨0, 1, 0, 0, 0, 0, 0, 0⟩), (Int.ofNat 1, ⟨0, 0, 1, 0, 0, 0, 0, 0⟩), (Int.ofNat 1, ⟨1, 0, 0, 0, 0, 0, 0, 1⟩), (Int.negSucc 0, ⟨0, 0, 0, 1, 0, 0, 0, 1⟩)]
  productDenominator := 4
  multiplierDenominator := 4
  sqrtCorrection := []
theorem checked : certificate.check PrimitiveData.polynomial = true := by
  unfold MultiplierCertificate.check
  decide +kernel

theorem nonnegative (x : Fin 8 → ℝ) (hroot : (x 7)^2=3) (hregion : PrimitiveData.Region x) :
    0 ≤ eval x certificate.polynomial :=
  MultiplierCertificate.nonnegative certificate PrimitiveData.polynomial checked
    (by decide +kernel) (by decide +kernel) x hroot hregion
#print axioms nonnegative
end M003
namespace M004
noncomputable def certificate : MultiplierCertificate where
  labels := [.sector2Rot1]
  polynomial := [(Int.ofNat 3, ⟨0, 1, 0, 0, 0, 0, 0, 0⟩), (Int.ofNat 1, ⟨0, 0, 1, 0, 0, 0, 0, 0⟩), (Int.ofNat 1, ⟨1, 0, 0, 0, 0, 0, 0, 1⟩), (Int.ofNat 1, ⟨0, 0, 0, 1, 0, 0, 0, 1⟩)]
  productDenominator := 2
  multiplierDenominator := 2
  sqrtCorrection := []
theorem checked : certificate.check PrimitiveData.polynomial = true := by
  unfold MultiplierCertificate.check
  decide +kernel

theorem nonnegative (x : Fin 8 → ℝ) (hroot : (x 7)^2=3) (hregion : PrimitiveData.Region x) :
    0 ≤ eval x certificate.polynomial :=
  MultiplierCertificate.nonnegative certificate PrimitiveData.polynomial checked
    (by decide +kernel) (by decide +kernel) x hroot hregion
#print axioms nonnegative
end M004
namespace M005
noncomputable def certificate : MultiplierCertificate where
  labels := [.sector1Rot2]
  polynomial := [(Int.negSucc 2, ⟨0, 1, 0, 0, 0, 0, 0, 0⟩), (Int.ofNat 1, ⟨0, 0, 1, 0, 0, 0, 0, 0⟩), (Int.negSucc 0, ⟨1, 0, 0, 0, 0, 0, 0, 1⟩), (Int.ofNat 1, ⟨0, 0, 0, 1, 0, 0, 0, 1⟩)]
  productDenominator := 4
  multiplierDenominator := 4
  sqrtCorrection := []
theorem checked : certificate.check PrimitiveData.polynomial = true := by
  unfold MultiplierCertificate.check
  decide +kernel

theorem nonnegative (x : Fin 8 → ℝ) (hroot : (x 7)^2=3) (hregion : PrimitiveData.Region x) :
    0 ≤ eval x certificate.polynomial :=
  MultiplierCertificate.nonnegative certificate PrimitiveData.polynomial checked
    (by decide +kernel) (by decide +kernel) x hroot hregion
#print axioms nonnegative
end M005
namespace M006
noncomputable def certificate : MultiplierCertificate where
  labels := [.sector2Rot2]
  polynomial := [(Int.negSucc 0, ⟨0, 0, 1, 0, 0, 0, 0, 0⟩), (Int.ofNat 1, ⟨1, 0, 0, 0, 0, 0, 0, 1⟩)]
  productDenominator := 1
  multiplierDenominator := 1
  sqrtCorrection := []
theorem checked : certificate.check PrimitiveData.polynomial = true := by
  unfold MultiplierCertificate.check
  decide +kernel

theorem nonnegative (x : Fin 8 → ℝ) (hroot : (x 7)^2=3) (hregion : PrimitiveData.Region x) :
    0 ≤ eval x certificate.polynomial :=
  MultiplierCertificate.nonnegative certificate PrimitiveData.polynomial checked
    (by decide +kernel) (by decide +kernel) x hroot hregion
#print axioms nonnegative
end M006
namespace M007
noncomputable def certificate : MultiplierCertificate where
  labels := [.gNorm]
  polynomial := [(Int.ofNat 16, ⟨0, 0, 0, 0, 0, 0, 0, 0⟩), (Int.negSucc 4, ⟨2, 0, 0, 0, 0, 0, 0, 0⟩), (Int.negSucc 4, ⟨0, 2, 0, 0, 0, 0, 0, 0⟩), (Int.negSucc 4, ⟨0, 0, 2, 0, 0, 0, 0, 0⟩), (Int.negSucc 4, ⟨0, 0, 0, 2, 0, 0, 0, 0⟩)]
  productDenominator := 5
  multiplierDenominator := 5
  sqrtCorrection := []
theorem checked : certificate.check PrimitiveData.polynomial = true := by
  unfold MultiplierCertificate.check
  decide +kernel

theorem nonnegative (x : Fin 8 → ℝ) (hroot : (x 7)^2=3) (hregion : PrimitiveData.Region x) :
    0 ≤ eval x certificate.polynomial :=
  MultiplierCertificate.nonnegative certificate PrimitiveData.polynomial checked
    (by decide +kernel) (by decide +kernel) x hroot hregion
#print axioms nonnegative
end M007
namespace M008
noncomputable def certificate : MultiplierCertificate where
  labels := [.denominator0]
  polynomial := [(Int.negSucc 2306, ⟨0, 0, 0, 0, 0, 0, 0, 0⟩), (Int.negSucc 39999, ⟨0, 0, 0, 0, 0, 1, 0, 0⟩), (Int.ofNat 20000, ⟨0, 0, 0, 0, 0, 0, 1, 0⟩)]
  productDenominator := 30000
  multiplierDenominator := 30000
  sqrtCorrection := []
theorem checked : certificate.check PrimitiveData.polynomial = true := by
  unfold MultiplierCertificate.check
  decide +kernel

theorem nonnegative (x : Fin 8 → ℝ) (hroot : (x 7)^2=3) (hregion : PrimitiveData.Region x) :
    0 ≤ eval x certificate.polynomial :=
  MultiplierCertificate.nonnegative certificate PrimitiveData.polynomial checked
    (by decide +kernel) (by decide +kernel) x hroot hregion
#print axioms nonnegative
end M008
namespace M009
noncomputable def certificate : MultiplierCertificate where
  labels := [.denominator1]
  polynomial := [(Int.negSucc 2306, ⟨0, 0, 0, 0, 0, 0, 0, 0⟩), (Int.ofNat 20000, ⟨0, 0, 0, 0, 0, 1, 0, 0⟩), (Int.ofNat 20000, ⟨0, 0, 0, 0, 0, 0, 1, 0⟩), (Int.negSucc 19999, ⟨0, 0, 0, 0, 1, 0, 0, 1⟩)]
  productDenominator := 30000
  multiplierDenominator := 30000
  sqrtCorrection := []
theorem checked : certificate.check PrimitiveData.polynomial = true := by
  unfold MultiplierCertificate.check
  decide +kernel

theorem nonnegative (x : Fin 8 → ℝ) (hroot : (x 7)^2=3) (hregion : PrimitiveData.Region x) :
    0 ≤ eval x certificate.polynomial :=
  MultiplierCertificate.nonnegative certificate PrimitiveData.polynomial checked
    (by decide +kernel) (by decide +kernel) x hroot hregion
#print axioms nonnegative
end M009
namespace M010
noncomputable def certificate : MultiplierCertificate where
  labels := [.denominator2]
  polynomial := [(Int.negSucc 2306, ⟨0, 0, 0, 0, 0, 0, 0, 0⟩), (Int.ofNat 20000, ⟨0, 0, 0, 0, 0, 1, 0, 0⟩), (Int.ofNat 20000, ⟨0, 0, 0, 0, 0, 0, 1, 0⟩), (Int.ofNat 20000, ⟨0, 0, 0, 0, 1, 0, 0, 1⟩)]
  productDenominator := 30000
  multiplierDenominator := 30000
  sqrtCorrection := []
theorem checked : certificate.check PrimitiveData.polynomial = true := by
  unfold MultiplierCertificate.check
  decide +kernel

theorem nonnegative (x : Fin 8 → ℝ) (hroot : (x 7)^2=3) (hregion : PrimitiveData.Region x) :
    0 ≤ eval x certificate.polynomial :=
  MultiplierCertificate.nonnegative certificate PrimitiveData.polynomial checked
    (by decide +kernel) (by decide +kernel) x hroot hregion
#print axioms nonnegative
end M010
namespace M011
noncomputable def certificate : MultiplierCertificate where
  labels := [.hLower]
  polynomial := [(Int.negSucc 0, ⟨0, 0, 0, 0, 0, 0, 0, 0⟩), (Int.ofNat 1, ⟨0, 0, 0, 0, 0, 0, 1, 0⟩)]
  productDenominator := 1
  multiplierDenominator := 1
  sqrtCorrection := []
theorem checked : certificate.check PrimitiveData.polynomial = true := by
  unfold MultiplierCertificate.check
  decide +kernel

theorem nonnegative (x : Fin 8 → ℝ) (hroot : (x 7)^2=3) (hregion : PrimitiveData.Region x) :
    0 ≤ eval x certificate.polynomial :=
  MultiplierCertificate.nonnegative certificate PrimitiveData.polynomial checked
    (by decide +kernel) (by decide +kernel) x hroot hregion
#print axioms nonnegative
end M011
namespace M012
noncomputable def certificate : MultiplierCertificate where
  labels := [.hUpper]
  polynomial := [(Int.ofNat 12, ⟨0, 0, 0, 0, 0, 0, 0, 0⟩), (Int.negSucc 4, ⟨0, 0, 0, 0, 0, 0, 1, 0⟩)]
  productDenominator := 5
  multiplierDenominator := 5
  sqrtCorrection := []
theorem checked : certificate.check PrimitiveData.polynomial = true := by
  unfold MultiplierCertificate.check
  decide +kernel

theorem nonnegative (x : Fin 8 → ℝ) (hroot : (x 7)^2=3) (hregion : PrimitiveData.Region x) :
    0 ≤ eval x certificate.polynomial :=
  MultiplierCertificate.nonnegative certificate PrimitiveData.polynomial checked
    (by decide +kernel) (by decide +kernel) x hroot hregion
#print axioms nonnegative
end M012
namespace M013
noncomputable def certificate : MultiplierCertificate where
  labels := [.xNorm]
  polynomial := [(Int.ofNat 119, ⟨0, 0, 0, 0, 0, 0, 0, 0⟩), (Int.negSucc 24, ⟨0, 0, 0, 0, 2, 0, 0, 0⟩), (Int.negSucc 24, ⟨0, 0, 0, 0, 0, 2, 0, 0⟩)]
  productDenominator := 25
  multiplierDenominator := 25
  sqrtCorrection := []
theorem checked : certificate.check PrimitiveData.polynomial = true := by
  unfold MultiplierCertificate.check
  decide +kernel

theorem nonnegative (x : Fin 8 → ℝ) (hroot : (x 7)^2=3) (hregion : PrimitiveData.Region x) :
    0 ≤ eval x certificate.polynomial :=
  MultiplierCertificate.nonnegative certificate PrimitiveData.polynomial checked
    (by decide +kernel) (by decide +kernel) x hroot hregion
#print axioms nonnegative
end M013
namespace M014
noncomputable def certificate : MultiplierCertificate where
  labels := [.horoballY]
  polynomial := [(Int.negSucc 1, ⟨0, 0, 0, 0, 0, 0, 0, 0⟩), (Int.ofNat 9, ⟨0, 0, 0, 0, 0, 1, 0, 0⟩), (Int.ofNat 9, ⟨0, 0, 0, 0, 0, 0, 1, 0⟩)]
  productDenominator := 9
  multiplierDenominator := 9
  sqrtCorrection := []
theorem checked : certificate.check PrimitiveData.polynomial = true := by
  unfold MultiplierCertificate.check
  decide +kernel

theorem nonnegative (x : Fin 8 → ℝ) (hroot : (x 7)^2=3) (hregion : PrimitiveData.Region x) :
    0 ≤ eval x certificate.polynomial :=
  MultiplierCertificate.nonnegative certificate PrimitiveData.polynomial checked
    (by decide +kernel) (by decide +kernel) x hroot hregion
#print axioms nonnegative
end M014
namespace M015
noncomputable def certificate : MultiplierCertificate where
  labels := [.horoballPlus]
  polynomial := [(Int.ofNat 27, ⟨0, 0, 0, 0, 0, 0, 0, 0⟩), (Int.ofNat 27, ⟨0, 0, 0, 0, 2, 0, 0, 0⟩), (Int.negSucc 7, ⟨0, 0, 0, 0, 0, 1, 0, 0⟩), (Int.ofNat 9, ⟨0, 0, 0, 0, 0, 2, 0, 0⟩), (Int.negSucc 7, ⟨0, 0, 0, 0, 0, 0, 1, 0⟩), (Int.ofNat 18, ⟨0, 0, 0, 0, 0, 1, 1, 0⟩), (Int.ofNat 9, ⟨0, 0, 0, 0, 0, 0, 2, 0⟩), (Int.negSucc 17, ⟨0, 0, 0, 0, 1, 1, 0, 1⟩), (Int.negSucc 17, ⟨0, 0, 0, 0, 1, 0, 1, 1⟩)]
  productDenominator := 27
  multiplierDenominator := 27
  sqrtCorrection := []
theorem checked : certificate.check PrimitiveData.polynomial = true := by
  unfold MultiplierCertificate.check
  decide +kernel

theorem nonnegative (x : Fin 8 → ℝ) (hroot : (x 7)^2=3) (hregion : PrimitiveData.Region x) :
    0 ≤ eval x certificate.polynomial :=
  MultiplierCertificate.nonnegative certificate PrimitiveData.polynomial checked
    (by decide +kernel) (by decide +kernel) x hroot hregion
#print axioms nonnegative
end M015
namespace M016
noncomputable def certificate : MultiplierCertificate where
  labels := [.horoballMinus]
  polynomial := [(Int.ofNat 27, ⟨0, 0, 0, 0, 0, 0, 0, 0⟩), (Int.ofNat 27, ⟨0, 0, 0, 0, 2, 0, 0, 0⟩), (Int.negSucc 7, ⟨0, 0, 0, 0, 0, 1, 0, 0⟩), (Int.ofNat 9, ⟨0, 0, 0, 0, 0, 2, 0, 0⟩), (Int.negSucc 7, ⟨0, 0, 0, 0, 0, 0, 1, 0⟩), (Int.ofNat 18, ⟨0, 0, 0, 0, 0, 1, 1, 0⟩), (Int.ofNat 9, ⟨0, 0, 0, 0, 0, 0, 2, 0⟩), (Int.ofNat 18, ⟨0, 0, 0, 0, 1, 1, 0, 1⟩), (Int.ofNat 18, ⟨0, 0, 0, 0, 1, 0, 1, 1⟩)]
  productDenominator := 27
  multiplierDenominator := 27
  sqrtCorrection := []
theorem checked : certificate.check PrimitiveData.polynomial = true := by
  unfold MultiplierCertificate.check
  decide +kernel

theorem nonnegative (x : Fin 8 → ℝ) (hroot : (x 7)^2=3) (hregion : PrimitiveData.Region x) :
    0 ≤ eval x certificate.polynomial :=
  MultiplierCertificate.nonnegative certificate PrimitiveData.polynomial checked
    (by decide +kernel) (by decide +kernel) x hroot hregion
#print axioms nonnegative
end M016
namespace M017
noncomputable def certificate : MultiplierCertificate where
  labels := [.halfplane0]
  polynomial := [(Int.negSucc 0, ⟨0, 0, 0, 0, 0, 0, 0, 0⟩), (Int.negSucc 14, ⟨0, 0, 0, 0, 1, 0, 0, 0⟩), (Int.ofNat 5, ⟨0, 0, 0, 0, 0, 1, 0, 1⟩), (Int.ofNat 5, ⟨0, 0, 0, 0, 0, 0, 1, 1⟩)]
  productDenominator := 1
  multiplierDenominator := 1
  sqrtCorrection := []
theorem checked : certificate.check PrimitiveData.polynomial = true := by
  unfold MultiplierCertificate.check
  decide +kernel

theorem nonnegative (x : Fin 8 → ℝ) (hroot : (x 7)^2=3) (hregion : PrimitiveData.Region x) :
    0 ≤ eval x certificate.polynomial :=
  MultiplierCertificate.nonnegative certificate PrimitiveData.polynomial checked
    (by decide +kernel) (by decide +kernel) x hroot hregion
#print axioms nonnegative
end M017
namespace M018
noncomputable def certificate : MultiplierCertificate where
  labels := [.halfplane1]
  polynomial := [(Int.negSucc 0, ⟨0, 0, 0, 0, 0, 0, 0, 0⟩), (Int.negSucc 9, ⟨0, 0, 0, 0, 0, 1, 0, 1⟩), (Int.ofNat 5, ⟨0, 0, 0, 0, 0, 0, 1, 1⟩)]
  productDenominator := 1
  multiplierDenominator := 1
  sqrtCorrection := []
theorem checked : certificate.check PrimitiveData.polynomial = true := by
  unfold MultiplierCertificate.check
  decide +kernel

theorem nonnegative (x : Fin 8 → ℝ) (hroot : (x 7)^2=3) (hregion : PrimitiveData.Region x) :
    0 ≤ eval x certificate.polynomial :=
  MultiplierCertificate.nonnegative certificate PrimitiveData.polynomial checked
    (by decide +kernel) (by decide +kernel) x hroot hregion
#print axioms nonnegative
end M018
namespace M019
noncomputable def certificate : MultiplierCertificate where
  labels := [.halfplane2]
  polynomial := [(Int.negSucc 0, ⟨0, 0, 0, 0, 0, 0, 0, 0⟩), (Int.ofNat 15, ⟨0, 0, 0, 0, 1, 0, 0, 0⟩), (Int.ofNat 5, ⟨0, 0, 0, 0, 0, 1, 0, 1⟩), (Int.ofNat 5, ⟨0, 0, 0, 0, 0, 0, 1, 1⟩)]
  productDenominator := 1
  multiplierDenominator := 1
  sqrtCorrection := []
theorem checked : certificate.check PrimitiveData.polynomial = true := by
  unfold MultiplierCertificate.check
  decide +kernel

theorem nonnegative (x : Fin 8 → ℝ) (hroot : (x 7)^2=3) (hregion : PrimitiveData.Region x) :
    0 ≤ eval x certificate.polynomial :=
  MultiplierCertificate.nonnegative certificate PrimitiveData.polynomial checked
    (by decide +kernel) (by decide +kernel) x hroot hregion
#print axioms nonnegative
end M019
namespace M020
noncomputable def certificate : MultiplierCertificate where
  labels := [.sector1, .sector2]
  polynomial := [(Int.negSucc 0, ⟨0, 0, 2, 0, 0, 0, 0, 0⟩), (Int.ofNat 1, ⟨0, 0, 1, 1, 0, 0, 0, 1⟩)]
  productDenominator := 1
  multiplierDenominator := 1
  sqrtCorrection := []
theorem checked : certificate.check PrimitiveData.polynomial = true := by
  unfold MultiplierCertificate.check
  decide +kernel

theorem nonnegative (x : Fin 8 → ℝ) (hroot : (x 7)^2=3) (hregion : PrimitiveData.Region x) :
    0 ≤ eval x certificate.polynomial :=
  MultiplierCertificate.nonnegative certificate PrimitiveData.polynomial checked
    (by decide +kernel) (by decide +kernel) x hroot hregion
#print axioms nonnegative
end M020
namespace M021
noncomputable def certificate : MultiplierCertificate where
  labels := [.sector1, .sector1Rot1]
  polynomial := [(Int.negSucc 2, ⟨0, 1, 1, 0, 0, 0, 0, 0⟩), (Int.ofNat 1, ⟨0, 0, 2, 0, 0, 0, 0, 0⟩), (Int.ofNat 1, ⟨1, 0, 1, 0, 0, 0, 0, 1⟩), (Int.negSucc 0, ⟨0, 0, 1, 1, 0, 0, 0, 1⟩)]
  productDenominator := 4
  multiplierDenominator := 4
  sqrtCorrection := []
theorem checked : certificate.check PrimitiveData.polynomial = true := by
  unfold MultiplierCertificate.check
  decide +kernel

theorem nonnegative (x : Fin 8 → ℝ) (hroot : (x 7)^2=3) (hregion : PrimitiveData.Region x) :
    0 ≤ eval x certificate.polynomial :=
  MultiplierCertificate.nonnegative certificate PrimitiveData.polynomial checked
    (by decide +kernel) (by decide +kernel) x hroot hregion
#print axioms nonnegative
end M021
namespace M022
noncomputable def certificate : MultiplierCertificate where
  labels := [.sector1, .sector2Rot1]
  polynomial := [(Int.ofNat 3, ⟨0, 1, 1, 0, 0, 0, 0, 0⟩), (Int.ofNat 1, ⟨0, 0, 2, 0, 0, 0, 0, 0⟩), (Int.ofNat 1, ⟨1, 0, 1, 0, 0, 0, 0, 1⟩), (Int.ofNat 1, ⟨0, 0, 1, 1, 0, 0, 0, 1⟩)]
  productDenominator := 2
  multiplierDenominator := 2
  sqrtCorrection := []
theorem checked : certificate.check PrimitiveData.polynomial = true := by
  unfold MultiplierCertificate.check
  decide +kernel

theorem nonnegative (x : Fin 8 → ℝ) (hroot : (x 7)^2=3) (hregion : PrimitiveData.Region x) :
    0 ≤ eval x certificate.polynomial :=
  MultiplierCertificate.nonnegative certificate PrimitiveData.polynomial checked
    (by decide +kernel) (by decide +kernel) x hroot hregion
#print axioms nonnegative
end M022
namespace M023
noncomputable def certificate : MultiplierCertificate where
  labels := [.sector1, .sector1Rot2]
  polynomial := [(Int.negSucc 2, ⟨0, 1, 1, 0, 0, 0, 0, 0⟩), (Int.ofNat 1, ⟨0, 0, 2, 0, 0, 0, 0, 0⟩), (Int.negSucc 0, ⟨1, 0, 1, 0, 0, 0, 0, 1⟩), (Int.ofNat 1, ⟨0, 0, 1, 1, 0, 0, 0, 1⟩)]
  productDenominator := 4
  multiplierDenominator := 4
  sqrtCorrection := []
theorem checked : certificate.check PrimitiveData.polynomial = true := by
  unfold MultiplierCertificate.check
  decide +kernel

theorem nonnegative (x : Fin 8 → ℝ) (hroot : (x 7)^2=3) (hregion : PrimitiveData.Region x) :
    0 ≤ eval x certificate.polynomial :=
  MultiplierCertificate.nonnegative certificate PrimitiveData.polynomial checked
    (by decide +kernel) (by decide +kernel) x hroot hregion
#print axioms nonnegative
end M023
namespace M024
noncomputable def certificate : MultiplierCertificate where
  labels := [.sector1, .sector2Rot2]
  polynomial := [(Int.negSucc 0, ⟨0, 0, 2, 0, 0, 0, 0, 0⟩), (Int.ofNat 1, ⟨1, 0, 1, 0, 0, 0, 0, 1⟩)]
  productDenominator := 1
  multiplierDenominator := 1
  sqrtCorrection := []
theorem checked : certificate.check PrimitiveData.polynomial = true := by
  unfold MultiplierCertificate.check
  decide +kernel

theorem nonnegative (x : Fin 8 → ℝ) (hroot : (x 7)^2=3) (hregion : PrimitiveData.Region x) :
    0 ≤ eval x certificate.polynomial :=
  MultiplierCertificate.nonnegative certificate PrimitiveData.polynomial checked
    (by decide +kernel) (by decide +kernel) x hroot hregion
#print axioms nonnegative
end M024
namespace M025
noncomputable def certificate : MultiplierCertificate where
  labels := [.sector1, .denominator0]
  polynomial := [(Int.negSucc 2306, ⟨0, 0, 1, 0, 0, 0, 0, 0⟩), (Int.negSucc 39999, ⟨0, 0, 1, 0, 0, 1, 0, 0⟩), (Int.ofNat 20000, ⟨0, 0, 1, 0, 0, 0, 1, 0⟩)]
  productDenominator := 30000
  multiplierDenominator := 30000
  sqrtCorrection := []
theorem checked : certificate.check PrimitiveData.polynomial = true := by
  unfold MultiplierCertificate.check
  decide +kernel

theorem nonnegative (x : Fin 8 → ℝ) (hroot : (x 7)^2=3) (hregion : PrimitiveData.Region x) :
    0 ≤ eval x certificate.polynomial :=
  MultiplierCertificate.nonnegative certificate PrimitiveData.polynomial checked
    (by decide +kernel) (by decide +kernel) x hroot hregion
#print axioms nonnegative
end M025
namespace M026
noncomputable def certificate : MultiplierCertificate where
  labels := [.sector1, .denominator1]
  polynomial := [(Int.negSucc 2306, ⟨0, 0, 1, 0, 0, 0, 0, 0⟩), (Int.ofNat 20000, ⟨0, 0, 1, 0, 0, 1, 0, 0⟩), (Int.ofNat 20000, ⟨0, 0, 1, 0, 0, 0, 1, 0⟩), (Int.negSucc 19999, ⟨0, 0, 1, 0, 1, 0, 0, 1⟩)]
  productDenominator := 30000
  multiplierDenominator := 30000
  sqrtCorrection := []
theorem checked : certificate.check PrimitiveData.polynomial = true := by
  unfold MultiplierCertificate.check
  decide +kernel

theorem nonnegative (x : Fin 8 → ℝ) (hroot : (x 7)^2=3) (hregion : PrimitiveData.Region x) :
    0 ≤ eval x certificate.polynomial :=
  MultiplierCertificate.nonnegative certificate PrimitiveData.polynomial checked
    (by decide +kernel) (by decide +kernel) x hroot hregion
#print axioms nonnegative
end M026
namespace M027
noncomputable def certificate : MultiplierCertificate where
  labels := [.sector1, .denominator2]
  polynomial := [(Int.negSucc 2306, ⟨0, 0, 1, 0, 0, 0, 0, 0⟩), (Int.ofNat 20000, ⟨0, 0, 1, 0, 0, 1, 0, 0⟩), (Int.ofNat 20000, ⟨0, 0, 1, 0, 0, 0, 1, 0⟩), (Int.ofNat 20000, ⟨0, 0, 1, 0, 1, 0, 0, 1⟩)]
  productDenominator := 30000
  multiplierDenominator := 30000
  sqrtCorrection := []
theorem checked : certificate.check PrimitiveData.polynomial = true := by
  unfold MultiplierCertificate.check
  decide +kernel

theorem nonnegative (x : Fin 8 → ℝ) (hroot : (x 7)^2=3) (hregion : PrimitiveData.Region x) :
    0 ≤ eval x certificate.polynomial :=
  MultiplierCertificate.nonnegative certificate PrimitiveData.polynomial checked
    (by decide +kernel) (by decide +kernel) x hroot hregion
#print axioms nonnegative
end M027
namespace M028
noncomputable def certificate : MultiplierCertificate where
  labels := [.sector1, .hLower]
  polynomial := [(Int.negSucc 0, ⟨0, 0, 1, 0, 0, 0, 0, 0⟩), (Int.ofNat 1, ⟨0, 0, 1, 0, 0, 0, 1, 0⟩)]
  productDenominator := 1
  multiplierDenominator := 1
  sqrtCorrection := []
theorem checked : certificate.check PrimitiveData.polynomial = true := by
  unfold MultiplierCertificate.check
  decide +kernel

theorem nonnegative (x : Fin 8 → ℝ) (hroot : (x 7)^2=3) (hregion : PrimitiveData.Region x) :
    0 ≤ eval x certificate.polynomial :=
  MultiplierCertificate.nonnegative certificate PrimitiveData.polynomial checked
    (by decide +kernel) (by decide +kernel) x hroot hregion
#print axioms nonnegative
end M028
namespace M029
noncomputable def certificate : MultiplierCertificate where
  labels := [.sector1, .hUpper]
  polynomial := [(Int.ofNat 12, ⟨0, 0, 1, 0, 0, 0, 0, 0⟩), (Int.negSucc 4, ⟨0, 0, 1, 0, 0, 0, 1, 0⟩)]
  productDenominator := 5
  multiplierDenominator := 5
  sqrtCorrection := []
theorem checked : certificate.check PrimitiveData.polynomial = true := by
  unfold MultiplierCertificate.check
  decide +kernel

theorem nonnegative (x : Fin 8 → ℝ) (hroot : (x 7)^2=3) (hregion : PrimitiveData.Region x) :
    0 ≤ eval x certificate.polynomial :=
  MultiplierCertificate.nonnegative certificate PrimitiveData.polynomial checked
    (by decide +kernel) (by decide +kernel) x hroot hregion
#print axioms nonnegative
end M029
namespace M030
noncomputable def certificate : MultiplierCertificate where
  labels := [.sector2, .sector1Rot1]
  polynomial := [(Int.ofNat 3, ⟨0, 1, 1, 0, 0, 0, 0, 0⟩), (Int.negSucc 0, ⟨0, 0, 2, 0, 0, 0, 0, 0⟩), (Int.ofNat 3, ⟨1, 0, 0, 1, 0, 0, 0, 0⟩), (Int.negSucc 2, ⟨0, 0, 0, 2, 0, 0, 0, 0⟩), (Int.negSucc 0, ⟨1, 0, 1, 0, 0, 0, 0, 1⟩), (Int.negSucc 2, ⟨0, 1, 0, 1, 0, 0, 0, 1⟩), (Int.ofNat 2, ⟨0, 0, 1, 1, 0, 0, 0, 1⟩)]
  productDenominator := 4
  multiplierDenominator := 4
  sqrtCorrection := [(Int.negSucc 3, ⟨1, 0, 0, 1, 0, 0, 0, 0⟩), (Int.ofNat 4, ⟨0, 0, 0, 2, 0, 0, 0, 0⟩)]
theorem checked : certificate.check PrimitiveData.polynomial = true := by
  unfold MultiplierCertificate.check
  decide +kernel

theorem nonnegative (x : Fin 8 → ℝ) (hroot : (x 7)^2=3) (hregion : PrimitiveData.Region x) :
    0 ≤ eval x certificate.polynomial :=
  MultiplierCertificate.nonnegative certificate PrimitiveData.polynomial checked
    (by decide +kernel) (by decide +kernel) x hroot hregion
#print axioms nonnegative
end M030
namespace M031
noncomputable def certificate : MultiplierCertificate where
  labels := [.sector2, .sector2Rot1]
  polynomial := [(Int.negSucc 2, ⟨0, 1, 1, 0, 0, 0, 0, 0⟩), (Int.negSucc 0, ⟨0, 0, 2, 0, 0, 0, 0, 0⟩), (Int.ofNat 3, ⟨1, 0, 0, 1, 0, 0, 0, 0⟩), (Int.ofNat 3, ⟨0, 0, 0, 2, 0, 0, 0, 0⟩), (Int.negSucc 0, ⟨1, 0, 1, 0, 0, 0, 0, 1⟩), (Int.ofNat 3, ⟨0, 1, 0, 1, 0, 0, 0, 1⟩)]
  productDenominator := 2
  multiplierDenominator := 2
  sqrtCorrection := [(Int.negSucc 1, ⟨1, 0, 0, 1, 0, 0, 0, 0⟩), (Int.negSucc 1, ⟨0, 0, 0, 2, 0, 0, 0, 0⟩)]
theorem checked : certificate.check PrimitiveData.polynomial = true := by
  unfold MultiplierCertificate.check
  decide +kernel

theorem nonnegative (x : Fin 8 → ℝ) (hroot : (x 7)^2=3) (hregion : PrimitiveData.Region x) :
    0 ≤ eval x certificate.polynomial :=
  MultiplierCertificate.nonnegative certificate PrimitiveData.polynomial checked
    (by decide +kernel) (by decide +kernel) x hroot hregion
#print axioms nonnegative
end M031
namespace M032
noncomputable def certificate : MultiplierCertificate where
  labels := [.sector2, .sector1Rot2]
  polynomial := [(Int.ofNat 3, ⟨0, 1, 1, 0, 0, 0, 0, 0⟩), (Int.negSucc 0, ⟨0, 0, 2, 0, 0, 0, 0, 0⟩), (Int.negSucc 2, ⟨1, 0, 0, 1, 0, 0, 0, 0⟩), (Int.ofNat 3, ⟨0, 0, 0, 2, 0, 0, 0, 0⟩), (Int.ofNat 1, ⟨1, 0, 1, 0, 0, 0, 0, 1⟩), (Int.negSucc 2, ⟨0, 1, 0, 1, 0, 0, 0, 1⟩)]
  productDenominator := 4
  multiplierDenominator := 4
  sqrtCorrection := [(Int.ofNat 4, ⟨1, 0, 0, 1, 0, 0, 0, 0⟩), (Int.negSucc 3, ⟨0, 0, 0, 2, 0, 0, 0, 0⟩)]
theorem checked : certificate.check PrimitiveData.polynomial = true := by
  unfold MultiplierCertificate.check
  decide +kernel

theorem nonnegative (x : Fin 8 → ℝ) (hroot : (x 7)^2=3) (hregion : PrimitiveData.Region x) :
    0 ≤ eval x certificate.polynomial :=
  MultiplierCertificate.nonnegative certificate PrimitiveData.polynomial checked
    (by decide +kernel) (by decide +kernel) x hroot hregion
#print axioms nonnegative
end M032
namespace M033
noncomputable def certificate : MultiplierCertificate where
  labels := [.sector2, .sector2Rot2]
  polynomial := [(Int.ofNat 1, ⟨0, 0, 2, 0, 0, 0, 0, 0⟩), (Int.ofNat 3, ⟨1, 0, 0, 1, 0, 0, 0, 0⟩), (Int.negSucc 0, ⟨1, 0, 1, 0, 0, 0, 0, 1⟩), (Int.negSucc 0, ⟨0, 0, 1, 1, 0, 0, 0, 1⟩)]
  productDenominator := 1
  multiplierDenominator := 1
  sqrtCorrection := [(Int.negSucc 0, ⟨1, 0, 0, 1, 0, 0, 0, 0⟩)]
theorem checked : certificate.check PrimitiveData.polynomial = true := by
  unfold MultiplierCertificate.check
  decide +kernel

theorem nonnegative (x : Fin 8 → ℝ) (hroot : (x 7)^2=3) (hregion : PrimitiveData.Region x) :
    0 ≤ eval x certificate.polynomial :=
  MultiplierCertificate.nonnegative certificate PrimitiveData.polynomial checked
    (by decide +kernel) (by decide +kernel) x hroot hregion
#print axioms nonnegative
end M033
namespace M034
noncomputable def certificate : MultiplierCertificate where
  labels := [.sector2, .denominator0]
  polynomial := [(Int.ofNat 2307, ⟨0, 0, 1, 0, 0, 0, 0, 0⟩), (Int.ofNat 40000, ⟨0, 0, 1, 0, 0, 1, 0, 0⟩), (Int.negSucc 19999, ⟨0, 0, 1, 0, 0, 0, 1, 0⟩), (Int.negSucc 2306, ⟨0, 0, 0, 1, 0, 0, 0, 1⟩), (Int.negSucc 39999, ⟨0, 0, 0, 1, 0, 1, 0, 1⟩), (Int.ofNat 20000, ⟨0, 0, 0, 1, 0, 0, 1, 1⟩)]
  productDenominator := 30000
  multiplierDenominator := 30000
  sqrtCorrection := []
theorem checked : certificate.check PrimitiveData.polynomial = true := by
  unfold MultiplierCertificate.check
  decide +kernel

theorem nonnegative (x : Fin 8 → ℝ) (hroot : (x 7)^2=3) (hregion : PrimitiveData.Region x) :
    0 ≤ eval x certificate.polynomial :=
  MultiplierCertificate.nonnegative certificate PrimitiveData.polynomial checked
    (by decide +kernel) (by decide +kernel) x hroot hregion
#print axioms nonnegative
end M034
namespace M035
noncomputable def certificate : MultiplierCertificate where
  labels := [.sector2, .denominator1]
  polynomial := [(Int.ofNat 2307, ⟨0, 0, 1, 0, 0, 0, 0, 0⟩), (Int.negSucc 59999, ⟨0, 0, 0, 1, 1, 0, 0, 0⟩), (Int.negSucc 19999, ⟨0, 0, 1, 0, 0, 1, 0, 0⟩), (Int.negSucc 19999, ⟨0, 0, 1, 0, 0, 0, 1, 0⟩), (Int.negSucc 2306, ⟨0, 0, 0, 1, 0, 0, 0, 1⟩), (Int.ofNat 20000, ⟨0, 0, 1, 0, 1, 0, 0, 1⟩), (Int.ofNat 20000, ⟨0, 0, 0, 1, 0, 1, 0, 1⟩), (Int.ofNat 20000, ⟨0, 0, 0, 1, 0, 0, 1, 1⟩)]
  productDenominator := 30000
  multiplierDenominator := 30000
  sqrtCorrection := [(Int.ofNat 600000000, ⟨0, 0, 0, 1, 1, 0, 0, 0⟩)]
theorem checked : certificate.check PrimitiveData.polynomial = true := by
  unfold MultiplierCertificate.check
  decide +kernel

theorem nonnegative (x : Fin 8 → ℝ) (hroot : (x 7)^2=3) (hregion : PrimitiveData.Region x) :
    0 ≤ eval x certificate.polynomial :=
  MultiplierCertificate.nonnegative certificate PrimitiveData.polynomial checked
    (by decide +kernel) (by decide +kernel) x hroot hregion
#print axioms nonnegative
end M035
namespace M036
noncomputable def certificate : MultiplierCertificate where
  labels := [.sector2, .denominator2]
  polynomial := [(Int.ofNat 2307, ⟨0, 0, 1, 0, 0, 0, 0, 0⟩), (Int.ofNat 60000, ⟨0, 0, 0, 1, 1, 0, 0, 0⟩), (Int.negSucc 19999, ⟨0, 0, 1, 0, 0, 1, 0, 0⟩), (Int.negSucc 19999, ⟨0, 0, 1, 0, 0, 0, 1, 0⟩), (Int.negSucc 2306, ⟨0, 0, 0, 1, 0, 0, 0, 1⟩), (Int.negSucc 19999, ⟨0, 0, 1, 0, 1, 0, 0, 1⟩), (Int.ofNat 20000, ⟨0, 0, 0, 1, 0, 1, 0, 1⟩), (Int.ofNat 20000, ⟨0, 0, 0, 1, 0, 0, 1, 1⟩)]
  productDenominator := 30000
  multiplierDenominator := 30000
  sqrtCorrection := [(Int.negSucc 599999999, ⟨0, 0, 0, 1, 1, 0, 0, 0⟩)]
theorem checked : certificate.check PrimitiveData.polynomial = true := by
  unfold MultiplierCertificate.check
  decide +kernel

theorem nonnegative (x : Fin 8 → ℝ) (hroot : (x 7)^2=3) (hregion : PrimitiveData.Region x) :
    0 ≤ eval x certificate.polynomial :=
  MultiplierCertificate.nonnegative certificate PrimitiveData.polynomial checked
    (by decide +kernel) (by decide +kernel) x hroot hregion
#print axioms nonnegative
end M036
namespace M037
noncomputable def certificate : MultiplierCertificate where
  labels := [.sector2, .hLower]
  polynomial := [(Int.ofNat 1, ⟨0, 0, 1, 0, 0, 0, 0, 0⟩), (Int.negSucc 0, ⟨0, 0, 1, 0, 0, 0, 1, 0⟩), (Int.negSucc 0, ⟨0, 0, 0, 1, 0, 0, 0, 1⟩), (Int.ofNat 1, ⟨0, 0, 0, 1, 0, 0, 1, 1⟩)]
  productDenominator := 1
  multiplierDenominator := 1
  sqrtCorrection := []
theorem checked : certificate.check PrimitiveData.polynomial = true := by
  unfold MultiplierCertificate.check
  decide +kernel

theorem nonnegative (x : Fin 8 → ℝ) (hroot : (x 7)^2=3) (hregion : PrimitiveData.Region x) :
    0 ≤ eval x certificate.polynomial :=
  MultiplierCertificate.nonnegative certificate PrimitiveData.polynomial checked
    (by decide +kernel) (by decide +kernel) x hroot hregion
#print axioms nonnegative
end M037
namespace M038
noncomputable def certificate : MultiplierCertificate where
  labels := [.sector2, .hUpper]
  polynomial := [(Int.negSucc 11, ⟨0, 0, 1, 0, 0, 0, 0, 0⟩), (Int.ofNat 5, ⟨0, 0, 1, 0, 0, 0, 1, 0⟩), (Int.ofNat 12, ⟨0, 0, 0, 1, 0, 0, 0, 1⟩), (Int.negSucc 4, ⟨0, 0, 0, 1, 0, 0, 1, 1⟩)]
  productDenominator := 5
  multiplierDenominator := 5
  sqrtCorrection := []
theorem checked : certificate.check PrimitiveData.polynomial = true := by
  unfold MultiplierCertificate.check
  decide +kernel

theorem nonnegative (x : Fin 8 → ℝ) (hroot : (x 7)^2=3) (hregion : PrimitiveData.Region x) :
    0 ≤ eval x certificate.polynomial :=
  MultiplierCertificate.nonnegative certificate PrimitiveData.polynomial checked
    (by decide +kernel) (by decide +kernel) x hroot hregion
#print axioms nonnegative
end M038
namespace M039
noncomputable def certificate : MultiplierCertificate where
  labels := [.sector1Rot1, .sector2Rot1]
  polynomial := [(Int.ofNat 3, ⟨2, 0, 0, 0, 0, 0, 0, 0⟩), (Int.negSucc 8, ⟨0, 2, 0, 0, 0, 0, 0, 0⟩), (Int.ofNat 1, ⟨0, 0, 2, 0, 0, 0, 0, 0⟩), (Int.negSucc 2, ⟨0, 0, 0, 2, 0, 0, 0, 0⟩), (Int.ofNat 2, ⟨1, 0, 1, 0, 0, 0, 0, 1⟩), (Int.negSucc 5, ⟨0, 1, 0, 1, 0, 0, 0, 1⟩)]
  productDenominator := 8
  multiplierDenominator := 8
  sqrtCorrection := [(Int.negSucc 7, ⟨2, 0, 0, 0, 0, 0, 0, 0⟩), (Int.ofNat 8, ⟨0, 0, 0, 2, 0, 0, 0, 0⟩)]
theorem checked : certificate.check PrimitiveData.polynomial = true := by
  unfold MultiplierCertificate.check
  decide +kernel

theorem nonnegative (x : Fin 8 → ℝ) (hroot : (x 7)^2=3) (hregion : PrimitiveData.Region x) :
    0 ≤ eval x certificate.polynomial :=
  MultiplierCertificate.nonnegative certificate PrimitiveData.polynomial checked
    (by decide +kernel) (by decide +kernel) x hroot hregion
#print axioms nonnegative
end M039
namespace M040
noncomputable def certificate : MultiplierCertificate where
  labels := [.sector1Rot1, .sector1Rot2]
  polynomial := [(Int.negSucc 2, ⟨2, 0, 0, 0, 0, 0, 0, 0⟩), (Int.ofNat 9, ⟨0, 2, 0, 0, 0, 0, 0, 0⟩), (Int.negSucc 5, ⟨0, 1, 1, 0, 0, 0, 0, 0⟩), (Int.ofNat 1, ⟨0, 0, 2, 0, 0, 0, 0, 0⟩), (Int.ofNat 6, ⟨1, 0, 0, 1, 0, 0, 0, 0⟩), (Int.negSucc 2, ⟨0, 0, 0, 2, 0, 0, 0, 0⟩)]
  productDenominator := 16
  multiplierDenominator := 16
  sqrtCorrection := [(Int.ofNat 16, ⟨2, 0, 0, 0, 0, 0, 0, 0⟩), (Int.negSucc 31, ⟨1, 0, 0, 1, 0, 0, 0, 0⟩), (Int.ofNat 16, ⟨0, 0, 0, 2, 0, 0, 0, 0⟩)]
theorem checked : certificate.check PrimitiveData.polynomial = true := by
  unfold MultiplierCertificate.check
  decide +kernel

theorem nonnegative (x : Fin 8 → ℝ) (hroot : (x 7)^2=3) (hregion : PrimitiveData.Region x) :
    0 ≤ eval x certificate.polynomial :=
  MultiplierCertificate.nonnegative certificate PrimitiveData.polynomial checked
    (by decide +kernel) (by decide +kernel) x hroot hregion
#print axioms nonnegative
end M040
namespace M041
noncomputable def certificate : MultiplierCertificate where
  labels := [.sector1Rot1, .sector2Rot2]
  polynomial := [(Int.ofNat 3, ⟨2, 0, 0, 0, 0, 0, 0, 0⟩), (Int.ofNat 3, ⟨0, 1, 1, 0, 0, 0, 0, 0⟩), (Int.negSucc 0, ⟨0, 0, 2, 0, 0, 0, 0, 0⟩), (Int.negSucc 2, ⟨1, 0, 0, 1, 0, 0, 0, 0⟩), (Int.negSucc 2, ⟨1, 1, 0, 0, 0, 0, 0, 1⟩), (Int.ofNat 1, ⟨0, 0, 1, 1, 0, 0, 0, 1⟩)]
  productDenominator := 4
  multiplierDenominator := 4
  sqrtCorrection := [(Int.negSucc 3, ⟨2, 0, 0, 0, 0, 0, 0, 0⟩), (Int.ofNat 4, ⟨1, 0, 0, 1, 0, 0, 0, 0⟩)]
theorem checked : certificate.check PrimitiveData.polynomial = true := by
  unfold MultiplierCertificate.check
  decide +kernel

theorem nonnegative (x : Fin 8 → ℝ) (hroot : (x 7)^2=3) (hregion : PrimitiveData.Region x) :
    0 ≤ eval x certificate.polynomial :=
  MultiplierCertificate.nonnegative certificate PrimitiveData.polynomial checked
    (by decide +kernel) (by decide +kernel) x hroot hregion
#print axioms nonnegative
end M041
namespace M042
noncomputable def certificate : MultiplierCertificate where
  labels := [.sector1Rot1, .denominator0]
  polynomial := [(Int.ofNat 6921, ⟨0, 1, 0, 0, 0, 0, 0, 0⟩), (Int.negSucc 2306, ⟨0, 0, 1, 0, 0, 0, 0, 0⟩), (Int.ofNat 120000, ⟨0, 1, 0, 0, 0, 1, 0, 0⟩), (Int.negSucc 39999, ⟨0, 0, 1, 0, 0, 1, 0, 0⟩), (Int.negSucc 59999, ⟨0, 1, 0, 0, 0, 0, 1, 0⟩), (Int.ofNat 20000, ⟨0, 0, 1, 0, 0, 0, 1, 0⟩), (Int.negSucc 2306, ⟨1, 0, 0, 0, 0, 0, 0, 1⟩), (Int.ofNat 2307, ⟨0, 0, 0, 1, 0, 0, 0, 1⟩), (Int.negSucc 39999, ⟨1, 0, 0, 0, 0, 1, 0, 1⟩), (Int.ofNat 40000, ⟨0, 0, 0, 1, 0, 1, 0, 1⟩), (Int.ofNat 20000, ⟨1, 0, 0, 0, 0, 0, 1, 1⟩), (Int.negSucc 19999, ⟨0, 0, 0, 1, 0, 0, 1, 1⟩)]
  productDenominator := 120000
  multiplierDenominator := 120000
  sqrtCorrection := []
theorem checked : certificate.check PrimitiveData.polynomial = true := by
  unfold MultiplierCertificate.check
  decide +kernel

theorem nonnegative (x : Fin 8 → ℝ) (hroot : (x 7)^2=3) (hregion : PrimitiveData.Region x) :
    0 ≤ eval x certificate.polynomial :=
  MultiplierCertificate.nonnegative certificate PrimitiveData.polynomial checked
    (by decide +kernel) (by decide +kernel) x hroot hregion
#print axioms nonnegative
end M042
namespace M043
noncomputable def certificate : MultiplierCertificate where
  labels := [.sector1Rot1, .denominator1]
  polynomial := [(Int.ofNat 6921, ⟨0, 1, 0, 0, 0, 0, 0, 0⟩), (Int.negSucc 2306, ⟨0, 0, 1, 0, 0, 0, 0, 0⟩), (Int.negSucc 59999, ⟨1, 0, 0, 0, 1, 0, 0, 0⟩), (Int.ofNat 60000, ⟨0, 0, 0, 1, 1, 0, 0, 0⟩), (Int.negSucc 59999, ⟨0, 1, 0, 0, 0, 1, 0, 0⟩), (Int.ofNat 20000, ⟨0, 0, 1, 0, 0, 1, 0, 0⟩), (Int.negSucc 59999, ⟨0, 1, 0, 0, 0, 0, 1, 0⟩), (Int.ofNat 20000, ⟨0, 0, 1, 0, 0, 0, 1, 0⟩), (Int.negSucc 2306, ⟨1, 0, 0, 0, 0, 0, 0, 1⟩), (Int.ofNat 2307, ⟨0, 0, 0, 1, 0, 0, 0, 1⟩), (Int.ofNat 60000, ⟨0, 1, 0, 0, 1, 0, 0, 1⟩), (Int.negSucc 19999, ⟨0, 0, 1, 0, 1, 0, 0, 1⟩), (Int.ofNat 20000, ⟨1, 0, 0, 0, 0, 1, 0, 1⟩), (Int.negSucc 19999, ⟨0, 0, 0, 1, 0, 1, 0, 1⟩), (Int.ofNat 20000, ⟨1, 0, 0, 0, 0, 0, 1, 1⟩), (Int.negSucc 19999, ⟨0, 0, 0, 1, 0, 0, 1, 1⟩)]
  productDenominator := 120000
  multiplierDenominator := 120000
  sqrtCorrection := [(Int.ofNat 2400000000, ⟨1, 0, 0, 0, 1, 0, 0, 0⟩), (Int.negSucc 2399999999, ⟨0, 0, 0, 1, 1, 0, 0, 0⟩)]
theorem checked : certificate.check PrimitiveData.polynomial = true := by
  unfold MultiplierCertificate.check
  decide +kernel

theorem nonnegative (x : Fin 8 → ℝ) (hroot : (x 7)^2=3) (hregion : PrimitiveData.Region x) :
    0 ≤ eval x certificate.polynomial :=
  MultiplierCertificate.nonnegative certificate PrimitiveData.polynomial checked
    (by decide +kernel) (by decide +kernel) x hroot hregion
#print axioms nonnegative
end M043
namespace M044
noncomputable def certificate : MultiplierCertificate where
  labels := [.sector1Rot1, .denominator2]
  polynomial := [(Int.ofNat 6921, ⟨0, 1, 0, 0, 0, 0, 0, 0⟩), (Int.negSucc 2306, ⟨0, 0, 1, 0, 0, 0, 0, 0⟩), (Int.ofNat 60000, ⟨1, 0, 0, 0, 1, 0, 0, 0⟩), (Int.negSucc 59999, ⟨0, 0, 0, 1, 1, 0, 0, 0⟩), (Int.negSucc 59999, ⟨0, 1, 0, 0, 0, 1, 0, 0⟩), (Int.ofNat 20000, ⟨0, 0, 1, 0, 0, 1, 0, 0⟩), (Int.negSucc 59999, ⟨0, 1, 0, 0, 0, 0, 1, 0⟩), (Int.ofNat 20000, ⟨0, 0, 1, 0, 0, 0, 1, 0⟩), (Int.negSucc 2306, ⟨1, 0, 0, 0, 0, 0, 0, 1⟩), (Int.ofNat 2307, ⟨0, 0, 0, 1, 0, 0, 0, 1⟩), (Int.negSucc 59999, ⟨0, 1, 0, 0, 1, 0, 0, 1⟩), (Int.ofNat 20000, ⟨0, 0, 1, 0, 1, 0, 0, 1⟩), (Int.ofNat 20000, ⟨1, 0, 0, 0, 0, 1, 0, 1⟩), (Int.negSucc 19999, ⟨0, 0, 0, 1, 0, 1, 0, 1⟩), (Int.ofNat 20000, ⟨1, 0, 0, 0, 0, 0, 1, 1⟩), (Int.negSucc 19999, ⟨0, 0, 0, 1, 0, 0, 1, 1⟩)]
  productDenominator := 120000
  multiplierDenominator := 120000
  sqrtCorrection := [(Int.negSucc 2399999999, ⟨1, 0, 0, 0, 1, 0, 0, 0⟩), (Int.ofNat 2400000000, ⟨0, 0, 0, 1, 1, 0, 0, 0⟩)]
theorem checked : certificate.check PrimitiveData.polynomial = true := by
  unfold MultiplierCertificate.check
  decide +kernel

theorem nonnegative (x : Fin 8 → ℝ) (hroot : (x 7)^2=3) (hregion : PrimitiveData.Region x) :
    0 ≤ eval x certificate.polynomial :=
  MultiplierCertificate.nonnegative certificate PrimitiveData.polynomial checked
    (by decide +kernel) (by decide +kernel) x hroot hregion
#print axioms nonnegative
end M044
namespace M045
noncomputable def certificate : MultiplierCertificate where
  labels := [.sector1Rot1, .hLower]
  polynomial := [(Int.ofNat 3, ⟨0, 1, 0, 0, 0, 0, 0, 0⟩), (Int.negSucc 0, ⟨0, 0, 1, 0, 0, 0, 0, 0⟩), (Int.negSucc 2, ⟨0, 1, 0, 0, 0, 0, 1, 0⟩), (Int.ofNat 1, ⟨0, 0, 1, 0, 0, 0, 1, 0⟩), (Int.negSucc 0, ⟨1, 0, 0, 0, 0, 0, 0, 1⟩), (Int.ofNat 1, ⟨0, 0, 0, 1, 0, 0, 0, 1⟩), (Int.ofNat 1, ⟨1, 0, 0, 0, 0, 0, 1, 1⟩), (Int.negSucc 0, ⟨0, 0, 0, 1, 0, 0, 1, 1⟩)]
  productDenominator := 4
  multiplierDenominator := 4
  sqrtCorrection := []
theorem checked : certificate.check PrimitiveData.polynomial = true := by
  unfold MultiplierCertificate.check
  decide +kernel

theorem nonnegative (x : Fin 8 → ℝ) (hroot : (x 7)^2=3) (hregion : PrimitiveData.Region x) :
    0 ≤ eval x certificate.polynomial :=
  MultiplierCertificate.nonnegative certificate PrimitiveData.polynomial checked
    (by decide +kernel) (by decide +kernel) x hroot hregion
#print axioms nonnegative
end M045
namespace M046
noncomputable def certificate : MultiplierCertificate where
  labels := [.sector1Rot1, .hUpper]
  polynomial := [(Int.negSucc 35, ⟨0, 1, 0, 0, 0, 0, 0, 0⟩), (Int.ofNat 12, ⟨0, 0, 1, 0, 0, 0, 0, 0⟩), (Int.ofNat 15, ⟨0, 1, 0, 0, 0, 0, 1, 0⟩), (Int.negSucc 4, ⟨0, 0, 1, 0, 0, 0, 1, 0⟩), (Int.ofNat 12, ⟨1, 0, 0, 0, 0, 0, 0, 1⟩), (Int.negSucc 11, ⟨0, 0, 0, 1, 0, 0, 0, 1⟩), (Int.negSucc 4, ⟨1, 0, 0, 0, 0, 0, 1, 1⟩), (Int.ofNat 5, ⟨0, 0, 0, 1, 0, 0, 1, 1⟩)]
  productDenominator := 20
  multiplierDenominator := 20
  sqrtCorrection := []
theorem checked : certificate.check PrimitiveData.polynomial = true := by
  unfold MultiplierCertificate.check
  decide +kernel

theorem nonnegative (x : Fin 8 → ℝ) (hroot : (x 7)^2=3) (hregion : PrimitiveData.Region x) :
    0 ≤ eval x certificate.polynomial :=
  MultiplierCertificate.nonnegative certificate PrimitiveData.polynomial checked
    (by decide +kernel) (by decide +kernel) x hroot hregion
#print axioms nonnegative
end M046
namespace M047
noncomputable def certificate : MultiplierCertificate where
  labels := [.sector2Rot1, .sector1Rot2]
  polynomial := [(Int.negSucc 2, ⟨2, 0, 0, 0, 0, 0, 0, 0⟩), (Int.negSucc 8, ⟨0, 2, 0, 0, 0, 0, 0, 0⟩), (Int.ofNat 1, ⟨0, 0, 2, 0, 0, 0, 0, 0⟩), (Int.ofNat 3, ⟨0, 0, 0, 2, 0, 0, 0, 0⟩), (Int.negSucc 5, ⟨1, 1, 0, 0, 0, 0, 0, 1⟩), (Int.ofNat 2, ⟨0, 0, 1, 1, 0, 0, 0, 1⟩)]
  productDenominator := 8
  multiplierDenominator := 8
  sqrtCorrection := [(Int.ofNat 8, ⟨2, 0, 0, 0, 0, 0, 0, 0⟩), (Int.negSucc 7, ⟨0, 0, 0, 2, 0, 0, 0, 0⟩)]
theorem checked : certificate.check PrimitiveData.polynomial = true := by
  unfold MultiplierCertificate.check
  decide +kernel

theorem nonnegative (x : Fin 8 → ℝ) (hroot : (x 7)^2=3) (hregion : PrimitiveData.Region x) :
    0 ≤ eval x certificate.polynomial :=
  MultiplierCertificate.nonnegative certificate PrimitiveData.polynomial checked
    (by decide +kernel) (by decide +kernel) x hroot hregion
#print axioms nonnegative
end M047
namespace M048
noncomputable def certificate : MultiplierCertificate where
  labels := [.sector2Rot1, .sector2Rot2]
  polynomial := [(Int.ofNat 3, ⟨2, 0, 0, 0, 0, 0, 0, 0⟩), (Int.negSucc 2, ⟨0, 1, 1, 0, 0, 0, 0, 0⟩), (Int.negSucc 0, ⟨0, 0, 2, 0, 0, 0, 0, 0⟩), (Int.ofNat 3, ⟨1, 0, 0, 1, 0, 0, 0, 0⟩), (Int.ofNat 3, ⟨1, 1, 0, 0, 0, 0, 0, 1⟩), (Int.negSucc 0, ⟨0, 0, 1, 1, 0, 0, 0, 1⟩)]
  productDenominator := 2
  multiplierDenominator := 2
  sqrtCorrection := [(Int.negSucc 1, ⟨2, 0, 0, 0, 0, 0, 0, 0⟩), (Int.negSucc 1, ⟨1, 0, 0, 1, 0, 0, 0, 0⟩)]
theorem checked : certificate.check PrimitiveData.polynomial = true := by
  unfold MultiplierCertificate.check
  decide +kernel

theorem nonnegative (x : Fin 8 → ℝ) (hroot : (x 7)^2=3) (hregion : PrimitiveData.Region x) :
    0 ≤ eval x certificate.polynomial :=
  MultiplierCertificate.nonnegative certificate PrimitiveData.polynomial checked
    (by decide +kernel) (by decide +kernel) x hroot hregion
#print axioms nonnegative
end M048
namespace M049
noncomputable def certificate : MultiplierCertificate where
  labels := [.sector2Rot1, .denominator0]
  polynomial := [(Int.negSucc 6920, ⟨0, 1, 0, 0, 0, 0, 0, 0⟩), (Int.negSucc 2306, ⟨0, 0, 1, 0, 0, 0, 0, 0⟩), (Int.negSucc 119999, ⟨0, 1, 0, 0, 0, 1, 0, 0⟩), (Int.negSucc 39999, ⟨0, 0, 1, 0, 0, 1, 0, 0⟩), (Int.ofNat 60000, ⟨0, 1, 0, 0, 0, 0, 1, 0⟩), (Int.ofNat 20000, ⟨0, 0, 1, 0, 0, 0, 1, 0⟩), (Int.negSucc 2306, ⟨1, 0, 0, 0, 0, 0, 0, 1⟩), (Int.negSucc 2306, ⟨0, 0, 0, 1, 0, 0, 0, 1⟩), (Int.negSucc 39999, ⟨1, 0, 0, 0, 0, 1, 0, 1⟩), (Int.negSucc 39999, ⟨0, 0, 0, 1, 0, 1, 0, 1⟩), (Int.ofNat 20000, ⟨1, 0, 0, 0, 0, 0, 1, 1⟩), (Int.ofNat 20000, ⟨0, 0, 0, 1, 0, 0, 1, 1⟩)]
  productDenominator := 60000
  multiplierDenominator := 60000
  sqrtCorrection := []
theorem checked : certificate.check PrimitiveData.polynomial = true := by
  unfold MultiplierCertificate.check
  decide +kernel

theorem nonnegative (x : Fin 8 → ℝ) (hroot : (x 7)^2=3) (hregion : PrimitiveData.Region x) :
    0 ≤ eval x certificate.polynomial :=
  MultiplierCertificate.nonnegative certificate PrimitiveData.polynomial checked
    (by decide +kernel) (by decide +kernel) x hroot hregion
#print axioms nonnegative
end M049
namespace M050
noncomputable def certificate : MultiplierCertificate where
  labels := [.sector2Rot1, .denominator1]
  polynomial := [(Int.negSucc 6920, ⟨0, 1, 0, 0, 0, 0, 0, 0⟩), (Int.negSucc 2306, ⟨0, 0, 1, 0, 0, 0, 0, 0⟩), (Int.negSucc 59999, ⟨1, 0, 0, 0, 1, 0, 0, 0⟩), (Int.negSucc 59999, ⟨0, 0, 0, 1, 1, 0, 0, 0⟩), (Int.ofNat 60000, ⟨0, 1, 0, 0, 0, 1, 0, 0⟩), (Int.ofNat 20000, ⟨0, 0, 1, 0, 0, 1, 0, 0⟩), (Int.ofNat 60000, ⟨0, 1, 0, 0, 0, 0, 1, 0⟩), (Int.ofNat 20000, ⟨0, 0, 1, 0, 0, 0, 1, 0⟩), (Int.negSucc 2306, ⟨1, 0, 0, 0, 0, 0, 0, 1⟩), (Int.negSucc 2306, ⟨0, 0, 0, 1, 0, 0, 0, 1⟩), (Int.negSucc 59999, ⟨0, 1, 0, 0, 1, 0, 0, 1⟩), (Int.negSucc 19999, ⟨0, 0, 1, 0, 1, 0, 0, 1⟩), (Int.ofNat 20000, ⟨1, 0, 0, 0, 0, 1, 0, 1⟩), (Int.ofNat 20000, ⟨0, 0, 0, 1, 0, 1, 0, 1⟩), (Int.ofNat 20000, ⟨1, 0, 0, 0, 0, 0, 1, 1⟩), (Int.ofNat 20000, ⟨0, 0, 0, 1, 0, 0, 1, 1⟩)]
  productDenominator := 60000
  multiplierDenominator := 60000
  sqrtCorrection := [(Int.ofNat 1200000000, ⟨1, 0, 0, 0, 1, 0, 0, 0⟩), (Int.ofNat 1200000000, ⟨0, 0, 0, 1, 1, 0, 0, 0⟩)]
theorem checked : certificate.check PrimitiveData.polynomial = true := by
  unfold MultiplierCertificate.check
  decide +kernel

theorem nonnegative (x : Fin 8 → ℝ) (hroot : (x 7)^2=3) (hregion : PrimitiveData.Region x) :
    0 ≤ eval x certificate.polynomial :=
  MultiplierCertificate.nonnegative certificate PrimitiveData.polynomial checked
    (by decide +kernel) (by decide +kernel) x hroot hregion
#print axioms nonnegative
end M050
namespace M051
noncomputable def certificate : MultiplierCertificate where
  labels := [.sector2Rot1, .denominator2]
  polynomial := [(Int.negSucc 6920, ⟨0, 1, 0, 0, 0, 0, 0, 0⟩), (Int.negSucc 2306, ⟨0, 0, 1, 0, 0, 0, 0, 0⟩), (Int.ofNat 60000, ⟨1, 0, 0, 0, 1, 0, 0, 0⟩), (Int.ofNat 60000, ⟨0, 0, 0, 1, 1, 0, 0, 0⟩), (Int.ofNat 60000, ⟨0, 1, 0, 0, 0, 1, 0, 0⟩), (Int.ofNat 20000, ⟨0, 0, 1, 0, 0, 1, 0, 0⟩), (Int.ofNat 60000, ⟨0, 1, 0, 0, 0, 0, 1, 0⟩), (Int.ofNat 20000, ⟨0, 0, 1, 0, 0, 0, 1, 0⟩), (Int.negSucc 2306, ⟨1, 0, 0, 0, 0, 0, 0, 1⟩), (Int.negSucc 2306, ⟨0, 0, 0, 1, 0, 0, 0, 1⟩), (Int.ofNat 60000, ⟨0, 1, 0, 0, 1, 0, 0, 1⟩), (Int.ofNat 20000, ⟨0, 0, 1, 0, 1, 0, 0, 1⟩), (Int.ofNat 20000, ⟨1, 0, 0, 0, 0, 1, 0, 1⟩), (Int.ofNat 20000, ⟨0, 0, 0, 1, 0, 1, 0, 1⟩), (Int.ofNat 20000, ⟨1, 0, 0, 0, 0, 0, 1, 1⟩), (Int.ofNat 20000, ⟨0, 0, 0, 1, 0, 0, 1, 1⟩)]
  productDenominator := 60000
  multiplierDenominator := 60000
  sqrtCorrection := [(Int.negSucc 1199999999, ⟨1, 0, 0, 0, 1, 0, 0, 0⟩), (Int.negSucc 1199999999, ⟨0, 0, 0, 1, 1, 0, 0, 0⟩)]
theorem checked : certificate.check PrimitiveData.polynomial = true := by
  unfold MultiplierCertificate.check
  decide +kernel

theorem nonnegative (x : Fin 8 → ℝ) (hroot : (x 7)^2=3) (hregion : PrimitiveData.Region x) :
    0 ≤ eval x certificate.polynomial :=
  MultiplierCertificate.nonnegative certificate PrimitiveData.polynomial checked
    (by decide +kernel) (by decide +kernel) x hroot hregion
#print axioms nonnegative
end M051
namespace M052
noncomputable def certificate : MultiplierCertificate where
  labels := [.sector2Rot1, .hLower]
  polynomial := [(Int.negSucc 2, ⟨0, 1, 0, 0, 0, 0, 0, 0⟩), (Int.negSucc 0, ⟨0, 0, 1, 0, 0, 0, 0, 0⟩), (Int.ofNat 3, ⟨0, 1, 0, 0, 0, 0, 1, 0⟩), (Int.ofNat 1, ⟨0, 0, 1, 0, 0, 0, 1, 0⟩), (Int.negSucc 0, ⟨1, 0, 0, 0, 0, 0, 0, 1⟩), (Int.negSucc 0, ⟨0, 0, 0, 1, 0, 0, 0, 1⟩), (Int.ofNat 1, ⟨1, 0, 0, 0, 0, 0, 1, 1⟩), (Int.ofNat 1, ⟨0, 0, 0, 1, 0, 0, 1, 1⟩)]
  productDenominator := 2
  multiplierDenominator := 2
  sqrtCorrection := []
theorem checked : certificate.check PrimitiveData.polynomial = true := by
  unfold MultiplierCertificate.check
  decide +kernel

theorem nonnegative (x : Fin 8 → ℝ) (hroot : (x 7)^2=3) (hregion : PrimitiveData.Region x) :
    0 ≤ eval x certificate.polynomial :=
  MultiplierCertificate.nonnegative certificate PrimitiveData.polynomial checked
    (by decide +kernel) (by decide +kernel) x hroot hregion
#print axioms nonnegative
end M052
namespace M053
noncomputable def certificate : MultiplierCertificate where
  labels := [.sector2Rot1, .hUpper]
  polynomial := [(Int.ofNat 36, ⟨0, 1, 0, 0, 0, 0, 0, 0⟩), (Int.ofNat 12, ⟨0, 0, 1, 0, 0, 0, 0, 0⟩), (Int.negSucc 14, ⟨0, 1, 0, 0, 0, 0, 1, 0⟩), (Int.negSucc 4, ⟨0, 0, 1, 0, 0, 0, 1, 0⟩), (Int.ofNat 12, ⟨1, 0, 0, 0, 0, 0, 0, 1⟩), (Int.ofNat 12, ⟨0, 0, 0, 1, 0, 0, 0, 1⟩), (Int.negSucc 4, ⟨1, 0, 0, 0, 0, 0, 1, 1⟩), (Int.negSucc 4, ⟨0, 0, 0, 1, 0, 0, 1, 1⟩)]
  productDenominator := 10
  multiplierDenominator := 10
  sqrtCorrection := []
theorem checked : certificate.check PrimitiveData.polynomial = true := by
  unfold MultiplierCertificate.check
  decide +kernel

theorem nonnegative (x : Fin 8 → ℝ) (hroot : (x 7)^2=3) (hregion : PrimitiveData.Region x) :
    0 ≤ eval x certificate.polynomial :=
  MultiplierCertificate.nonnegative certificate PrimitiveData.polynomial checked
    (by decide +kernel) (by decide +kernel) x hroot hregion
#print axioms nonnegative
end M053
namespace M054
noncomputable def certificate : MultiplierCertificate where
  labels := [.sector1Rot2, .sector2Rot2]
  polynomial := [(Int.negSucc 2, ⟨2, 0, 0, 0, 0, 0, 0, 0⟩), (Int.ofNat 3, ⟨0, 1, 1, 0, 0, 0, 0, 0⟩), (Int.negSucc 0, ⟨0, 0, 2, 0, 0, 0, 0, 0⟩), (Int.ofNat 3, ⟨1, 0, 0, 1, 0, 0, 0, 0⟩), (Int.negSucc 2, ⟨1, 1, 0, 0, 0, 0, 0, 1⟩), (Int.ofNat 2, ⟨1, 0, 1, 0, 0, 0, 0, 1⟩), (Int.negSucc 0, ⟨0, 0, 1, 1, 0, 0, 0, 1⟩)]
  productDenominator := 4
  multiplierDenominator := 4
  sqrtCorrection := [(Int.ofNat 4, ⟨2, 0, 0, 0, 0, 0, 0, 0⟩), (Int.negSucc 3, ⟨1, 0, 0, 1, 0, 0, 0, 0⟩)]
theorem checked : certificate.check PrimitiveData.polynomial = true := by
  unfold MultiplierCertificate.check
  decide +kernel

theorem nonnegative (x : Fin 8 → ℝ) (hroot : (x 7)^2=3) (hregion : PrimitiveData.Region x) :
    0 ≤ eval x certificate.polynomial :=
  MultiplierCertificate.nonnegative certificate PrimitiveData.polynomial checked
    (by decide +kernel) (by decide +kernel) x hroot hregion
#print axioms nonnegative
end M054
namespace M055
noncomputable def certificate : MultiplierCertificate where
  labels := [.sector1Rot2, .denominator0]
  polynomial := [(Int.ofNat 6921, ⟨0, 1, 0, 0, 0, 0, 0, 0⟩), (Int.negSucc 2306, ⟨0, 0, 1, 0, 0, 0, 0, 0⟩), (Int.ofNat 120000, ⟨0, 1, 0, 0, 0, 1, 0, 0⟩), (Int.negSucc 39999, ⟨0, 0, 1, 0, 0, 1, 0, 0⟩), (Int.negSucc 59999, ⟨0, 1, 0, 0, 0, 0, 1, 0⟩), (Int.ofNat 20000, ⟨0, 0, 1, 0, 0, 0, 1, 0⟩), (Int.ofNat 2307, ⟨1, 0, 0, 0, 0, 0, 0, 1⟩), (Int.negSucc 2306, ⟨0, 0, 0, 1, 0, 0, 0, 1⟩), (Int.ofNat 40000, ⟨1, 0, 0, 0, 0, 1, 0, 1⟩), (Int.negSucc 39999, ⟨0, 0, 0, 1, 0, 1, 0, 1⟩), (Int.negSucc 19999, ⟨1, 0, 0, 0, 0, 0, 1, 1⟩), (Int.ofNat 20000, ⟨0, 0, 0, 1, 0, 0, 1, 1⟩)]
  productDenominator := 120000
  multiplierDenominator := 120000
  sqrtCorrection := []
theorem checked : certificate.check PrimitiveData.polynomial = true := by
  unfold MultiplierCertificate.check
  decide +kernel

theorem nonnegative (x : Fin 8 → ℝ) (hroot : (x 7)^2=3) (hregion : PrimitiveData.Region x) :
    0 ≤ eval x certificate.polynomial :=
  MultiplierCertificate.nonnegative certificate PrimitiveData.polynomial checked
    (by decide +kernel) (by decide +kernel) x hroot hregion
#print axioms nonnegative
end M055
namespace M056
noncomputable def certificate : MultiplierCertificate where
  labels := [.sector1Rot2, .denominator1]
  polynomial := [(Int.ofNat 6921, ⟨0, 1, 0, 0, 0, 0, 0, 0⟩), (Int.negSucc 2306, ⟨0, 0, 1, 0, 0, 0, 0, 0⟩), (Int.ofNat 60000, ⟨1, 0, 0, 0, 1, 0, 0, 0⟩), (Int.negSucc 59999, ⟨0, 0, 0, 1, 1, 0, 0, 0⟩), (Int.negSucc 59999, ⟨0, 1, 0, 0, 0, 1, 0, 0⟩), (Int.ofNat 20000, ⟨0, 0, 1, 0, 0, 1, 0, 0⟩), (Int.negSucc 59999, ⟨0, 1, 0, 0, 0, 0, 1, 0⟩), (Int.ofNat 20000, ⟨0, 0, 1, 0, 0, 0, 1, 0⟩), (Int.ofNat 2307, ⟨1, 0, 0, 0, 0, 0, 0, 1⟩), (Int.negSucc 2306, ⟨0, 0, 0, 1, 0, 0, 0, 1⟩), (Int.ofNat 60000, ⟨0, 1, 0, 0, 1, 0, 0, 1⟩), (Int.negSucc 19999, ⟨0, 0, 1, 0, 1, 0, 0, 1⟩), (Int.negSucc 19999, ⟨1, 0, 0, 0, 0, 1, 0, 1⟩), (Int.ofNat 20000, ⟨0, 0, 0, 1, 0, 1, 0, 1⟩), (Int.negSucc 19999, ⟨1, 0, 0, 0, 0, 0, 1, 1⟩), (Int.ofNat 20000, ⟨0, 0, 0, 1, 0, 0, 1, 1⟩)]
  productDenominator := 120000
  multiplierDenominator := 120000
  sqrtCorrection := [(Int.negSucc 2399999999, ⟨1, 0, 0, 0, 1, 0, 0, 0⟩), (Int.ofNat 2400000000, ⟨0, 0, 0, 1, 1, 0, 0, 0⟩)]
theorem checked : certificate.check PrimitiveData.polynomial = true := by
  unfold MultiplierCertificate.check
  decide +kernel

theorem nonnegative (x : Fin 8 → ℝ) (hroot : (x 7)^2=3) (hregion : PrimitiveData.Region x) :
    0 ≤ eval x certificate.polynomial :=
  MultiplierCertificate.nonnegative certificate PrimitiveData.polynomial checked
    (by decide +kernel) (by decide +kernel) x hroot hregion
#print axioms nonnegative
end M056
namespace M057
noncomputable def certificate : MultiplierCertificate where
  labels := [.sector1Rot2, .denominator2]
  polynomial := [(Int.ofNat 6921, ⟨0, 1, 0, 0, 0, 0, 0, 0⟩), (Int.negSucc 2306, ⟨0, 0, 1, 0, 0, 0, 0, 0⟩), (Int.negSucc 59999, ⟨1, 0, 0, 0, 1, 0, 0, 0⟩), (Int.ofNat 60000, ⟨0, 0, 0, 1, 1, 0, 0, 0⟩), (Int.negSucc 59999, ⟨0, 1, 0, 0, 0, 1, 0, 0⟩), (Int.ofNat 20000, ⟨0, 0, 1, 0, 0, 1, 0, 0⟩), (Int.negSucc 59999, ⟨0, 1, 0, 0, 0, 0, 1, 0⟩), (Int.ofNat 20000, ⟨0, 0, 1, 0, 0, 0, 1, 0⟩), (Int.ofNat 2307, ⟨1, 0, 0, 0, 0, 0, 0, 1⟩), (Int.negSucc 2306, ⟨0, 0, 0, 1, 0, 0, 0, 1⟩), (Int.negSucc 59999, ⟨0, 1, 0, 0, 1, 0, 0, 1⟩), (Int.ofNat 20000, ⟨0, 0, 1, 0, 1, 0, 0, 1⟩), (Int.negSucc 19999, ⟨1, 0, 0, 0, 0, 1, 0, 1⟩), (Int.ofNat 20000, ⟨0, 0, 0, 1, 0, 1, 0, 1⟩), (Int.negSucc 19999, ⟨1, 0, 0, 0, 0, 0, 1, 1⟩), (Int.ofNat 20000, ⟨0, 0, 0, 1, 0, 0, 1, 1⟩)]
  productDenominator := 120000
  multiplierDenominator := 120000
  sqrtCorrection := [(Int.ofNat 2400000000, ⟨1, 0, 0, 0, 1, 0, 0, 0⟩), (Int.negSucc 2399999999, ⟨0, 0, 0, 1, 1, 0, 0, 0⟩)]
theorem checked : certificate.check PrimitiveData.polynomial = true := by
  unfold MultiplierCertificate.check
  decide +kernel

theorem nonnegative (x : Fin 8 → ℝ) (hroot : (x 7)^2=3) (hregion : PrimitiveData.Region x) :
    0 ≤ eval x certificate.polynomial :=
  MultiplierCertificate.nonnegative certificate PrimitiveData.polynomial checked
    (by decide +kernel) (by decide +kernel) x hroot hregion
#print axioms nonnegative
end M057
namespace M058
noncomputable def certificate : MultiplierCertificate where
  labels := [.sector1Rot2, .hLower]
  polynomial := [(Int.ofNat 3, ⟨0, 1, 0, 0, 0, 0, 0, 0⟩), (Int.negSucc 0, ⟨0, 0, 1, 0, 0, 0, 0, 0⟩), (Int.negSucc 2, ⟨0, 1, 0, 0, 0, 0, 1, 0⟩), (Int.ofNat 1, ⟨0, 0, 1, 0, 0, 0, 1, 0⟩), (Int.ofNat 1, ⟨1, 0, 0, 0, 0, 0, 0, 1⟩), (Int.negSucc 0, ⟨0, 0, 0, 1, 0, 0, 0, 1⟩), (Int.negSucc 0, ⟨1, 0, 0, 0, 0, 0, 1, 1⟩), (Int.ofNat 1, ⟨0, 0, 0, 1, 0, 0, 1, 1⟩)]
  productDenominator := 4
  multiplierDenominator := 4
  sqrtCorrection := []
theorem checked : certificate.check PrimitiveData.polynomial = true := by
  unfold MultiplierCertificate.check
  decide +kernel

theorem nonnegative (x : Fin 8 → ℝ) (hroot : (x 7)^2=3) (hregion : PrimitiveData.Region x) :
    0 ≤ eval x certificate.polynomial :=
  MultiplierCertificate.nonnegative certificate PrimitiveData.polynomial checked
    (by decide +kernel) (by decide +kernel) x hroot hregion
#print axioms nonnegative
end M058
namespace M059
noncomputable def certificate : MultiplierCertificate where
  labels := [.sector1Rot2, .hUpper]
  polynomial := [(Int.negSucc 35, ⟨0, 1, 0, 0, 0, 0, 0, 0⟩), (Int.ofNat 12, ⟨0, 0, 1, 0, 0, 0, 0, 0⟩), (Int.ofNat 15, ⟨0, 1, 0, 0, 0, 0, 1, 0⟩), (Int.negSucc 4, ⟨0, 0, 1, 0, 0, 0, 1, 0⟩), (Int.negSucc 11, ⟨1, 0, 0, 0, 0, 0, 0, 1⟩), (Int.ofNat 12, ⟨0, 0, 0, 1, 0, 0, 0, 1⟩), (Int.ofNat 5, ⟨1, 0, 0, 0, 0, 0, 1, 1⟩), (Int.negSucc 4, ⟨0, 0, 0, 1, 0, 0, 1, 1⟩)]
  productDenominator := 20
  multiplierDenominator := 20
  sqrtCorrection := []
theorem checked : certificate.check PrimitiveData.polynomial = true := by
  unfold MultiplierCertificate.check
  decide +kernel

theorem nonnegative (x : Fin 8 → ℝ) (hroot : (x 7)^2=3) (hregion : PrimitiveData.Region x) :
    0 ≤ eval x certificate.polynomial :=
  MultiplierCertificate.nonnegative certificate PrimitiveData.polynomial checked
    (by decide +kernel) (by decide +kernel) x hroot hregion
#print axioms nonnegative
end M059
namespace M060
noncomputable def certificate : MultiplierCertificate where
  labels := [.sector2Rot2, .denominator0]
  polynomial := [(Int.ofNat 2307, ⟨0, 0, 1, 0, 0, 0, 0, 0⟩), (Int.ofNat 40000, ⟨0, 0, 1, 0, 0, 1, 0, 0⟩), (Int.negSucc 19999, ⟨0, 0, 1, 0, 0, 0, 1, 0⟩), (Int.negSucc 2306, ⟨1, 0, 0, 0, 0, 0, 0, 1⟩), (Int.negSucc 39999, ⟨1, 0, 0, 0, 0, 1, 0, 1⟩), (Int.ofNat 20000, ⟨1, 0, 0, 0, 0, 0, 1, 1⟩)]
  productDenominator := 30000
  multiplierDenominator := 30000
  sqrtCorrection := []
theorem checked : certificate.check PrimitiveData.polynomial = true := by
  unfold MultiplierCertificate.check
  decide +kernel

theorem nonnegative (x : Fin 8 → ℝ) (hroot : (x 7)^2=3) (hregion : PrimitiveData.Region x) :
    0 ≤ eval x certificate.polynomial :=
  MultiplierCertificate.nonnegative certificate PrimitiveData.polynomial checked
    (by decide +kernel) (by decide +kernel) x hroot hregion
#print axioms nonnegative
end M060
namespace M061
noncomputable def certificate : MultiplierCertificate where
  labels := [.sector2Rot2, .denominator1]
  polynomial := [(Int.ofNat 2307, ⟨0, 0, 1, 0, 0, 0, 0, 0⟩), (Int.negSucc 59999, ⟨1, 0, 0, 0, 1, 0, 0, 0⟩), (Int.negSucc 19999, ⟨0, 0, 1, 0, 0, 1, 0, 0⟩), (Int.negSucc 19999, ⟨0, 0, 1, 0, 0, 0, 1, 0⟩), (Int.negSucc 2306, ⟨1, 0, 0, 0, 0, 0, 0, 1⟩), (Int.ofNat 20000, ⟨0, 0, 1, 0, 1, 0, 0, 1⟩), (Int.ofNat 20000, ⟨1, 0, 0, 0, 0, 1, 0, 1⟩), (Int.ofNat 20000, ⟨1, 0, 0, 0, 0, 0, 1, 1⟩)]
  productDenominator := 30000
  multiplierDenominator := 30000
  sqrtCorrection := [(Int.ofNat 600000000, ⟨1, 0, 0, 0, 1, 0, 0, 0⟩)]
theorem checked : certificate.check PrimitiveData.polynomial = true := by
  unfold MultiplierCertificate.check
  decide +kernel

theorem nonnegative (x : Fin 8 → ℝ) (hroot : (x 7)^2=3) (hregion : PrimitiveData.Region x) :
    0 ≤ eval x certificate.polynomial :=
  MultiplierCertificate.nonnegative certificate PrimitiveData.polynomial checked
    (by decide +kernel) (by decide +kernel) x hroot hregion
#print axioms nonnegative
end M061
namespace M062
noncomputable def certificate : MultiplierCertificate where
  labels := [.sector2Rot2, .denominator2]
  polynomial := [(Int.ofNat 2307, ⟨0, 0, 1, 0, 0, 0, 0, 0⟩), (Int.ofNat 60000, ⟨1, 0, 0, 0, 1, 0, 0, 0⟩), (Int.negSucc 19999, ⟨0, 0, 1, 0, 0, 1, 0, 0⟩), (Int.negSucc 19999, ⟨0, 0, 1, 0, 0, 0, 1, 0⟩), (Int.negSucc 2306, ⟨1, 0, 0, 0, 0, 0, 0, 1⟩), (Int.negSucc 19999, ⟨0, 0, 1, 0, 1, 0, 0, 1⟩), (Int.ofNat 20000, ⟨1, 0, 0, 0, 0, 1, 0, 1⟩), (Int.ofNat 20000, ⟨1, 0, 0, 0, 0, 0, 1, 1⟩)]
  productDenominator := 30000
  multiplierDenominator := 30000
  sqrtCorrection := [(Int.negSucc 599999999, ⟨1, 0, 0, 0, 1, 0, 0, 0⟩)]
theorem checked : certificate.check PrimitiveData.polynomial = true := by
  unfold MultiplierCertificate.check
  decide +kernel

theorem nonnegative (x : Fin 8 → ℝ) (hroot : (x 7)^2=3) (hregion : PrimitiveData.Region x) :
    0 ≤ eval x certificate.polynomial :=
  MultiplierCertificate.nonnegative certificate PrimitiveData.polynomial checked
    (by decide +kernel) (by decide +kernel) x hroot hregion
#print axioms nonnegative
end M062
namespace M063
noncomputable def certificate : MultiplierCertificate where
  labels := [.sector2Rot2, .hLower]
  polynomial := [(Int.ofNat 1, ⟨0, 0, 1, 0, 0, 0, 0, 0⟩), (Int.negSucc 0, ⟨0, 0, 1, 0, 0, 0, 1, 0⟩), (Int.negSucc 0, ⟨1, 0, 0, 0, 0, 0, 0, 1⟩), (Int.ofNat 1, ⟨1, 0, 0, 0, 0, 0, 1, 1⟩)]
  productDenominator := 1
  multiplierDenominator := 1
  sqrtCorrection := []
theorem checked : certificate.check PrimitiveData.polynomial = true := by
  unfold MultiplierCertificate.check
  decide +kernel

theorem nonnegative (x : Fin 8 → ℝ) (hroot : (x 7)^2=3) (hregion : PrimitiveData.Region x) :
    0 ≤ eval x certificate.polynomial :=
  MultiplierCertificate.nonnegative certificate PrimitiveData.polynomial checked
    (by decide +kernel) (by decide +kernel) x hroot hregion
#print axioms nonnegative
end M063
namespace M064
noncomputable def certificate : MultiplierCertificate where
  labels := [.sector2Rot2, .hUpper]
  polynomial := [(Int.negSucc 11, ⟨0, 0, 1, 0, 0, 0, 0, 0⟩), (Int.ofNat 5, ⟨0, 0, 1, 0, 0, 0, 1, 0⟩), (Int.ofNat 12, ⟨1, 0, 0, 0, 0, 0, 0, 1⟩), (Int.negSucc 4, ⟨1, 0, 0, 0, 0, 0, 1, 1⟩)]
  productDenominator := 5
  multiplierDenominator := 5
  sqrtCorrection := []
theorem checked : certificate.check PrimitiveData.polynomial = true := by
  unfold MultiplierCertificate.check
  decide +kernel

theorem nonnegative (x : Fin 8 → ℝ) (hroot : (x 7)^2=3) (hregion : PrimitiveData.Region x) :
    0 ≤ eval x certificate.polynomial :=
  MultiplierCertificate.nonnegative certificate PrimitiveData.polynomial checked
    (by decide +kernel) (by decide +kernel) x hroot hregion
#print axioms nonnegative
end M064
namespace M065
noncomputable def certificate : MultiplierCertificate where
  labels := [.denominator0, .denominator1]
  polynomial := [(Int.ofNat 5322249, ⟨0, 0, 0, 0, 0, 0, 0, 0⟩), (Int.ofNat 46140000, ⟨0, 0, 0, 0, 0, 1, 0, 0⟩), (Int.negSucc 799999999, ⟨0, 0, 0, 0, 0, 2, 0, 0⟩), (Int.negSucc 92279999, ⟨0, 0, 0, 0, 0, 0, 1, 0⟩), (Int.negSucc 399999999, ⟨0, 0, 0, 0, 0, 1, 1, 0⟩), (Int.ofNat 400000000, ⟨0, 0, 0, 0, 0, 0, 2, 0⟩), (Int.ofNat 46140000, ⟨0, 0, 0, 0, 1, 0, 0, 1⟩), (Int.ofNat 800000000, ⟨0, 0, 0, 0, 1, 1, 0, 1⟩), (Int.negSucc 399999999, ⟨0, 0, 0, 0, 1, 0, 1, 1⟩)]
  productDenominator := 900000000
  multiplierDenominator := 900000000
  sqrtCorrection := []
theorem checked : certificate.check PrimitiveData.polynomial = true := by
  unfold MultiplierCertificate.check
  decide +kernel

theorem nonnegative (x : Fin 8 → ℝ) (hroot : (x 7)^2=3) (hregion : PrimitiveData.Region x) :
    0 ≤ eval x certificate.polynomial :=
  MultiplierCertificate.nonnegative certificate PrimitiveData.polynomial checked
    (by decide +kernel) (by decide +kernel) x hroot hregion
#print axioms nonnegative
end M065
namespace M066
noncomputable def certificate : MultiplierCertificate where
  labels := [.denominator0, .denominator2]
  polynomial := [(Int.ofNat 5322249, ⟨0, 0, 0, 0, 0, 0, 0, 0⟩), (Int.ofNat 46140000, ⟨0, 0, 0, 0, 0, 1, 0, 0⟩), (Int.negSucc 799999999, ⟨0, 0, 0, 0, 0, 2, 0, 0⟩), (Int.negSucc 92279999, ⟨0, 0, 0, 0, 0, 0, 1, 0⟩), (Int.negSucc 399999999, ⟨0, 0, 0, 0, 0, 1, 1, 0⟩), (Int.ofNat 400000000, ⟨0, 0, 0, 0, 0, 0, 2, 0⟩), (Int.negSucc 46139999, ⟨0, 0, 0, 0, 1, 0, 0, 1⟩), (Int.negSucc 799999999, ⟨0, 0, 0, 0, 1, 1, 0, 1⟩), (Int.ofNat 400000000, ⟨0, 0, 0, 0, 1, 0, 1, 1⟩)]
  productDenominator := 900000000
  multiplierDenominator := 900000000
  sqrtCorrection := []
theorem checked : certificate.check PrimitiveData.polynomial = true := by
  unfold MultiplierCertificate.check
  decide +kernel

theorem nonnegative (x : Fin 8 → ℝ) (hroot : (x 7)^2=3) (hregion : PrimitiveData.Region x) :
    0 ≤ eval x certificate.polynomial :=
  MultiplierCertificate.nonnegative certificate PrimitiveData.polynomial checked
    (by decide +kernel) (by decide +kernel) x hroot hregion
#print axioms nonnegative
end M066
namespace M067
noncomputable def certificate : MultiplierCertificate where
  labels := [.denominator0, .hLower]
  polynomial := [(Int.ofNat 2307, ⟨0, 0, 0, 0, 0, 0, 0, 0⟩), (Int.ofNat 40000, ⟨0, 0, 0, 0, 0, 1, 0, 0⟩), (Int.negSucc 22306, ⟨0, 0, 0, 0, 0, 0, 1, 0⟩), (Int.negSucc 39999, ⟨0, 0, 0, 0, 0, 1, 1, 0⟩), (Int.ofNat 20000, ⟨0, 0, 0, 0, 0, 0, 2, 0⟩)]
  productDenominator := 30000
  multiplierDenominator := 30000
  sqrtCorrection := []
theorem checked : certificate.check PrimitiveData.polynomial = true := by
  unfold MultiplierCertificate.check
  decide +kernel

theorem nonnegative (x : Fin 8 → ℝ) (hroot : (x 7)^2=3) (hregion : PrimitiveData.Region x) :
    0 ≤ eval x certificate.polynomial :=
  MultiplierCertificate.nonnegative certificate PrimitiveData.polynomial checked
    (by decide +kernel) (by decide +kernel) x hroot hregion
#print axioms nonnegative
end M067
namespace M068
noncomputable def certificate : MultiplierCertificate where
  labels := [.denominator0, .hUpper]
  polynomial := [(Int.negSucc 27683, ⟨0, 0, 0, 0, 0, 0, 0, 0⟩), (Int.negSucc 479999, ⟨0, 0, 0, 0, 0, 1, 0, 0⟩), (Int.ofNat 251535, ⟨0, 0, 0, 0, 0, 0, 1, 0⟩), (Int.ofNat 200000, ⟨0, 0, 0, 0, 0, 1, 1, 0⟩), (Int.negSucc 99999, ⟨0, 0, 0, 0, 0, 0, 2, 0⟩)]
  productDenominator := 150000
  multiplierDenominator := 150000
  sqrtCorrection := []
theorem checked : certificate.check PrimitiveData.polynomial = true := by
  unfold MultiplierCertificate.check
  decide +kernel

theorem nonnegative (x : Fin 8 → ℝ) (hroot : (x 7)^2=3) (hregion : PrimitiveData.Region x) :
    0 ≤ eval x certificate.polynomial :=
  MultiplierCertificate.nonnegative certificate PrimitiveData.polynomial checked
    (by decide +kernel) (by decide +kernel) x hroot hregion
#print axioms nonnegative
end M068
namespace M069
noncomputable def certificate : MultiplierCertificate where
  labels := [.denominator1, .denominator2]
  polynomial := [(Int.ofNat 5322249, ⟨0, 0, 0, 0, 0, 0, 0, 0⟩), (Int.negSucc 1199999999, ⟨0, 0, 0, 0, 2, 0, 0, 0⟩), (Int.negSucc 92279999, ⟨0, 0, 0, 0, 0, 1, 0, 0⟩), (Int.ofNat 400000000, ⟨0, 0, 0, 0, 0, 2, 0, 0⟩), (Int.negSucc 92279999, ⟨0, 0, 0, 0, 0, 0, 1, 0⟩), (Int.ofNat 800000000, ⟨0, 0, 0, 0, 0, 1, 1, 0⟩), (Int.ofNat 400000000, ⟨0, 0, 0, 0, 0, 0, 2, 0⟩)]
  productDenominator := 900000000
  multiplierDenominator := 900000000
  sqrtCorrection := [(Int.ofNat 360000000000000000, ⟨0, 0, 0, 0, 2, 0, 0, 0⟩)]
theorem checked : certificate.check PrimitiveData.polynomial = true := by
  unfold MultiplierCertificate.check
  decide +kernel

theorem nonnegative (x : Fin 8 → ℝ) (hroot : (x 7)^2=3) (hregion : PrimitiveData.Region x) :
    0 ≤ eval x certificate.polynomial :=
  MultiplierCertificate.nonnegative certificate PrimitiveData.polynomial checked
    (by decide +kernel) (by decide +kernel) x hroot hregion
#print axioms nonnegative
end M069
namespace M070
noncomputable def certificate : MultiplierCertificate where
  labels := [.denominator1, .hLower]
  polynomial := [(Int.ofNat 2307, ⟨0, 0, 0, 0, 0, 0, 0, 0⟩), (Int.negSucc 19999, ⟨0, 0, 0, 0, 0, 1, 0, 0⟩), (Int.negSucc 22306, ⟨0, 0, 0, 0, 0, 0, 1, 0⟩), (Int.ofNat 20000, ⟨0, 0, 0, 0, 0, 1, 1, 0⟩), (Int.ofNat 20000, ⟨0, 0, 0, 0, 0, 0, 2, 0⟩), (Int.ofNat 20000, ⟨0, 0, 0, 0, 1, 0, 0, 1⟩), (Int.negSucc 19999, ⟨0, 0, 0, 0, 1, 0, 1, 1⟩)]
  productDenominator := 30000
  multiplierDenominator := 30000
  sqrtCorrection := []
theorem checked : certificate.check PrimitiveData.polynomial = true := by
  unfold MultiplierCertificate.check
  decide +kernel

theorem nonnegative (x : Fin 8 → ℝ) (hroot : (x 7)^2=3) (hregion : PrimitiveData.Region x) :
    0 ≤ eval x certificate.polynomial :=
  MultiplierCertificate.nonnegative certificate PrimitiveData.polynomial checked
    (by decide +kernel) (by decide +kernel) x hroot hregion
#print axioms nonnegative
end M070
namespace M071
noncomputable def certificate : MultiplierCertificate where
  labels := [.denominator1, .hUpper]
  polynomial := [(Int.negSucc 27683, ⟨0, 0, 0, 0, 0, 0, 0, 0⟩), (Int.ofNat 240000, ⟨0, 0, 0, 0, 0, 1, 0, 0⟩), (Int.ofNat 251535, ⟨0, 0, 0, 0, 0, 0, 1, 0⟩), (Int.negSucc 99999, ⟨0, 0, 0, 0, 0, 1, 1, 0⟩), (Int.negSucc 99999, ⟨0, 0, 0, 0, 0, 0, 2, 0⟩), (Int.negSucc 239999, ⟨0, 0, 0, 0, 1, 0, 0, 1⟩), (Int.ofNat 100000, ⟨0, 0, 0, 0, 1, 0, 1, 1⟩)]
  productDenominator := 150000
  multiplierDenominator := 150000
  sqrtCorrection := []
theorem checked : certificate.check PrimitiveData.polynomial = true := by
  unfold MultiplierCertificate.check
  decide +kernel

theorem nonnegative (x : Fin 8 → ℝ) (hroot : (x 7)^2=3) (hregion : PrimitiveData.Region x) :
    0 ≤ eval x certificate.polynomial :=
  MultiplierCertificate.nonnegative certificate PrimitiveData.polynomial checked
    (by decide +kernel) (by decide +kernel) x hroot hregion
#print axioms nonnegative
end M071
namespace M072
noncomputable def certificate : MultiplierCertificate where
  labels := [.denominator2, .hLower]
  polynomial := [(Int.ofNat 2307, ⟨0, 0, 0, 0, 0, 0, 0, 0⟩), (Int.negSucc 19999, ⟨0, 0, 0, 0, 0, 1, 0, 0⟩), (Int.negSucc 22306, ⟨0, 0, 0, 0, 0, 0, 1, 0⟩), (Int.ofNat 20000, ⟨0, 0, 0, 0, 0, 1, 1, 0⟩), (Int.ofNat 20000, ⟨0, 0, 0, 0, 0, 0, 2, 0⟩), (Int.negSucc 19999, ⟨0, 0, 0, 0, 1, 0, 0, 1⟩), (Int.ofNat 20000, ⟨0, 0, 0, 0, 1, 0, 1, 1⟩)]
  productDenominator := 30000
  multiplierDenominator := 30000
  sqrtCorrection := []
theorem checked : certificate.check PrimitiveData.polynomial = true := by
  unfold MultiplierCertificate.check
  decide +kernel

theorem nonnegative (x : Fin 8 → ℝ) (hroot : (x 7)^2=3) (hregion : PrimitiveData.Region x) :
    0 ≤ eval x certificate.polynomial :=
  MultiplierCertificate.nonnegative certificate PrimitiveData.polynomial checked
    (by decide +kernel) (by decide +kernel) x hroot hregion
#print axioms nonnegative
end M072
namespace M073
noncomputable def certificate : MultiplierCertificate where
  labels := [.denominator2, .hUpper]
  polynomial := [(Int.negSucc 27683, ⟨0, 0, 0, 0, 0, 0, 0, 0⟩), (Int.ofNat 240000, ⟨0, 0, 0, 0, 0, 1, 0, 0⟩), (Int.ofNat 251535, ⟨0, 0, 0, 0, 0, 0, 1, 0⟩), (Int.negSucc 99999, ⟨0, 0, 0, 0, 0, 1, 1, 0⟩), (Int.negSucc 99999, ⟨0, 0, 0, 0, 0, 0, 2, 0⟩), (Int.ofNat 240000, ⟨0, 0, 0, 0, 1, 0, 0, 1⟩), (Int.negSucc 99999, ⟨0, 0, 0, 0, 1, 0, 1, 1⟩)]
  productDenominator := 150000
  multiplierDenominator := 150000
  sqrtCorrection := []
theorem checked : certificate.check PrimitiveData.polynomial = true := by
  unfold MultiplierCertificate.check
  decide +kernel

theorem nonnegative (x : Fin 8 → ℝ) (hroot : (x 7)^2=3) (hregion : PrimitiveData.Region x) :
    0 ≤ eval x certificate.polynomial :=
  MultiplierCertificate.nonnegative certificate PrimitiveData.polynomial checked
    (by decide +kernel) (by decide +kernel) x hroot hregion
#print axioms nonnegative
end M073
namespace M074
noncomputable def certificate : MultiplierCertificate where
  labels := [.hLower, .hUpper]
  polynomial := [(Int.negSucc 11, ⟨0, 0, 0, 0, 0, 0, 0, 0⟩), (Int.ofNat 17, ⟨0, 0, 0, 0, 0, 0, 1, 0⟩), (Int.negSucc 4, ⟨0, 0, 0, 0, 0, 0, 2, 0⟩)]
  productDenominator := 5
  multiplierDenominator := 5
  sqrtCorrection := []
theorem checked : certificate.check PrimitiveData.polynomial = true := by
  unfold MultiplierCertificate.check
  decide +kernel

theorem nonnegative (x : Fin 8 → ℝ) (hroot : (x 7)^2=3) (hregion : PrimitiveData.Region x) :
    0 ≤ eval x certificate.polynomial :=
  MultiplierCertificate.nonnegative certificate PrimitiveData.polynomial checked
    (by decide +kernel) (by decide +kernel) x hroot hregion
#print axioms nonnegative
end M074
end Certificate.MultiplierProofs
