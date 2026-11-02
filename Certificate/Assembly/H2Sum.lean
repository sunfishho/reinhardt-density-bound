import Certificate.SOS.H2B000Data
import Certificate.SOS.H2B001Data
import Certificate.SOS.H2B002Data
import Certificate.SOS.H2B003Data
import Certificate.SOS.H2B004Data
import Certificate.SOS.H2B005Data
import Certificate.SOS.H2B006Data
import Certificate.SOS.H2B007Data
import Certificate.SOS.H2B008Data
import Certificate.SOS.H2B009Data
import Certificate.SOS.H2B010Data
import Certificate.SOS.H2B011Data
import Certificate.SOS.H2B012Data
import Certificate.SOS.H2B013Data
import Certificate.SOS.H2B014Data
import Certificate.SOS.H2B015Data
import Certificate.SOS.H2B016Data
import Certificate.SOS.H2B017Data
import Certificate.SOS.H2B018Data
import Certificate.SOS.H2B019Data
import Certificate.SOS.H2B020Data
import Certificate.SOS.H2B021Data
import Certificate.SOS.H2B022Data
import Certificate.Identities.H2Data
namespace Certificate.Assembly.H2
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
noncomputable def blocks : List Polynomial := [
  scale Certificate.SOS.H2B000.weight Certificate.SOS.H2B000.weighted,
  scale Certificate.SOS.H2B001.weight Certificate.SOS.H2B001.weighted,
  scale Certificate.SOS.H2B002.weight Certificate.SOS.H2B002.weighted,
  scale Certificate.SOS.H2B003.weight Certificate.SOS.H2B003.weighted,
  scale Certificate.SOS.H2B004.weight Certificate.SOS.H2B004.weighted,
  scale Certificate.SOS.H2B005.weight Certificate.SOS.H2B005.weighted,
  scale Certificate.SOS.H2B006.weight Certificate.SOS.H2B006.weighted,
  scale Certificate.SOS.H2B007.weight Certificate.SOS.H2B007.weighted,
  scale Certificate.SOS.H2B008.weight Certificate.SOS.H2B008.weighted,
  scale Certificate.SOS.H2B009.weight Certificate.SOS.H2B009.weighted,
  scale Certificate.SOS.H2B010.weight Certificate.SOS.H2B010.weighted,
  scale Certificate.SOS.H2B011.weight Certificate.SOS.H2B011.weighted,
  scale Certificate.SOS.H2B012.weight Certificate.SOS.H2B012.weighted,
  scale Certificate.SOS.H2B013.weight Certificate.SOS.H2B013.weighted,
  scale Certificate.SOS.H2B014.weight Certificate.SOS.H2B014.weighted,
  scale Certificate.SOS.H2B015.weight Certificate.SOS.H2B015.weighted,
  scale Certificate.SOS.H2B016.weight Certificate.SOS.H2B016.weighted,
  scale Certificate.SOS.H2B017.weight Certificate.SOS.H2B017.weighted,
  scale Certificate.SOS.H2B018.weight Certificate.SOS.H2B018.weighted,
  scale Certificate.SOS.H2B019.weight Certificate.SOS.H2B019.weighted,
  scale Certificate.SOS.H2B020.weight Certificate.SOS.H2B020.weighted,
  scale Certificate.SOS.H2B021.weight Certificate.SOS.H2B021.weighted,
  scale Certificate.SOS.H2B022.weight Certificate.SOS.H2B022.weighted]
theorem sum_check : checkEqual (collapse 20 blocks) Certificate.Identities.H2.recordedSOS = true := by
  decide +kernel

theorem sum_identity (x : Fin 8 → ℝ) :
    eval x Certificate.Identities.H2.recordedSOS = (blocks.map (eval x)).sum := by
  have he := eq_of_check x _ _ sum_check
  simpa only [eval_collapse,evalMany_eq_sum_map] using he.symm
#print axioms sum_identity
end Certificate.Assembly.H2
