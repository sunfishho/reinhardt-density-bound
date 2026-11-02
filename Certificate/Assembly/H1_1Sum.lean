import Certificate.Assembly.SumTrees.H1_1.Chunk009
import Certificate.Identities.H1_1Data
import Certificate.MergeArithmetic
namespace Certificate.Assembly.H1_1
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
noncomputable def blocks : List Polynomial := [
  (scale Certificate.SOS.H1_1B000.weight Certificate.SOS.H1_1B000.weighted),
  (scale Certificate.SOS.H1_1B001.weight Certificate.SOS.H1_1B001.weighted),
  (scale Certificate.SOS.H1_1B002.weight Certificate.SOS.H1_1B002.weighted),
  (scale Certificate.SOS.H1_1B003.weight Certificate.SOS.H1_1B003.weighted),
  (scale Certificate.SOS.H1_1B004.weight Certificate.SOS.H1_1B004.weighted),
  (scale Certificate.SOS.H1_1B005.weight Certificate.SOS.H1_1B005.weighted),
  (scale Certificate.SOS.H1_1B006.weight Certificate.SOS.H1_1B006.weighted),
  (scale Certificate.SOS.H1_1B007.weight Certificate.SOS.H1_1B007.weighted),
  (scale Certificate.SOS.H1_1B008.weight Certificate.SOS.H1_1B008.weighted),
  (scale Certificate.SOS.H1_1B009.weight Certificate.SOS.H1_1B009.weighted),
  (scale Certificate.SOS.H1_1B010.weight Certificate.SOS.H1_1B010.weighted),
  (scale Certificate.SOS.H1_1B011.weight Certificate.SOS.H1_1B011.weighted),
  (scale Certificate.SOS.H1_1B012.weight Certificate.SOS.H1_1B012.weighted),
  (scale Certificate.SOS.H1_1B013.weight Certificate.SOS.H1_1B013.weighted),
  (scale Certificate.SOS.H1_1B014.weight Certificate.SOS.H1_1B014.weighted),
  (scale Certificate.SOS.H1_1B015.weight Certificate.SOS.H1_1B015.weighted),
  (scale Certificate.SOS.H1_1B016.weight Certificate.SOS.H1_1B016.weighted),
  (scale Certificate.SOS.H1_1B017.weight Certificate.SOS.H1_1B017.weighted),
  (scale Certificate.SOS.H1_1B018.weight Certificate.SOS.H1_1B018.weighted),
  (scale Certificate.SOS.H1_1B019.weight Certificate.SOS.H1_1B019.weighted),
  (scale Certificate.SOS.H1_1B020.weight Certificate.SOS.H1_1B020.weighted),
  (scale Certificate.SOS.H1_1B021.weight Certificate.SOS.H1_1B021.weighted),
  (scale Certificate.SOS.H1_1B022.weight Certificate.SOS.H1_1B022.weighted),
  (scale Certificate.SOS.H1_1B023.weight Certificate.SOS.H1_1B023.weighted),
  (scale Certificate.SOS.H1_1B024.weight Certificate.SOS.H1_1B024.weighted),
  (scale Certificate.SOS.H1_1B025.weight Certificate.SOS.H1_1B025.weighted),
  (scale Certificate.SOS.H1_1B026.weight Certificate.SOS.H1_1B026.weighted),
  (scale Certificate.SOS.H1_1B027.weight Certificate.SOS.H1_1B027.weighted),
  (scale Certificate.SOS.H1_1B028.weight Certificate.SOS.H1_1B028.weighted),
  (scale Certificate.SOS.H1_1B029.weight Certificate.SOS.H1_1B029.weighted),
  (scale Certificate.SOS.H1_1B030.weight Certificate.SOS.H1_1B030.weighted),
  (scale Certificate.SOS.H1_1B031.weight Certificate.SOS.H1_1B031.weighted),
  (scale Certificate.SOS.H1_1B032.weight Certificate.SOS.H1_1B032.weighted),
  (scale Certificate.SOS.H1_1B033.weight Certificate.SOS.H1_1B033.weighted),
  (scale Certificate.SOS.H1_1B034.weight Certificate.SOS.H1_1B034.weighted),
  (scale Certificate.SOS.H1_1B035.weight Certificate.SOS.H1_1B035.weighted),
  (scale Certificate.SOS.H1_1B036.weight Certificate.SOS.H1_1B036.weighted),
  (scale Certificate.SOS.H1_1B037.weight Certificate.SOS.H1_1B037.weighted),
  (scale Certificate.SOS.H1_1B038.weight Certificate.SOS.H1_1B038.weighted),
  (scale Certificate.SOS.H1_1B039.weight Certificate.SOS.H1_1B039.weighted),
  (scale Certificate.SOS.H1_1B040.weight Certificate.SOS.H1_1B040.weighted),
  (scale Certificate.SOS.H1_1B041.weight Certificate.SOS.H1_1B041.weighted),
  (scale Certificate.SOS.H1_1B042.weight Certificate.SOS.H1_1B042.weighted),
  (scale Certificate.SOS.H1_1B043.weight Certificate.SOS.H1_1B043.weighted),
  (scale Certificate.SOS.H1_1B044.weight Certificate.SOS.H1_1B044.weighted),
  (scale Certificate.SOS.H1_1B045.weight Certificate.SOS.H1_1B045.weighted),
  (scale Certificate.SOS.H1_1B046.weight Certificate.SOS.H1_1B046.weighted),
  (scale Certificate.SOS.H1_1B047.weight Certificate.SOS.H1_1B047.weighted),
  (scale Certificate.SOS.H1_1B048.weight Certificate.SOS.H1_1B048.weighted),
  (scale Certificate.SOS.H1_1B049.weight Certificate.SOS.H1_1B049.weighted),
  (scale Certificate.SOS.H1_1B050.weight Certificate.SOS.H1_1B050.weighted),
  (scale Certificate.SOS.H1_1B051.weight Certificate.SOS.H1_1B051.weighted),
  (scale Certificate.SOS.H1_1B052.weight Certificate.SOS.H1_1B052.weighted),
  (scale Certificate.SOS.H1_1B053.weight Certificate.SOS.H1_1B053.weighted),
  (scale Certificate.SOS.H1_1B054.weight Certificate.SOS.H1_1B054.weighted),
  (scale Certificate.SOS.H1_1B055.weight Certificate.SOS.H1_1B055.weighted),
  (scale Certificate.SOS.H1_1B056.weight Certificate.SOS.H1_1B056.weighted),
  (scale Certificate.SOS.H1_1B057.weight Certificate.SOS.H1_1B057.weighted),
  (scale Certificate.SOS.H1_1B058.weight Certificate.SOS.H1_1B058.weighted),
  (scale Certificate.SOS.H1_1B059.weight Certificate.SOS.H1_1B059.weighted),
  (scale Certificate.SOS.H1_1B060.weight Certificate.SOS.H1_1B060.weighted),
  (scale Certificate.SOS.H1_1B061.weight Certificate.SOS.H1_1B061.weighted),
  (scale Certificate.SOS.H1_1B062.weight Certificate.SOS.H1_1B062.weighted),
  (scale Certificate.SOS.H1_1B063.weight Certificate.SOS.H1_1B063.weighted),
  (scale Certificate.SOS.H1_1B064.weight Certificate.SOS.H1_1B064.weighted),
  (scale Certificate.SOS.H1_1B065.weight Certificate.SOS.H1_1B065.weighted),
  (scale Certificate.SOS.H1_1B066.weight Certificate.SOS.H1_1B066.weighted),
  (scale Certificate.SOS.H1_1B067.weight Certificate.SOS.H1_1B067.weighted),
  (scale Certificate.SOS.H1_1B068.weight Certificate.SOS.H1_1B068.weighted),
  (scale Certificate.SOS.H1_1B069.weight Certificate.SOS.H1_1B069.weighted),
  (scale Certificate.SOS.H1_1B070.weight Certificate.SOS.H1_1B070.weighted),
  (scale Certificate.SOS.H1_1B071.weight Certificate.SOS.H1_1B071.weighted),
  (scale Certificate.SOS.H1_1B072.weight Certificate.SOS.H1_1B072.weighted),
  (scale Certificate.SOS.H1_1B073.weight Certificate.SOS.H1_1B073.weighted),
  (scale Certificate.SOS.H1_1B074.weight Certificate.SOS.H1_1B074.weighted)]
theorem sum_check : checkEqualMerged node073 Certificate.Identities.H1_1.recordedSOS = true := by
  decide +kernel

theorem sum_identity (x : Fin 8 → ℝ) :
    eval x Certificate.Identities.H1_1.recordedSOS = (blocks.map (eval x)).sum := by
  rw [← eq_of_checkMerged x _ _ sum_check, node073_total]
  simp only [blocks, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    add_zero, add_assoc]
#print axioms sum_identity
end Certificate.Assembly.H1_1
