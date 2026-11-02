import Certificate.Assembly.SumTrees.H1_2.Chunk009
import Certificate.Identities.H1_2Data
import Certificate.MergeArithmetic
namespace Certificate.Assembly.H1_2
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
noncomputable def blocks : List Polynomial := [
  (scale Certificate.SOS.H1_2B000.weight Certificate.SOS.H1_2B000.weighted),
  (scale Certificate.SOS.H1_2B001.weight Certificate.SOS.H1_2B001.weighted),
  (scale Certificate.SOS.H1_2B002.weight Certificate.SOS.H1_2B002.weighted),
  (scale Certificate.SOS.H1_2B003.weight Certificate.SOS.H1_2B003.weighted),
  (scale Certificate.SOS.H1_2B004.weight Certificate.SOS.H1_2B004.weighted),
  (scale Certificate.SOS.H1_2B005.weight Certificate.SOS.H1_2B005.weighted),
  (scale Certificate.SOS.H1_2B006.weight Certificate.SOS.H1_2B006.weighted),
  (scale Certificate.SOS.H1_2B007.weight Certificate.SOS.H1_2B007.weighted),
  (scale Certificate.SOS.H1_2B008.weight Certificate.SOS.H1_2B008.weighted),
  (scale Certificate.SOS.H1_2B009.weight Certificate.SOS.H1_2B009.weighted),
  (scale Certificate.SOS.H1_2B010.weight Certificate.SOS.H1_2B010.weighted),
  (scale Certificate.SOS.H1_2B011.weight Certificate.SOS.H1_2B011.weighted),
  (scale Certificate.SOS.H1_2B012.weight Certificate.SOS.H1_2B012.weighted),
  (scale Certificate.SOS.H1_2B013.weight Certificate.SOS.H1_2B013.weighted),
  (scale Certificate.SOS.H1_2B014.weight Certificate.SOS.H1_2B014.weighted),
  (scale Certificate.SOS.H1_2B015.weight Certificate.SOS.H1_2B015.weighted),
  (scale Certificate.SOS.H1_2B016.weight Certificate.SOS.H1_2B016.weighted),
  (scale Certificate.SOS.H1_2B017.weight Certificate.SOS.H1_2B017.weighted),
  (scale Certificate.SOS.H1_2B018.weight Certificate.SOS.H1_2B018.weighted),
  (scale Certificate.SOS.H1_2B019.weight Certificate.SOS.H1_2B019.weighted),
  (scale Certificate.SOS.H1_2B020.weight Certificate.SOS.H1_2B020.weighted),
  (scale Certificate.SOS.H1_2B021.weight Certificate.SOS.H1_2B021.weighted),
  (scale Certificate.SOS.H1_2B022.weight Certificate.SOS.H1_2B022.weighted),
  (scale Certificate.SOS.H1_2B023.weight Certificate.SOS.H1_2B023.weighted),
  (scale Certificate.SOS.H1_2B024.weight Certificate.SOS.H1_2B024.weighted),
  (scale Certificate.SOS.H1_2B025.weight Certificate.SOS.H1_2B025.weighted),
  (scale Certificate.SOS.H1_2B026.weight Certificate.SOS.H1_2B026.weighted),
  (scale Certificate.SOS.H1_2B027.weight Certificate.SOS.H1_2B027.weighted),
  (scale Certificate.SOS.H1_2B028.weight Certificate.SOS.H1_2B028.weighted),
  (scale Certificate.SOS.H1_2B029.weight Certificate.SOS.H1_2B029.weighted),
  (scale Certificate.SOS.H1_2B030.weight Certificate.SOS.H1_2B030.weighted),
  (scale Certificate.SOS.H1_2B031.weight Certificate.SOS.H1_2B031.weighted),
  (scale Certificate.SOS.H1_2B032.weight Certificate.SOS.H1_2B032.weighted),
  (scale Certificate.SOS.H1_2B033.weight Certificate.SOS.H1_2B033.weighted),
  (scale Certificate.SOS.H1_2B034.weight Certificate.SOS.H1_2B034.weighted),
  (scale Certificate.SOS.H1_2B035.weight Certificate.SOS.H1_2B035.weighted),
  (scale Certificate.SOS.H1_2B036.weight Certificate.SOS.H1_2B036.weighted),
  (scale Certificate.SOS.H1_2B037.weight Certificate.SOS.H1_2B037.weighted),
  (scale Certificate.SOS.H1_2B038.weight Certificate.SOS.H1_2B038.weighted),
  (scale Certificate.SOS.H1_2B039.weight Certificate.SOS.H1_2B039.weighted),
  (scale Certificate.SOS.H1_2B040.weight Certificate.SOS.H1_2B040.weighted),
  (scale Certificate.SOS.H1_2B041.weight Certificate.SOS.H1_2B041.weighted),
  (scale Certificate.SOS.H1_2B042.weight Certificate.SOS.H1_2B042.weighted),
  (scale Certificate.SOS.H1_2B043.weight Certificate.SOS.H1_2B043.weighted),
  (scale Certificate.SOS.H1_2B044.weight Certificate.SOS.H1_2B044.weighted),
  (scale Certificate.SOS.H1_2B045.weight Certificate.SOS.H1_2B045.weighted),
  (scale Certificate.SOS.H1_2B046.weight Certificate.SOS.H1_2B046.weighted),
  (scale Certificate.SOS.H1_2B047.weight Certificate.SOS.H1_2B047.weighted),
  (scale Certificate.SOS.H1_2B048.weight Certificate.SOS.H1_2B048.weighted),
  (scale Certificate.SOS.H1_2B049.weight Certificate.SOS.H1_2B049.weighted),
  (scale Certificate.SOS.H1_2B050.weight Certificate.SOS.H1_2B050.weighted),
  (scale Certificate.SOS.H1_2B051.weight Certificate.SOS.H1_2B051.weighted),
  (scale Certificate.SOS.H1_2B052.weight Certificate.SOS.H1_2B052.weighted),
  (scale Certificate.SOS.H1_2B053.weight Certificate.SOS.H1_2B053.weighted),
  (scale Certificate.SOS.H1_2B054.weight Certificate.SOS.H1_2B054.weighted),
  (scale Certificate.SOS.H1_2B055.weight Certificate.SOS.H1_2B055.weighted),
  (scale Certificate.SOS.H1_2B056.weight Certificate.SOS.H1_2B056.weighted),
  (scale Certificate.SOS.H1_2B057.weight Certificate.SOS.H1_2B057.weighted),
  (scale Certificate.SOS.H1_2B058.weight Certificate.SOS.H1_2B058.weighted),
  (scale Certificate.SOS.H1_2B059.weight Certificate.SOS.H1_2B059.weighted),
  (scale Certificate.SOS.H1_2B060.weight Certificate.SOS.H1_2B060.weighted),
  (scale Certificate.SOS.H1_2B061.weight Certificate.SOS.H1_2B061.weighted),
  (scale Certificate.SOS.H1_2B062.weight Certificate.SOS.H1_2B062.weighted),
  (scale Certificate.SOS.H1_2B063.weight Certificate.SOS.H1_2B063.weighted),
  (scale Certificate.SOS.H1_2B064.weight Certificate.SOS.H1_2B064.weighted),
  (scale Certificate.SOS.H1_2B065.weight Certificate.SOS.H1_2B065.weighted),
  (scale Certificate.SOS.H1_2B066.weight Certificate.SOS.H1_2B066.weighted),
  (scale Certificate.SOS.H1_2B067.weight Certificate.SOS.H1_2B067.weighted),
  (scale Certificate.SOS.H1_2B068.weight Certificate.SOS.H1_2B068.weighted),
  (scale Certificate.SOS.H1_2B069.weight Certificate.SOS.H1_2B069.weighted),
  (scale Certificate.SOS.H1_2B070.weight Certificate.SOS.H1_2B070.weighted),
  (scale Certificate.SOS.H1_2B071.weight Certificate.SOS.H1_2B071.weighted),
  (scale Certificate.SOS.H1_2B072.weight Certificate.SOS.H1_2B072.weighted),
  (scale Certificate.SOS.H1_2B073.weight Certificate.SOS.H1_2B073.weighted),
  (scale Certificate.SOS.H1_2B074.weight Certificate.SOS.H1_2B074.weighted)]
theorem sum_check : checkEqualMerged node073 Certificate.Identities.H1_2.recordedSOS = true := by
  decide +kernel

theorem sum_identity (x : Fin 8 → ℝ) :
    eval x Certificate.Identities.H1_2.recordedSOS = (blocks.map (eval x)).sum := by
  rw [← eq_of_checkMerged x _ _ sum_check, node073_total]
  simp only [blocks, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    add_zero, add_assoc]
#print axioms sum_identity
end Certificate.Assembly.H1_2
