import Certificate.Assembly.SumTrees.H1_0.Chunk009
import Certificate.Identities.H1_0Data
import Certificate.MergeArithmetic
namespace Certificate.Assembly.H1_0
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
noncomputable def blocks : List Polynomial := [
  (scale Certificate.SOS.H1_0B000.weight Certificate.SOS.H1_0B000.weighted),
  (scale Certificate.SOS.H1_0B001.weight Certificate.SOS.H1_0B001.weighted),
  (scale Certificate.SOS.H1_0B002.weight Certificate.SOS.H1_0B002.weighted),
  (scale Certificate.SOS.H1_0B003.weight Certificate.SOS.H1_0B003.weighted),
  (scale Certificate.SOS.H1_0B004.weight Certificate.SOS.H1_0B004.weighted),
  (scale Certificate.SOS.H1_0B005.weight Certificate.SOS.H1_0B005.weighted),
  (scale Certificate.SOS.H1_0B006.weight Certificate.SOS.H1_0B006.weighted),
  (scale Certificate.SOS.H1_0B007.weight Certificate.SOS.H1_0B007.weighted),
  (scale Certificate.SOS.H1_0B008.weight Certificate.SOS.H1_0B008.weighted),
  (scale Certificate.SOS.H1_0B009.weight Certificate.SOS.H1_0B009.weighted),
  (scale Certificate.SOS.H1_0B010.weight Certificate.SOS.H1_0B010.weighted),
  (scale Certificate.SOS.H1_0B011.weight Certificate.SOS.H1_0B011.weighted),
  (scale Certificate.SOS.H1_0B012.weight Certificate.SOS.H1_0B012.weighted),
  (scale Certificate.SOS.H1_0B013.weight Certificate.SOS.H1_0B013.weighted),
  (scale Certificate.SOS.H1_0B014.weight Certificate.SOS.H1_0B014.weighted),
  (scale Certificate.SOS.H1_0B015.weight Certificate.SOS.H1_0B015.weighted),
  (scale Certificate.SOS.H1_0B016.weight Certificate.SOS.H1_0B016.weighted),
  (scale Certificate.SOS.H1_0B017.weight Certificate.SOS.H1_0B017.weighted),
  (scale Certificate.SOS.H1_0B018.weight Certificate.SOS.H1_0B018.weighted),
  (scale Certificate.SOS.H1_0B019.weight Certificate.SOS.H1_0B019.weighted),
  (scale Certificate.SOS.H1_0B020.weight Certificate.SOS.H1_0B020.weighted),
  (scale Certificate.SOS.H1_0B021.weight Certificate.SOS.H1_0B021.weighted),
  (scale Certificate.SOS.H1_0B022.weight Certificate.SOS.H1_0B022.weighted),
  (scale Certificate.SOS.H1_0B023.weight Certificate.SOS.H1_0B023.weighted),
  (scale Certificate.SOS.H1_0B024.weight Certificate.SOS.H1_0B024.weighted),
  (scale Certificate.SOS.H1_0B025.weight Certificate.SOS.H1_0B025.weighted),
  (scale Certificate.SOS.H1_0B026.weight Certificate.SOS.H1_0B026.weighted),
  (scale Certificate.SOS.H1_0B027.weight Certificate.SOS.H1_0B027.weighted),
  (scale Certificate.SOS.H1_0B028.weight Certificate.SOS.H1_0B028.weighted),
  (scale Certificate.SOS.H1_0B029.weight Certificate.SOS.H1_0B029.weighted),
  (scale Certificate.SOS.H1_0B030.weight Certificate.SOS.H1_0B030.weighted),
  (scale Certificate.SOS.H1_0B031.weight Certificate.SOS.H1_0B031.weighted),
  (scale Certificate.SOS.H1_0B032.weight Certificate.SOS.H1_0B032.weighted),
  (scale Certificate.SOS.H1_0B033.weight Certificate.SOS.H1_0B033.weighted),
  (scale Certificate.SOS.H1_0B034.weight Certificate.SOS.H1_0B034.weighted),
  (scale Certificate.SOS.H1_0B035.weight Certificate.SOS.H1_0B035.weighted),
  (scale Certificate.SOS.H1_0B036.weight Certificate.SOS.H1_0B036.weighted),
  (scale Certificate.SOS.H1_0B037.weight Certificate.SOS.H1_0B037.weighted),
  (scale Certificate.SOS.H1_0B038.weight Certificate.SOS.H1_0B038.weighted),
  (scale Certificate.SOS.H1_0B039.weight Certificate.SOS.H1_0B039.weighted),
  (scale Certificate.SOS.H1_0B040.weight Certificate.SOS.H1_0B040.weighted),
  (scale Certificate.SOS.H1_0B041.weight Certificate.SOS.H1_0B041.weighted),
  (scale Certificate.SOS.H1_0B042.weight Certificate.SOS.H1_0B042.weighted),
  (scale Certificate.SOS.H1_0B043.weight Certificate.SOS.H1_0B043.weighted),
  (scale Certificate.SOS.H1_0B044.weight Certificate.SOS.H1_0B044.weighted),
  (scale Certificate.SOS.H1_0B045.weight Certificate.SOS.H1_0B045.weighted),
  (scale Certificate.SOS.H1_0B046.weight Certificate.SOS.H1_0B046.weighted),
  (scale Certificate.SOS.H1_0B047.weight Certificate.SOS.H1_0B047.weighted),
  (scale Certificate.SOS.H1_0B048.weight Certificate.SOS.H1_0B048.weighted),
  (scale Certificate.SOS.H1_0B049.weight Certificate.SOS.H1_0B049.weighted),
  (scale Certificate.SOS.H1_0B050.weight Certificate.SOS.H1_0B050.weighted),
  (scale Certificate.SOS.H1_0B051.weight Certificate.SOS.H1_0B051.weighted),
  (scale Certificate.SOS.H1_0B052.weight Certificate.SOS.H1_0B052.weighted),
  (scale Certificate.SOS.H1_0B053.weight Certificate.SOS.H1_0B053.weighted),
  (scale Certificate.SOS.H1_0B054.weight Certificate.SOS.H1_0B054.weighted),
  (scale Certificate.SOS.H1_0B055.weight Certificate.SOS.H1_0B055.weighted),
  (scale Certificate.SOS.H1_0B056.weight Certificate.SOS.H1_0B056.weighted),
  (scale Certificate.SOS.H1_0B057.weight Certificate.SOS.H1_0B057.weighted),
  (scale Certificate.SOS.H1_0B058.weight Certificate.SOS.H1_0B058.weighted),
  (scale Certificate.SOS.H1_0B059.weight Certificate.SOS.H1_0B059.weighted),
  (scale Certificate.SOS.H1_0B060.weight Certificate.SOS.H1_0B060.weighted),
  (scale Certificate.SOS.H1_0B061.weight Certificate.SOS.H1_0B061.weighted),
  (scale Certificate.SOS.H1_0B062.weight Certificate.SOS.H1_0B062.weighted),
  (scale Certificate.SOS.H1_0B063.weight Certificate.SOS.H1_0B063.weighted),
  (scale Certificate.SOS.H1_0B064.weight Certificate.SOS.H1_0B064.weighted),
  (scale Certificate.SOS.H1_0B065.weight Certificate.SOS.H1_0B065.weighted),
  (scale Certificate.SOS.H1_0B066.weight Certificate.SOS.H1_0B066.weighted),
  (scale Certificate.SOS.H1_0B067.weight Certificate.SOS.H1_0B067.weighted),
  (scale Certificate.SOS.H1_0B068.weight Certificate.SOS.H1_0B068.weighted),
  (scale Certificate.SOS.H1_0B069.weight Certificate.SOS.H1_0B069.weighted),
  (scale Certificate.SOS.H1_0B070.weight Certificate.SOS.H1_0B070.weighted),
  (scale Certificate.SOS.H1_0B071.weight Certificate.SOS.H1_0B071.weighted),
  (scale Certificate.SOS.H1_0B072.weight Certificate.SOS.H1_0B072.weighted),
  (scale Certificate.SOS.H1_0B073.weight Certificate.SOS.H1_0B073.weighted),
  (scale Certificate.SOS.H1_0B074.weight Certificate.SOS.H1_0B074.weighted)]
theorem sum_check : checkEqualMerged node073 Certificate.Identities.H1_0.recordedSOS = true := by
  decide +kernel

theorem sum_identity (x : Fin 8 → ℝ) :
    eval x Certificate.Identities.H1_0.recordedSOS = (blocks.map (eval x)).sum := by
  rw [← eq_of_checkMerged x _ _ sum_check, node073_total]
  simp only [blocks, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    add_zero, add_assoc]
#print axioms sum_identity
end Certificate.Assembly.H1_0
