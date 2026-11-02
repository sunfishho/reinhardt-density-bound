import Certificate.Assembly.H1_1Blocks000
import Certificate.Assembly.H1_1Blocks001
import Certificate.Assembly.H1_1Blocks002
import Certificate.Assembly.H1_1Sum
import Certificate.Identities.H1_1Proof
namespace Certificate.Assembly.H1_1
open Certificate.Sparse
set_option maxHeartbeats 0
theorem sos_nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x Certificate.Identities.H1_1.recordedSOS := by
  rw [sum_identity]
  have hp : ∀ p ∈ blocks, 0 ≤ eval x p := by
    intro p hp
    simp only [blocks,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Certificate.Assembly.H1_1B000.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_1B001.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_1B002.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_1B003.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_1B004.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_1B005.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_1B006.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_1B007.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_1B008.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_1B009.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_1B010.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_1B011.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_1B012.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_1B013.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_1B014.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_1B015.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_1B016.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_1B017.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_1B018.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_1B019.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_1B020.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_1B021.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_1B022.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_1B023.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_1B024.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_1B025.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_1B026.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_1B027.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_1B028.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_1B029.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_1B030.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_1B031.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_1B032.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_1B033.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_1B034.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_1B035.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_1B036.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_1B037.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_1B038.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_1B039.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_1B040.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_1B041.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_1B042.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_1B043.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_1B044.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_1B045.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_1B046.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_1B047.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_1B048.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_1B049.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_1B050.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_1B051.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_1B052.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_1B053.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_1B054.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_1B055.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_1B056.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_1B057.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_1B058.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_1B059.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_1B060.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_1B061.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_1B062.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_1B063.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_1B064.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_1B065.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_1B066.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_1B067.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_1B068.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_1B069.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_1B070.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_1B071.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_1B072.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_1B073.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_1B074.nonnegative x hx hregion
  exact List.sum_nonneg (fun y hy => by
    rcases List.mem_map.mp hy with ⟨p,hmem,rfl⟩
    exact hp p hmem)

/-- The cleared target inequality on the exact determinant-one region. -/
theorem target_lower_bound (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hg : x 0*x 3-x 1*x 2=1) (hh : (x 6)^2-(x 4)^2-(x 5)^2=1)
    (hregion : Certificate.PrimitiveData.Region x) :
    eval x Certificate.Identities.H1_1.gamma ≤ eval x Certificate.Identities.H1_1.target := by
  have hgg : eval x Certificate.Identities.H1_1.gg = 0 := by
    norm_num [Certificate.Identities.H1_1.gg,Certificate.Identities.H1_1.gg_0,eval,Exponent.eval]
    nlinarith only [hg]
  have hgh : eval x Certificate.Identities.H1_1.gh = 0 := by
    norm_num [Certificate.Identities.H1_1.gh,Certificate.Identities.H1_1.gh_0,eval,Exponent.eval]
    nlinarith only [hh]
  have hgt : eval x Certificate.Identities.H1_1.gt = 0 := by
    norm_num [Certificate.Identities.H1_1.gt,Certificate.Identities.H1_1.gt_0,eval,Exponent.eval,hx,Real.sq_sqrt]
  rw [Certificate.Identities.H1_1.quotient_identity,hgg,hgh,hgt]
  have hs := sos_nonnegative x hx hregion
  linarith only [hs]
#print axioms sos_nonnegative
#print axioms target_lower_bound
end Certificate.Assembly.H1_1
