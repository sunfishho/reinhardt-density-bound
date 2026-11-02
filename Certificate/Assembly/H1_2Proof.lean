import Certificate.Assembly.H1_2Blocks000
import Certificate.Assembly.H1_2Blocks001
import Certificate.Assembly.H1_2Blocks002
import Certificate.Assembly.H1_2Sum
import Certificate.Identities.H1_2Proof
namespace Certificate.Assembly.H1_2
open Certificate.Sparse
set_option maxHeartbeats 0
theorem sos_nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x Certificate.Identities.H1_2.recordedSOS := by
  rw [sum_identity]
  have hp : ∀ p ∈ blocks, 0 ≤ eval x p := by
    intro p hp
    simp only [blocks,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Certificate.Assembly.H1_2B000.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_2B001.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_2B002.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_2B003.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_2B004.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_2B005.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_2B006.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_2B007.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_2B008.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_2B009.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_2B010.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_2B011.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_2B012.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_2B013.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_2B014.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_2B015.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_2B016.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_2B017.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_2B018.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_2B019.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_2B020.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_2B021.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_2B022.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_2B023.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_2B024.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_2B025.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_2B026.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_2B027.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_2B028.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_2B029.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_2B030.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_2B031.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_2B032.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_2B033.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_2B034.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_2B035.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_2B036.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_2B037.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_2B038.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_2B039.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_2B040.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_2B041.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_2B042.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_2B043.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_2B044.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_2B045.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_2B046.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_2B047.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_2B048.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_2B049.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_2B050.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_2B051.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_2B052.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_2B053.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_2B054.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_2B055.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_2B056.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_2B057.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_2B058.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_2B059.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_2B060.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_2B061.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_2B062.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_2B063.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_2B064.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_2B065.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_2B066.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_2B067.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_2B068.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_2B069.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_2B070.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_2B071.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_2B072.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_2B073.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_2B074.nonnegative x hx hregion
  exact List.sum_nonneg (fun y hy => by
    rcases List.mem_map.mp hy with ⟨p,hmem,rfl⟩
    exact hp p hmem)

/-- The cleared target inequality on the exact determinant-one region. -/
theorem target_lower_bound (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hg : x 0*x 3-x 1*x 2=1) (hh : (x 6)^2-(x 4)^2-(x 5)^2=1)
    (hregion : Certificate.PrimitiveData.Region x) :
    eval x Certificate.Identities.H1_2.gamma ≤ eval x Certificate.Identities.H1_2.target := by
  have hgg : eval x Certificate.Identities.H1_2.gg = 0 := by
    norm_num [Certificate.Identities.H1_2.gg,Certificate.Identities.H1_2.gg_0,eval,Exponent.eval]
    nlinarith only [hg]
  have hgh : eval x Certificate.Identities.H1_2.gh = 0 := by
    norm_num [Certificate.Identities.H1_2.gh,Certificate.Identities.H1_2.gh_0,eval,Exponent.eval]
    nlinarith only [hh]
  have hgt : eval x Certificate.Identities.H1_2.gt = 0 := by
    norm_num [Certificate.Identities.H1_2.gt,Certificate.Identities.H1_2.gt_0,eval,Exponent.eval,hx,Real.sq_sqrt]
  rw [Certificate.Identities.H1_2.quotient_identity,hgg,hgh,hgt]
  have hs := sos_nonnegative x hx hregion
  linarith only [hs]
#print axioms sos_nonnegative
#print axioms target_lower_bound
end Certificate.Assembly.H1_2
