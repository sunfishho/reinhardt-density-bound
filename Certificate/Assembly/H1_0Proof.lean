import Certificate.Assembly.H1_0Blocks000
import Certificate.Assembly.H1_0Blocks001
import Certificate.Assembly.H1_0Blocks002
import Certificate.Assembly.H1_0Sum
import Certificate.Identities.H1_0Proof
namespace Certificate.Assembly.H1_0
open Certificate.Sparse
set_option maxHeartbeats 0
theorem sos_nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x Certificate.Identities.H1_0.recordedSOS := by
  rw [sum_identity]
  have hp : ∀ p ∈ blocks, 0 ≤ eval x p := by
    intro p hp
    simp only [blocks,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Certificate.Assembly.H1_0B000.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_0B001.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_0B002.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_0B003.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_0B004.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_0B005.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_0B006.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_0B007.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_0B008.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_0B009.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_0B010.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_0B011.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_0B012.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_0B013.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_0B014.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_0B015.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_0B016.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_0B017.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_0B018.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_0B019.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_0B020.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_0B021.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_0B022.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_0B023.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_0B024.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_0B025.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_0B026.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_0B027.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_0B028.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_0B029.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_0B030.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_0B031.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_0B032.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_0B033.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_0B034.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_0B035.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_0B036.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_0B037.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_0B038.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_0B039.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_0B040.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_0B041.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_0B042.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_0B043.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_0B044.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_0B045.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_0B046.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_0B047.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_0B048.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_0B049.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_0B050.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_0B051.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_0B052.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_0B053.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_0B054.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_0B055.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_0B056.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_0B057.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_0B058.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_0B059.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_0B060.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_0B061.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_0B062.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_0B063.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_0B064.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_0B065.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_0B066.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_0B067.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_0B068.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_0B069.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_0B070.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_0B071.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_0B072.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_0B073.nonnegative x hx hregion
    · exact Certificate.Assembly.H1_0B074.nonnegative x hx hregion
  exact List.sum_nonneg (fun y hy => by
    rcases List.mem_map.mp hy with ⟨p,hmem,rfl⟩
    exact hp p hmem)

/-- The cleared target inequality on the exact determinant-one region. -/
theorem target_lower_bound (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hg : x 0*x 3-x 1*x 2=1) (hh : (x 6)^2-(x 4)^2-(x 5)^2=1)
    (hregion : Certificate.PrimitiveData.Region x) :
    eval x Certificate.Identities.H1_0.gamma ≤ eval x Certificate.Identities.H1_0.target := by
  have hgg : eval x Certificate.Identities.H1_0.gg = 0 := by
    norm_num [Certificate.Identities.H1_0.gg,Certificate.Identities.H1_0.gg_0,eval,Exponent.eval]
    nlinarith only [hg]
  have hgh : eval x Certificate.Identities.H1_0.gh = 0 := by
    norm_num [Certificate.Identities.H1_0.gh,Certificate.Identities.H1_0.gh_0,eval,Exponent.eval]
    nlinarith only [hh]
  have hgt : eval x Certificate.Identities.H1_0.gt = 0 := by
    norm_num [Certificate.Identities.H1_0.gt,Certificate.Identities.H1_0.gt_0,eval,Exponent.eval,hx,Real.sq_sqrt]
  rw [Certificate.Identities.H1_0.quotient_identity,hgg,hgh,hgt]
  have hs := sos_nonnegative x hx hregion
  linarith only [hs]
#print axioms sos_nonnegative
#print axioms target_lower_bound
end Certificate.Assembly.H1_0
