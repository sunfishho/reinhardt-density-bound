import Certificate.Assembly.H2B000
import Certificate.Assembly.H2B001
import Certificate.Assembly.H2B002
import Certificate.Assembly.H2B003
import Certificate.Assembly.H2B004
import Certificate.Assembly.H2B005
import Certificate.Assembly.H2B006
import Certificate.Assembly.H2B007
import Certificate.Assembly.H2B008
import Certificate.Assembly.H2B009
import Certificate.Assembly.H2B010
import Certificate.Assembly.H2B011
import Certificate.Assembly.H2B012
import Certificate.Assembly.H2B013
import Certificate.Assembly.H2B014
import Certificate.Assembly.H2B015
import Certificate.Assembly.H2B016
import Certificate.Assembly.H2B017
import Certificate.Assembly.H2B018
import Certificate.Assembly.H2B019
import Certificate.Assembly.H2B020
import Certificate.Assembly.H2B021
import Certificate.Assembly.H2B022
import Certificate.Assembly.H2Sum
import Certificate.Identities.H2Proof
namespace Certificate.Assembly.H2
open Certificate.Sparse
set_option maxHeartbeats 0
theorem sos_nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hregion : Certificate.PrimitiveData.Region x) :
    0 ≤ eval x Certificate.Identities.H2.recordedSOS := by
  rw [sum_identity]
  have hp : ∀ p ∈ blocks, 0 ≤ eval x p := by
    intro p hp
    simp only [blocks,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Certificate.Assembly.H2B000.nonnegative x hx hregion
    · exact Certificate.Assembly.H2B001.nonnegative x hx hregion
    · exact Certificate.Assembly.H2B002.nonnegative x hx hregion
    · exact Certificate.Assembly.H2B003.nonnegative x hx hregion
    · exact Certificate.Assembly.H2B004.nonnegative x hx hregion
    · exact Certificate.Assembly.H2B005.nonnegative x hx hregion
    · exact Certificate.Assembly.H2B006.nonnegative x hx hregion
    · exact Certificate.Assembly.H2B007.nonnegative x hx hregion
    · exact Certificate.Assembly.H2B008.nonnegative x hx hregion
    · exact Certificate.Assembly.H2B009.nonnegative x hx hregion
    · exact Certificate.Assembly.H2B010.nonnegative x hx hregion
    · exact Certificate.Assembly.H2B011.nonnegative x hx hregion
    · exact Certificate.Assembly.H2B012.nonnegative x hx hregion
    · exact Certificate.Assembly.H2B013.nonnegative x hx hregion
    · exact Certificate.Assembly.H2B014.nonnegative x hx hregion
    · exact Certificate.Assembly.H2B015.nonnegative x hx hregion
    · exact Certificate.Assembly.H2B016.nonnegative x hx hregion
    · exact Certificate.Assembly.H2B017.nonnegative x hx hregion
    · exact Certificate.Assembly.H2B018.nonnegative x hx hregion
    · exact Certificate.Assembly.H2B019.nonnegative x hx hregion
    · exact Certificate.Assembly.H2B020.nonnegative x hx hregion
    · exact Certificate.Assembly.H2B021.nonnegative x hx hregion
    · exact Certificate.Assembly.H2B022.nonnegative x hx hregion
  exact List.sum_nonneg (fun y hy => by
    rcases List.mem_map.mp hy with ⟨p,hmem,rfl⟩
    exact hp p hmem)

/-- The cleared target inequality on the exact determinant-one region. -/
theorem target_lower_bound (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)
    (hg : x 0*x 3-x 1*x 2=1) (hh : (x 6)^2-(x 4)^2-(x 5)^2=1)
    (hregion : Certificate.PrimitiveData.Region x) :
    eval x Certificate.Identities.H2.gamma ≤ eval x Certificate.Identities.H2.target := by
  have hgg : eval x Certificate.Identities.H2.gg = 0 := by
    norm_num [Certificate.Identities.H2.gg,Certificate.Identities.H2.gg_0,eval,Exponent.eval]
    nlinarith only [hg]
  have hgh : eval x Certificate.Identities.H2.gh = 0 := by
    norm_num [Certificate.Identities.H2.gh,Certificate.Identities.H2.gh_0,eval,Exponent.eval]
    nlinarith only [hh]
  have hgt : eval x Certificate.Identities.H2.gt = 0 := by
    norm_num [Certificate.Identities.H2.gt,Certificate.Identities.H2.gt_0,eval,Exponent.eval,hx,Real.sq_sqrt]
  rw [Certificate.Identities.H2.quotient_identity,hgg,hgh,hgt]
  have hs := sos_nonnegative x hx hregion
  linarith only [hs]
#print axioms sos_nonnegative
#print axioms target_lower_bound
end Certificate.Assembly.H2
