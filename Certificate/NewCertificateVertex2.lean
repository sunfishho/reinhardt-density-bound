import Certificate.NewCertificateDefinitions
import Certificate.Assembly.H1_2Proof
import Certificate.Potential.H1_2
namespace Certificate.NewCertificate
open Certificate.Sparse Certificate.Potential
set_option maxHeartbeats 0
theorem differential_2 (x : State) (hx : OnRegion x) :
    0 ≤ denominatorAt x (vertex 2)*(x.cost-dG x)-dX x 2 := by
  have h := Assembly.H1_2.target_lower_bound x.coordinates (by rfl)
    hx.1.1 hx.1.2 hx.2
  have hz : eval x.coordinates Identities.H1_2.gamma = 0 := by
    norm_num [Identities.H1_2.gamma,eval]
  rw [hz,Potential.H1_2.semantic_identity] at h
  have hs : (0 : ℝ) < Potential.H1_2.scaleFactor := by
    exact_mod_cast Potential.H1_2.scale_positive
  have ht := (mul_nonneg_iff_of_pos_left hs).mp h
  have hselect : clearedTarget (2 : Fin 3) = clearedTarget_2 := by
    simp only [clearedTarget,Matrix.cons_val]
  have ht' : 0 ≤ eval x.coordinates (clearedTarget 2) :=
    (congrArg (fun p : Polynomial => (0 : ℝ) ≤ eval x.coordinates p) hselect).mpr ht
  rw [clearedTarget_evaluation] at ht'
  have hd : (0 : ℝ) < 3*(Potential.denominator : ℝ) := by
    have hp : (0 : ℝ) < Potential.denominator := by exact_mod_cast denominator_pos
    exact mul_pos (by norm_num) hp
  exact (mul_nonneg_iff_of_pos_left hd).mp ht'

#print axioms differential_2
end Certificate.NewCertificate
