import Certificate.Identities.H1_0Data
namespace Certificate.Identities.H1_0
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
/-- This checks the quotient/reduction stage only. The connection between
`recordedSOS` and the actual Gram blocks is a separate obligation. -/
theorem quotient_check : checkEqual target
    (merge gamma (merge recordedSOS (merge (mulFast qg gg)
      (merge (mulFast qh gh) (mulFast qt gt))))) = true := by
  decide +kernel

/-- A universal polynomial identity, with no geometric hypotheses. -/
theorem quotient_identity {R : Type*} [CommRing R] (x : Fin 8 → R) :
    eval x target = eval x gamma + eval x recordedSOS +
      eval x qg * eval x gg + eval x qh * eval x gh + eval x qt * eval x gt := by
  have h := eq_of_check x _ _ quotient_check
  simpa only [eval_merge,eval_mulFast,add_assoc] using h
#print axioms quotient_identity
end Certificate.Identities.H1_0
