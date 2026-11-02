import Certificate.Generated.H2B015Data
import Certificate.SOSPolynomial
namespace Certificate.SOS.H2B015
open Certificate.Sparse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def basisList : List Exponent := [⟨0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0⟩]
noncomputable def basis : Fin Certificate.Generated.H2B015.data.size → Exponent := fun i => basisList.getD i.val ⟨0,0,0,0,0,0,0,0⟩
noncomputable def gram_0 : Polynomial := [
  (Int.ofNat 55481492689990711246848, ⟨0, 0, 0, 0, 0, 0, 0, 0⟩),
  (Int.negSucc 712131691077959679, ⟨0, 0, 0, 0, 1, 0, 0, 0⟩),
  (Int.ofNat 11612970740138492559360, ⟨0, 0, 0, 0, 2, 0, 0, 0⟩),
  (Int.negSucc 68166817789202206294015, ⟨0, 0, 0, 0, 0, 1, 0, 0⟩),
  (Int.ofNat 472315010920480768, ⟨0, 0, 0, 0, 1, 1, 0, 0⟩),
  (Int.ofNat 22690520061052951986176, ⟨0, 0, 0, 0, 0, 2, 0, 0⟩),
  (Int.negSucc 109845189700668251701247, ⟨0, 0, 0, 0, 0, 0, 1, 0⟩),
  (Int.ofNat 710442841217695744, ⟨0, 0, 0, 0, 1, 0, 1, 0⟩),
  (Int.ofNat 68045636619278781251584, ⟨0, 0, 0, 0, 0, 1, 1, 0⟩),
  (Int.ofNat 54643552380372203339776, ⟨0, 0, 0, 0, 0, 0, 2, 0⟩)]
noncomputable def gram : Polynomial := gram_0
noncomputable def multiplier_0 : Polynomial := [
  (Int.ofNat 2307, ⟨0, 0, 0, 0, 0, 0, 0, 0⟩),
  (Int.ofNat 40000, ⟨0, 0, 0, 0, 0, 1, 0, 0⟩),
  (Int.negSucc 22306, ⟨0, 0, 0, 0, 0, 0, 1, 0⟩),
  (Int.negSucc 39999, ⟨0, 0, 0, 0, 0, 1, 1, 0⟩),
  (Int.ofNat 20000, ⟨0, 0, 0, 0, 0, 0, 2, 0⟩)]
noncomputable def multiplier : Polynomial := multiplier_0
noncomputable def weighted_0 : Polynomial := [
  (Int.ofNat 127995803635808570846478336, ⟨0, 0, 0, 0, 0, 0, 0, 0⟩),
  (Int.negSucc 1642887811316852981759, ⟨0, 0, 0, 0, 1, 0, 0, 0⟩),
  (Int.ofNat 26791123497499502334443520, ⟨0, 0, 0, 0, 2, 0, 0, 0⟩),
  (Int.ofNat 2061998858959938959953625088, ⟨0, 0, 0, 0, 0, 1, 0, 0⟩),
  (Int.negSucc 27395636912924838068223, ⟨0, 0, 0, 0, 1, 1, 0, 0⟩),
  (Int.ofNat 464518829605539702374400000, ⟨0, 0, 0, 0, 2, 1, 0, 0⟩),
  (Int.negSucc 2674325681787239091528531967, ⟨0, 0, 0, 0, 0, 2, 0, 0⟩),
  (Int.ofNat 18892600436819230720000, ⟨0, 0, 0, 0, 1, 2, 0, 0⟩),
  (Int.ofNat 907620802442118079447040000, ⟨0, 0, 0, 0, 0, 3, 0, 0⟩),
  (Int.negSucc 1491038510075064452458217471, ⟨0, 0, 0, 0, 0, 0, 1, 0⟩),
  (Int.ofNat 17524513267565270663168, ⟨0, 0, 0, 0, 1, 0, 1, 0⟩),
  (Int.negSucc 259050538300269353521643519, ⟨0, 0, 0, 0, 2, 0, 1, 0⟩),
  (Int.negSucc 4935488807521948753775820799, ⟨0, 0, 0, 0, 0, 1, 1, 0⟩),
  (Int.ofNat 46367050343223052468224, ⟨0, 0, 0, 0, 1, 1, 1, 0⟩),
  (Int.negSucc 464518829605539702374399999, ⟨0, 0, 0, 0, 2, 1, 1, 0⟩),
  (Int.ofNat 4942340745337331301868371968, ⟨0, 0, 0, 0, 0, 2, 1, 0⟩),
  (Int.negSucc 18892600436819230719999, ⟨0, 0, 0, 0, 1, 2, 1, 0⟩),
  (Int.negSucc 907620802442118079447039999, ⟨0, 0, 0, 0, 0, 3, 1, 0⟩),
  (Int.ofNat 3686009175794139588741562368, ⟨0, 0, 0, 0, 0, 0, 2, 0⟩),
  (Int.negSucc 30090482280602332561407, ⟨0, 0, 0, 0, 1, 0, 2, 0⟩),
  (Int.ofNat 232259414802769851187200000, ⟨0, 0, 0, 0, 2, 0, 2, 0⟩),
  (Int.ofNat 3698319311391322302381555712, ⟨0, 0, 0, 0, 0, 1, 2, 0⟩),
  (Int.negSucc 18971413430298214399999, ⟨0, 0, 0, 0, 1, 1, 2, 0⟩),
  (Int.negSucc 2268015063550092210339839999, ⟨0, 0, 0, 0, 0, 2, 2, 0⟩),
  (Int.negSucc 3415837516962327773925343231, ⟨0, 0, 0, 0, 0, 0, 3, 0⟩),
  (Int.ofNat 14208856824353914880000, ⟨0, 0, 0, 0, 1, 0, 3, 0⟩),
  (Int.negSucc 824829362829312508559359999, ⟨0, 0, 0, 0, 0, 1, 3, 0⟩),
  (Int.ofNat 1092871047607444066795520000, ⟨0, 0, 0, 0, 0, 0, 4, 0⟩)]
noncomputable def weighted : Polynomial := weighted_0
noncomputable def weight : ℤ := 90000
end Certificate.SOS.H2B015
