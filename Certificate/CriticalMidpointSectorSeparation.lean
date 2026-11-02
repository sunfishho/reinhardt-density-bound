import Certificate.CriticalMidpointFundamentalPartition

/-! The six open sectors of a balanced hexagon are disjoint. Coordinates in
the first two midpoint directions reduce the claim to six linear sign tests. -/
namespace Certificate.Packing
open Set Filter Topology
set_option maxHeartbeats 300000

def criticalSectorTests (i : Fin 6) (a b : ℝ) : ℝ × ℝ :=
  ![(b,a),(-a,a+b),(-a-b,b),(-b,-a),(a,-a-b),(a+b,-b)] i

theorem criticalSectorTests_disjoint {i j : Fin 6} {a b : ℝ}
    (hi : 0 < (criticalSectorTests i a b).1 ∧ 0 < (criticalSectorTests i a b).2)
    (hj : 0 < (criticalSectorTests j a b).1 ∧ 0 < (criticalSectorTests j a b).2) : i=j := by
  fin_cases i <;> fin_cases j
  all_goals first | rfl | (dsimp [criticalSectorTests] at hi hj; exfalso; linarith [hi.1,hi.2,hj.1,hj.2])

theorem criticalMidpointSector_coordinate_iff (p : criticalMidpointSet) (i : Fin 6) (a b : ℝ) :
    InCriticalMidpointSector (criticalMidpointStep p i) (a • p.val+b • (criticalMidpointNext p).val) ↔
      0 < (criticalSectorTests i a b).1 ∧ 0 < (criticalSectorTests i a b).2 := by
  rw [inCriticalMidpointSector_iff_det_pos,criticalMidpointStep_next,criticalMidpointStep_val,
    criticalMidpointStep_val]
  have he : det2 (criticalMidpointConfiguration p i) (a • p.val+b • (criticalMidpointNext p).val)=
      (criticalSectorTests i a b).1 * det2 p.val (criticalMidpointNext p).val ∧
      det2 (a • p.val+b • (criticalMidpointNext p).val) (criticalMidpointConfiguration p (i+1))=
      (criticalSectorTests i a b).2 * det2 p.val (criticalMidpointNext p).val := by
    fin_cases i <;> constructor <;>
      dsimp [criticalMidpointConfiguration,criticalSectorTests,det2] <;> ring
  rw [he.1,he.2]
  exact and_congr (mul_pos_iff_of_pos_right (criticalMidpointNext_det_pos p))
    (mul_pos_iff_of_pos_right (criticalMidpointNext_det_pos p))

theorem criticalMidpoint_sectors_disjoint (p : criticalMidpointSet) {i j : Fin 6} {x : E}
    (hi : InCriticalMidpointSector (criticalMidpointStep p i) x)
    (hj : InCriticalMidpointSector (criticalMidpointStep p j) x) : i=j := by
  let L := pairFrame p.val (criticalMidpointNext p).val (criticalMidpointNext_det_pos p).ne'
  have he : x=(L.symm x 0) • p.val+(L.symm x 1) • (criticalMidpointNext p).val :=
    (L.apply_symm_apply x).symm
  rw [he,criticalMidpointSector_coordinate_iff] at hi hj
  exact criticalSectorTests_disjoint hi hj

end Certificate.Packing
