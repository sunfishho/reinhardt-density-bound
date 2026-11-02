import Certificate.Generated.H2B009Data
import Mathlib.Tactic.FinCases
namespace Certificate.Generated.H2B009
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
theorem scalar_conditions : data.ScalarConditions := by
  unfold GramData.ScalarConditions
  decide +kernel
theorem factor_shape : ∀ i, (data.factorRow i).length = data.size := by decide +kernel
theorem symmetric_a : ∀ i j, data.A j i = data.A i j := data.symmetric_A
theorem symmetric_b : ∀ i j, data.B j i = data.B i j := data.symmetric_B
theorem row_0 : data.RowCondition (⟨0, by decide +kernel⟩ : Fin data.size) := by
  unfold GramData.RowCondition
  decide +kernel
theorem row_1 : data.RowCondition (⟨1, by decide +kernel⟩ : Fin data.size) := by
  unfold GramData.RowCondition
  decide +kernel
theorem row_2 : data.RowCondition (⟨2, by decide +kernel⟩ : Fin data.size) := by
  unfold GramData.RowCondition
  decide +kernel
theorem row_3 : data.RowCondition (⟨3, by decide +kernel⟩ : Fin data.size) := by
  unfold GramData.RowCondition
  decide +kernel
theorem all_rows : ∀ i, data.RowCondition i := by
  intro i
  fin_cases i
  · exact row_0
  · exact row_1
  · exact row_2
  · exact row_3
theorem positive_semidefinite : (realGram data.A data.B data.den).PosSemidef :=
  data.sound scalar_conditions factor_shape symmetric_a symmetric_b all_rows
#print axioms positive_semidefinite
end Certificate.Generated.H2B009
