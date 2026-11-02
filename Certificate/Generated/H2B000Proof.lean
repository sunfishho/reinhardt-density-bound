import Certificate.Generated.H2B000Data
import Mathlib.Tactic.FinCases
namespace Certificate.Generated.H2B000
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
theorem row_4 : data.RowCondition (⟨4, by decide +kernel⟩ : Fin data.size) := by
  unfold GramData.RowCondition
  decide +kernel
theorem row_5 : data.RowCondition (⟨5, by decide +kernel⟩ : Fin data.size) := by
  unfold GramData.RowCondition
  decide +kernel
theorem row_6 : data.RowCondition (⟨6, by decide +kernel⟩ : Fin data.size) := by
  unfold GramData.RowCondition
  decide +kernel
theorem row_7 : data.RowCondition (⟨7, by decide +kernel⟩ : Fin data.size) := by
  unfold GramData.RowCondition
  decide +kernel
theorem row_8 : data.RowCondition (⟨8, by decide +kernel⟩ : Fin data.size) := by
  unfold GramData.RowCondition
  decide +kernel
theorem all_rows : ∀ i, data.RowCondition i := by
  intro i
  fin_cases i
  · exact row_0
  · exact row_1
  · exact row_2
  · exact row_3
  · exact row_4
  · exact row_5
  · exact row_6
  · exact row_7
  · exact row_8
theorem positive_semidefinite : (realGram data.A data.B data.den).PosSemidef :=
  data.sound scalar_conditions factor_shape symmetric_a symmetric_b all_rows
#print axioms positive_semidefinite
end Certificate.Generated.H2B000
