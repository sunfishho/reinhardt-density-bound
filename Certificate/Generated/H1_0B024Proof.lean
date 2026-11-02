import Certificate.Generated.H1_0B024Data
import Mathlib.Tactic.FinCases
namespace Certificate.Generated.H1_0B024
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
theorem row_9 : data.RowCondition (⟨9, by decide +kernel⟩ : Fin data.size) := by
  unfold GramData.RowCondition
  decide +kernel
theorem row_10 : data.RowCondition (⟨10, by decide +kernel⟩ : Fin data.size) := by
  unfold GramData.RowCondition
  decide +kernel
theorem row_11 : data.RowCondition (⟨11, by decide +kernel⟩ : Fin data.size) := by
  unfold GramData.RowCondition
  decide +kernel
theorem row_12 : data.RowCondition (⟨12, by decide +kernel⟩ : Fin data.size) := by
  unfold GramData.RowCondition
  decide +kernel
theorem row_13 : data.RowCondition (⟨13, by decide +kernel⟩ : Fin data.size) := by
  unfold GramData.RowCondition
  decide +kernel
theorem row_14 : data.RowCondition (⟨14, by decide +kernel⟩ : Fin data.size) := by
  unfold GramData.RowCondition
  decide +kernel
theorem row_15 : data.RowCondition (⟨15, by decide +kernel⟩ : Fin data.size) := by
  unfold GramData.RowCondition
  decide +kernel
theorem row_16 : data.RowCondition (⟨16, by decide +kernel⟩ : Fin data.size) := by
  unfold GramData.RowCondition
  decide +kernel
theorem row_17 : data.RowCondition (⟨17, by decide +kernel⟩ : Fin data.size) := by
  unfold GramData.RowCondition
  decide +kernel
theorem row_18 : data.RowCondition (⟨18, by decide +kernel⟩ : Fin data.size) := by
  unfold GramData.RowCondition
  decide +kernel
theorem row_19 : data.RowCondition (⟨19, by decide +kernel⟩ : Fin data.size) := by
  unfold GramData.RowCondition
  decide +kernel
theorem row_20 : data.RowCondition (⟨20, by decide +kernel⟩ : Fin data.size) := by
  unfold GramData.RowCondition
  decide +kernel
theorem row_21 : data.RowCondition (⟨21, by decide +kernel⟩ : Fin data.size) := by
  unfold GramData.RowCondition
  decide +kernel
theorem row_22 : data.RowCondition (⟨22, by decide +kernel⟩ : Fin data.size) := by
  unfold GramData.RowCondition
  decide +kernel
theorem row_23 : data.RowCondition (⟨23, by decide +kernel⟩ : Fin data.size) := by
  unfold GramData.RowCondition
  decide +kernel
theorem row_24 : data.RowCondition (⟨24, by decide +kernel⟩ : Fin data.size) := by
  unfold GramData.RowCondition
  decide +kernel
theorem row_25 : data.RowCondition (⟨25, by decide +kernel⟩ : Fin data.size) := by
  unfold GramData.RowCondition
  decide +kernel
theorem row_26 : data.RowCondition (⟨26, by decide +kernel⟩ : Fin data.size) := by
  unfold GramData.RowCondition
  decide +kernel
theorem row_27 : data.RowCondition (⟨27, by decide +kernel⟩ : Fin data.size) := by
  unfold GramData.RowCondition
  decide +kernel
theorem row_28 : data.RowCondition (⟨28, by decide +kernel⟩ : Fin data.size) := by
  unfold GramData.RowCondition
  decide +kernel
theorem row_29 : data.RowCondition (⟨29, by decide +kernel⟩ : Fin data.size) := by
  unfold GramData.RowCondition
  decide +kernel
theorem row_30 : data.RowCondition (⟨30, by decide +kernel⟩ : Fin data.size) := by
  unfold GramData.RowCondition
  decide +kernel
theorem row_31 : data.RowCondition (⟨31, by decide +kernel⟩ : Fin data.size) := by
  unfold GramData.RowCondition
  decide +kernel
theorem row_32 : data.RowCondition (⟨32, by decide +kernel⟩ : Fin data.size) := by
  unfold GramData.RowCondition
  decide +kernel
theorem row_33 : data.RowCondition (⟨33, by decide +kernel⟩ : Fin data.size) := by
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
  · exact row_9
  · exact row_10
  · exact row_11
  · exact row_12
  · exact row_13
  · exact row_14
  · exact row_15
  · exact row_16
  · exact row_17
  · exact row_18
  · exact row_19
  · exact row_20
  · exact row_21
  · exact row_22
  · exact row_23
  · exact row_24
  · exact row_25
  · exact row_26
  · exact row_27
  · exact row_28
  · exact row_29
  · exact row_30
  · exact row_31
  · exact row_32
  · exact row_33
theorem positive_semidefinite : (realGram data.A data.B data.den).PosSemidef :=
  data.sound scalar_conditions factor_shape symmetric_a symmetric_b all_rows
#print axioms positive_semidefinite
end Certificate.Generated.H1_0B024
