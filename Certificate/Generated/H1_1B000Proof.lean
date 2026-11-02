import Certificate.Generated.H1_1B000Data
import Mathlib.Tactic.FinCases
namespace Certificate.Generated.H1_1B000
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
theorem row_34 : data.RowCondition (⟨34, by decide +kernel⟩ : Fin data.size) := by
  unfold GramData.RowCondition
  decide +kernel
theorem row_35 : data.RowCondition (⟨35, by decide +kernel⟩ : Fin data.size) := by
  unfold GramData.RowCondition
  decide +kernel
theorem row_36 : data.RowCondition (⟨36, by decide +kernel⟩ : Fin data.size) := by
  unfold GramData.RowCondition
  decide +kernel
theorem row_37 : data.RowCondition (⟨37, by decide +kernel⟩ : Fin data.size) := by
  unfold GramData.RowCondition
  decide +kernel
theorem row_38 : data.RowCondition (⟨38, by decide +kernel⟩ : Fin data.size) := by
  unfold GramData.RowCondition
  decide +kernel
theorem row_39 : data.RowCondition (⟨39, by decide +kernel⟩ : Fin data.size) := by
  unfold GramData.RowCondition
  decide +kernel
theorem row_40 : data.RowCondition (⟨40, by decide +kernel⟩ : Fin data.size) := by
  unfold GramData.RowCondition
  decide +kernel
theorem row_41 : data.RowCondition (⟨41, by decide +kernel⟩ : Fin data.size) := by
  unfold GramData.RowCondition
  decide +kernel
theorem row_42 : data.RowCondition (⟨42, by decide +kernel⟩ : Fin data.size) := by
  unfold GramData.RowCondition
  decide +kernel
theorem row_43 : data.RowCondition (⟨43, by decide +kernel⟩ : Fin data.size) := by
  unfold GramData.RowCondition
  decide +kernel
theorem row_44 : data.RowCondition (⟨44, by decide +kernel⟩ : Fin data.size) := by
  unfold GramData.RowCondition
  decide +kernel
theorem row_45 : data.RowCondition (⟨45, by decide +kernel⟩ : Fin data.size) := by
  unfold GramData.RowCondition
  decide +kernel
theorem row_46 : data.RowCondition (⟨46, by decide +kernel⟩ : Fin data.size) := by
  unfold GramData.RowCondition
  decide +kernel
theorem row_47 : data.RowCondition (⟨47, by decide +kernel⟩ : Fin data.size) := by
  unfold GramData.RowCondition
  decide +kernel
theorem row_48 : data.RowCondition (⟨48, by decide +kernel⟩ : Fin data.size) := by
  unfold GramData.RowCondition
  decide +kernel
theorem row_49 : data.RowCondition (⟨49, by decide +kernel⟩ : Fin data.size) := by
  unfold GramData.RowCondition
  decide +kernel
theorem row_50 : data.RowCondition (⟨50, by decide +kernel⟩ : Fin data.size) := by
  unfold GramData.RowCondition
  decide +kernel
theorem row_51 : data.RowCondition (⟨51, by decide +kernel⟩ : Fin data.size) := by
  unfold GramData.RowCondition
  decide +kernel
theorem row_52 : data.RowCondition (⟨52, by decide +kernel⟩ : Fin data.size) := by
  unfold GramData.RowCondition
  decide +kernel
theorem row_53 : data.RowCondition (⟨53, by decide +kernel⟩ : Fin data.size) := by
  unfold GramData.RowCondition
  decide +kernel
theorem row_54 : data.RowCondition (⟨54, by decide +kernel⟩ : Fin data.size) := by
  unfold GramData.RowCondition
  decide +kernel
theorem row_55 : data.RowCondition (⟨55, by decide +kernel⟩ : Fin data.size) := by
  unfold GramData.RowCondition
  decide +kernel
theorem row_56 : data.RowCondition (⟨56, by decide +kernel⟩ : Fin data.size) := by
  unfold GramData.RowCondition
  decide +kernel
theorem row_57 : data.RowCondition (⟨57, by decide +kernel⟩ : Fin data.size) := by
  unfold GramData.RowCondition
  decide +kernel
theorem row_58 : data.RowCondition (⟨58, by decide +kernel⟩ : Fin data.size) := by
  unfold GramData.RowCondition
  decide +kernel
theorem row_59 : data.RowCondition (⟨59, by decide +kernel⟩ : Fin data.size) := by
  unfold GramData.RowCondition
  decide +kernel
theorem row_60 : data.RowCondition (⟨60, by decide +kernel⟩ : Fin data.size) := by
  unfold GramData.RowCondition
  decide +kernel
theorem row_61 : data.RowCondition (⟨61, by decide +kernel⟩ : Fin data.size) := by
  unfold GramData.RowCondition
  decide +kernel
theorem row_62 : data.RowCondition (⟨62, by decide +kernel⟩ : Fin data.size) := by
  unfold GramData.RowCondition
  decide +kernel
theorem row_63 : data.RowCondition (⟨63, by decide +kernel⟩ : Fin data.size) := by
  unfold GramData.RowCondition
  decide +kernel
theorem row_64 : data.RowCondition (⟨64, by decide +kernel⟩ : Fin data.size) := by
  unfold GramData.RowCondition
  decide +kernel
theorem row_65 : data.RowCondition (⟨65, by decide +kernel⟩ : Fin data.size) := by
  unfold GramData.RowCondition
  decide +kernel
theorem row_66 : data.RowCondition (⟨66, by decide +kernel⟩ : Fin data.size) := by
  unfold GramData.RowCondition
  decide +kernel
theorem row_67 : data.RowCondition (⟨67, by decide +kernel⟩ : Fin data.size) := by
  unfold GramData.RowCondition
  decide +kernel
theorem row_68 : data.RowCondition (⟨68, by decide +kernel⟩ : Fin data.size) := by
  unfold GramData.RowCondition
  decide +kernel
theorem row_69 : data.RowCondition (⟨69, by decide +kernel⟩ : Fin data.size) := by
  unfold GramData.RowCondition
  decide +kernel
theorem row_70 : data.RowCondition (⟨70, by decide +kernel⟩ : Fin data.size) := by
  unfold GramData.RowCondition
  decide +kernel
theorem row_71 : data.RowCondition (⟨71, by decide +kernel⟩ : Fin data.size) := by
  unfold GramData.RowCondition
  decide +kernel
theorem row_72 : data.RowCondition (⟨72, by decide +kernel⟩ : Fin data.size) := by
  unfold GramData.RowCondition
  decide +kernel
theorem row_73 : data.RowCondition (⟨73, by decide +kernel⟩ : Fin data.size) := by
  unfold GramData.RowCondition
  decide +kernel
theorem row_74 : data.RowCondition (⟨74, by decide +kernel⟩ : Fin data.size) := by
  unfold GramData.RowCondition
  decide +kernel
theorem row_75 : data.RowCondition (⟨75, by decide +kernel⟩ : Fin data.size) := by
  unfold GramData.RowCondition
  decide +kernel
theorem row_76 : data.RowCondition (⟨76, by decide +kernel⟩ : Fin data.size) := by
  unfold GramData.RowCondition
  decide +kernel
theorem row_77 : data.RowCondition (⟨77, by decide +kernel⟩ : Fin data.size) := by
  unfold GramData.RowCondition
  decide +kernel
theorem row_78 : data.RowCondition (⟨78, by decide +kernel⟩ : Fin data.size) := by
  unfold GramData.RowCondition
  decide +kernel
theorem row_79 : data.RowCondition (⟨79, by decide +kernel⟩ : Fin data.size) := by
  unfold GramData.RowCondition
  decide +kernel
theorem row_80 : data.RowCondition (⟨80, by decide +kernel⟩ : Fin data.size) := by
  unfold GramData.RowCondition
  decide +kernel
theorem row_81 : data.RowCondition (⟨81, by decide +kernel⟩ : Fin data.size) := by
  unfold GramData.RowCondition
  decide +kernel
theorem row_82 : data.RowCondition (⟨82, by decide +kernel⟩ : Fin data.size) := by
  unfold GramData.RowCondition
  decide +kernel
theorem row_83 : data.RowCondition (⟨83, by decide +kernel⟩ : Fin data.size) := by
  unfold GramData.RowCondition
  decide +kernel
theorem row_84 : data.RowCondition (⟨84, by decide +kernel⟩ : Fin data.size) := by
  unfold GramData.RowCondition
  decide +kernel
theorem row_85 : data.RowCondition (⟨85, by decide +kernel⟩ : Fin data.size) := by
  unfold GramData.RowCondition
  decide +kernel
theorem row_86 : data.RowCondition (⟨86, by decide +kernel⟩ : Fin data.size) := by
  unfold GramData.RowCondition
  decide +kernel
theorem row_87 : data.RowCondition (⟨87, by decide +kernel⟩ : Fin data.size) := by
  unfold GramData.RowCondition
  decide +kernel
theorem row_88 : data.RowCondition (⟨88, by decide +kernel⟩ : Fin data.size) := by
  unfold GramData.RowCondition
  decide +kernel
theorem row_89 : data.RowCondition (⟨89, by decide +kernel⟩ : Fin data.size) := by
  unfold GramData.RowCondition
  decide +kernel
theorem row_90 : data.RowCondition (⟨90, by decide +kernel⟩ : Fin data.size) := by
  unfold GramData.RowCondition
  decide +kernel
theorem row_91 : data.RowCondition (⟨91, by decide +kernel⟩ : Fin data.size) := by
  unfold GramData.RowCondition
  decide +kernel
theorem row_92 : data.RowCondition (⟨92, by decide +kernel⟩ : Fin data.size) := by
  unfold GramData.RowCondition
  decide +kernel
theorem row_93 : data.RowCondition (⟨93, by decide +kernel⟩ : Fin data.size) := by
  unfold GramData.RowCondition
  decide +kernel
theorem row_94 : data.RowCondition (⟨94, by decide +kernel⟩ : Fin data.size) := by
  unfold GramData.RowCondition
  decide +kernel
theorem row_95 : data.RowCondition (⟨95, by decide +kernel⟩ : Fin data.size) := by
  unfold GramData.RowCondition
  decide +kernel
theorem row_96 : data.RowCondition (⟨96, by decide +kernel⟩ : Fin data.size) := by
  unfold GramData.RowCondition
  decide +kernel
theorem row_97 : data.RowCondition (⟨97, by decide +kernel⟩ : Fin data.size) := by
  unfold GramData.RowCondition
  decide +kernel
theorem row_98 : data.RowCondition (⟨98, by decide +kernel⟩ : Fin data.size) := by
  unfold GramData.RowCondition
  decide +kernel
theorem row_99 : data.RowCondition (⟨99, by decide +kernel⟩ : Fin data.size) := by
  unfold GramData.RowCondition
  decide +kernel
theorem row_100 : data.RowCondition (⟨100, by decide +kernel⟩ : Fin data.size) := by
  unfold GramData.RowCondition
  decide +kernel
theorem row_101 : data.RowCondition (⟨101, by decide +kernel⟩ : Fin data.size) := by
  unfold GramData.RowCondition
  decide +kernel
theorem row_102 : data.RowCondition (⟨102, by decide +kernel⟩ : Fin data.size) := by
  unfold GramData.RowCondition
  decide +kernel
theorem row_103 : data.RowCondition (⟨103, by decide +kernel⟩ : Fin data.size) := by
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
  · exact row_34
  · exact row_35
  · exact row_36
  · exact row_37
  · exact row_38
  · exact row_39
  · exact row_40
  · exact row_41
  · exact row_42
  · exact row_43
  · exact row_44
  · exact row_45
  · exact row_46
  · exact row_47
  · exact row_48
  · exact row_49
  · exact row_50
  · exact row_51
  · exact row_52
  · exact row_53
  · exact row_54
  · exact row_55
  · exact row_56
  · exact row_57
  · exact row_58
  · exact row_59
  · exact row_60
  · exact row_61
  · exact row_62
  · exact row_63
  · exact row_64
  · exact row_65
  · exact row_66
  · exact row_67
  · exact row_68
  · exact row_69
  · exact row_70
  · exact row_71
  · exact row_72
  · exact row_73
  · exact row_74
  · exact row_75
  · exact row_76
  · exact row_77
  · exact row_78
  · exact row_79
  · exact row_80
  · exact row_81
  · exact row_82
  · exact row_83
  · exact row_84
  · exact row_85
  · exact row_86
  · exact row_87
  · exact row_88
  · exact row_89
  · exact row_90
  · exact row_91
  · exact row_92
  · exact row_93
  · exact row_94
  · exact row_95
  · exact row_96
  · exact row_97
  · exact row_98
  · exact row_99
  · exact row_100
  · exact row_101
  · exact row_102
  · exact row_103
theorem positive_semidefinite : (realGram data.A data.B data.den).PosSemidef :=
  data.sound scalar_conditions factor_shape symmetric_a symmetric_b all_rows
#print axioms positive_semidefinite
end Certificate.Generated.H1_1B000
