import Certificate.AreaAssemblyHelpers

/-! The six exterior corner sectors of the regular inscribed hexagon.
Their intersections, and their intersections with the inscribed hexagon,
have zero area. These are geometric conclusions, not assumed disjointness. -/
namespace Certificate.Packing.HVGeometry
open MeasureTheory Set Pointwise
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false

noncomputable def rayA : E →ₗ[ℝ] ℝ := coord 1
noncomputable def rayB : E →ₗ[ℝ] ℝ := Real.sqrt 3 • coord 0 - coord 1
noncomputable def rayC : E →ₗ[ℝ] ℝ := Real.sqrt 3 • coord 0 + coord 1
noncomputable def leftNormal : Fin 6 → (E →ₗ[ℝ] ℝ) :=
  ![rayA,-rayB,rayA,-rayA,rayB,-rayA]
noncomputable def rightNormal : Fin 6 → (E →ₗ[ℝ] ℝ) :=
  ![rayB,rayC,-rayC,-rayB,-rayC,rayC]
noncomputable def baseNormal : Fin 6 → (E →ₗ[ℝ] ℝ) :=
  ![rayC,rayA,-rayB,-rayC,-rayA,rayB]
noncomputable def baseLevel : Fin 6 → ℝ :=
  ![Real.sqrt 3,Real.sqrt 3/2,Real.sqrt 3,Real.sqrt 3,Real.sqrt 3/2,Real.sqrt 3]
noncomputable def cornerRegion (i : Fin 6) : Set E :=
  {x | 0 ≤ leftNormal i x ∧ 0 ≤ rightNormal i x ∧ baseLevel i ≤ baseNormal i x}

lemma convex_cornerRegion (i : Fin 6) : Convex ℝ (cornerRegion i) :=
  (convex_superlevel (leftNormal i) 0).inter
    ((convex_superlevel (rightNormal i) 0).inter
      (convex_superlevel (baseNormal i) (baseLevel i)))

lemma rayA_ne_zero : rayA ≠ 0 := by
  intro h
  have hh := congrArg (fun f : E →ₗ[ℝ] ℝ => f (pt 0 1)) h
  norm_num [rayA,pt] at hh
lemma rayB_ne_zero : rayB ≠ 0 := by
  intro h
  have hh := congrArg (fun f : E →ₗ[ℝ] ℝ => f (pt 1 0)) h
  have hs := Real.sqrt_pos.2 (by norm_num : (0:ℝ)<3)
  norm_num [rayB,pt] at hh
lemma rayC_ne_zero : rayC ≠ 0 := by
  intro h
  have hh := congrArg (fun f : E →ₗ[ℝ] ℝ => f (pt 1 0)) h
  have hs := Real.sqrt_pos.2 (by norm_num : (0:ℝ)<3)
  norm_num [rayC,pt] at hh

lemma cornerRegion_inter_null :
    Pairwise (fun i j => AEDisjoint volume (cornerRegion i) (cornerRegion j)) := by
  have h01 : volume (cornerRegion 0 ∩ cornerRegion 1) = 0 := by
    apply measure_inter_zero_of_separation (rayB) rayB_ne_zero 0
    · intro x hx
      dsimp [cornerRegion,leftNormal,rightNormal,baseNormal,baseLevel] at hx
      simp only [rayA,rayB,rayC,
        LinearMap.neg_apply,LinearMap.add_apply,LinearMap.sub_apply,
        LinearMap.smul_apply,smul_eq_mul,coord_eval,Set.mem_ofPred_eq] at hx ⊢
      linarith [hx.1,hx.2.1]
    · intro x hx
      dsimp [cornerRegion,leftNormal,rightNormal,baseNormal,baseLevel] at hx
      simp only [rayA,rayB,rayC,
        LinearMap.neg_apply,LinearMap.add_apply,LinearMap.sub_apply,
        LinearMap.smul_apply,smul_eq_mul,coord_eval,Set.mem_ofPred_eq] at hx ⊢
      linarith [hx.1,hx.2.1]
  have h02 : volume (cornerRegion 0 ∩ cornerRegion 2) = 0 := by
    apply measure_inter_zero_of_separation (rayB) rayB_ne_zero 0
    · intro x hx
      dsimp [cornerRegion,leftNormal,rightNormal,baseNormal,baseLevel] at hx
      simp only [rayA,rayB,rayC,
        LinearMap.neg_apply,LinearMap.add_apply,LinearMap.sub_apply,
        LinearMap.smul_apply,smul_eq_mul,coord_eval,Set.mem_ofPred_eq] at hx ⊢
      linarith [hx.1,hx.2.1]
    · intro x hx
      dsimp [cornerRegion,leftNormal,rightNormal,baseNormal,baseLevel] at hx
      simp only [rayA,rayB,rayC,
        LinearMap.neg_apply,LinearMap.add_apply,LinearMap.sub_apply,
        LinearMap.smul_apply,smul_eq_mul,coord_eval,Set.mem_ofPred_eq] at hx ⊢
      linarith [hx.1,hx.2.1]
  have h03 : volume (cornerRegion 0 ∩ cornerRegion 3) = 0 := by
    apply measure_inter_zero_of_separation (rayA) rayA_ne_zero 0
    · intro x hx
      dsimp [cornerRegion,leftNormal,rightNormal,baseNormal,baseLevel] at hx
      simp only [rayA,rayB,rayC,
        LinearMap.neg_apply,LinearMap.add_apply,LinearMap.sub_apply,
        LinearMap.smul_apply,smul_eq_mul,coord_eval,Set.mem_ofPred_eq] at hx ⊢
      linarith [hx.1,hx.2.1]
    · intro x hx
      dsimp [cornerRegion,leftNormal,rightNormal,baseNormal,baseLevel] at hx
      simp only [rayA,rayB,rayC,
        LinearMap.neg_apply,LinearMap.add_apply,LinearMap.sub_apply,
        LinearMap.smul_apply,smul_eq_mul,coord_eval,Set.mem_ofPred_eq] at hx ⊢
      linarith [hx.1,hx.2.1]
  have h04 : volume (cornerRegion 0 ∩ cornerRegion 4) = 0 := by
    apply measure_inter_zero_of_separation (rayA) rayA_ne_zero 0
    · intro x hx
      dsimp [cornerRegion,leftNormal,rightNormal,baseNormal,baseLevel] at hx
      simp only [rayA,rayB,rayC,
        LinearMap.neg_apply,LinearMap.add_apply,LinearMap.sub_apply,
        LinearMap.smul_apply,smul_eq_mul,coord_eval,Set.mem_ofPred_eq] at hx ⊢
      linarith [hx.1,hx.2.1]
    · intro x hx
      dsimp [cornerRegion,leftNormal,rightNormal,baseNormal,baseLevel] at hx
      simp only [rayA,rayB,rayC,
        LinearMap.neg_apply,LinearMap.add_apply,LinearMap.sub_apply,
        LinearMap.smul_apply,smul_eq_mul,coord_eval,Set.mem_ofPred_eq] at hx ⊢
      linarith [hx.1,hx.2.1]
  have h05 : volume (cornerRegion 0 ∩ cornerRegion 5) = 0 := by
    apply measure_inter_zero_of_separation (rayA) rayA_ne_zero 0
    · intro x hx
      dsimp [cornerRegion,leftNormal,rightNormal,baseNormal,baseLevel] at hx
      simp only [rayA,rayB,rayC,
        LinearMap.neg_apply,LinearMap.add_apply,LinearMap.sub_apply,
        LinearMap.smul_apply,smul_eq_mul,coord_eval,Set.mem_ofPred_eq] at hx ⊢
      linarith [hx.1,hx.2.1]
    · intro x hx
      dsimp [cornerRegion,leftNormal,rightNormal,baseNormal,baseLevel] at hx
      simp only [rayA,rayB,rayC,
        LinearMap.neg_apply,LinearMap.add_apply,LinearMap.sub_apply,
        LinearMap.smul_apply,smul_eq_mul,coord_eval,Set.mem_ofPred_eq] at hx ⊢
      linarith [hx.1,hx.2.1]
  have h12 : volume (cornerRegion 1 ∩ cornerRegion 2) = 0 := by
    apply measure_inter_zero_of_separation (rayC) rayC_ne_zero 0
    · intro x hx
      dsimp [cornerRegion,leftNormal,rightNormal,baseNormal,baseLevel] at hx
      simp only [rayA,rayB,rayC,
        LinearMap.neg_apply,LinearMap.add_apply,LinearMap.sub_apply,
        LinearMap.smul_apply,smul_eq_mul,coord_eval,Set.mem_ofPred_eq] at hx ⊢
      linarith [hx.1,hx.2.1]
    · intro x hx
      dsimp [cornerRegion,leftNormal,rightNormal,baseNormal,baseLevel] at hx
      simp only [rayA,rayB,rayC,
        LinearMap.neg_apply,LinearMap.add_apply,LinearMap.sub_apply,
        LinearMap.smul_apply,smul_eq_mul,coord_eval,Set.mem_ofPred_eq] at hx ⊢
      linarith [hx.1,hx.2.1]
  have h13 : volume (cornerRegion 1 ∩ cornerRegion 3) = 0 := by
    apply measure_inter_zero_of_separation (rayC) rayC_ne_zero 0
    · intro x hx
      dsimp [cornerRegion,leftNormal,rightNormal,baseNormal,baseLevel] at hx
      simp only [rayA,rayB,rayC,
        LinearMap.neg_apply,LinearMap.add_apply,LinearMap.sub_apply,
        LinearMap.smul_apply,smul_eq_mul,coord_eval,Set.mem_ofPred_eq] at hx ⊢
      linarith [hx.1,hx.2.1]
    · intro x hx
      dsimp [cornerRegion,leftNormal,rightNormal,baseNormal,baseLevel] at hx
      simp only [rayA,rayB,rayC,
        LinearMap.neg_apply,LinearMap.add_apply,LinearMap.sub_apply,
        LinearMap.smul_apply,smul_eq_mul,coord_eval,Set.mem_ofPred_eq] at hx ⊢
      linarith [hx.1,hx.2.1]
  have h14 : volume (cornerRegion 1 ∩ cornerRegion 4) = 0 := by
    apply measure_inter_zero_of_separation (rayC) rayC_ne_zero 0
    · intro x hx
      dsimp [cornerRegion,leftNormal,rightNormal,baseNormal,baseLevel] at hx
      simp only [rayA,rayB,rayC,
        LinearMap.neg_apply,LinearMap.add_apply,LinearMap.sub_apply,
        LinearMap.smul_apply,smul_eq_mul,coord_eval,Set.mem_ofPred_eq] at hx ⊢
      linarith [hx.1,hx.2.1]
    · intro x hx
      dsimp [cornerRegion,leftNormal,rightNormal,baseNormal,baseLevel] at hx
      simp only [rayA,rayB,rayC,
        LinearMap.neg_apply,LinearMap.add_apply,LinearMap.sub_apply,
        LinearMap.smul_apply,smul_eq_mul,coord_eval,Set.mem_ofPred_eq] at hx ⊢
      linarith [hx.1,hx.2.1]
  have h15 : volume (cornerRegion 1 ∩ cornerRegion 5) = 0 := by
    apply measure_inter_zero_of_separation (-rayB) (neg_ne_zero.mpr rayB_ne_zero) 0
    · intro x hx
      dsimp [cornerRegion,leftNormal,rightNormal,baseNormal,baseLevel] at hx
      simp only [rayA,rayB,rayC,
        LinearMap.neg_apply,LinearMap.add_apply,LinearMap.sub_apply,
        LinearMap.smul_apply,smul_eq_mul,coord_eval,Set.mem_ofPred_eq] at hx ⊢
      linarith [hx.1,hx.2.1]
    · intro x hx
      dsimp [cornerRegion,leftNormal,rightNormal,baseNormal,baseLevel] at hx
      simp only [rayA,rayB,rayC,
        LinearMap.neg_apply,LinearMap.add_apply,LinearMap.sub_apply,
        LinearMap.smul_apply,smul_eq_mul,coord_eval,Set.mem_ofPred_eq] at hx ⊢
      linarith [hx.1,hx.2.1]
  have h23 : volume (cornerRegion 2 ∩ cornerRegion 3) = 0 := by
    apply measure_inter_zero_of_separation (rayA) rayA_ne_zero 0
    · intro x hx
      dsimp [cornerRegion,leftNormal,rightNormal,baseNormal,baseLevel] at hx
      simp only [rayA,rayB,rayC,
        LinearMap.neg_apply,LinearMap.add_apply,LinearMap.sub_apply,
        LinearMap.smul_apply,smul_eq_mul,coord_eval,Set.mem_ofPred_eq] at hx ⊢
      linarith [hx.1,hx.2.1]
    · intro x hx
      dsimp [cornerRegion,leftNormal,rightNormal,baseNormal,baseLevel] at hx
      simp only [rayA,rayB,rayC,
        LinearMap.neg_apply,LinearMap.add_apply,LinearMap.sub_apply,
        LinearMap.smul_apply,smul_eq_mul,coord_eval,Set.mem_ofPred_eq] at hx ⊢
      linarith [hx.1,hx.2.1]
  have h24 : volume (cornerRegion 2 ∩ cornerRegion 4) = 0 := by
    apply measure_inter_zero_of_separation (rayA) rayA_ne_zero 0
    · intro x hx
      dsimp [cornerRegion,leftNormal,rightNormal,baseNormal,baseLevel] at hx
      simp only [rayA,rayB,rayC,
        LinearMap.neg_apply,LinearMap.add_apply,LinearMap.sub_apply,
        LinearMap.smul_apply,smul_eq_mul,coord_eval,Set.mem_ofPred_eq] at hx ⊢
      linarith [hx.1,hx.2.1]
    · intro x hx
      dsimp [cornerRegion,leftNormal,rightNormal,baseNormal,baseLevel] at hx
      simp only [rayA,rayB,rayC,
        LinearMap.neg_apply,LinearMap.add_apply,LinearMap.sub_apply,
        LinearMap.smul_apply,smul_eq_mul,coord_eval,Set.mem_ofPred_eq] at hx ⊢
      linarith [hx.1,hx.2.1]
  have h25 : volume (cornerRegion 2 ∩ cornerRegion 5) = 0 := by
    apply measure_inter_zero_of_separation (rayA) rayA_ne_zero 0
    · intro x hx
      dsimp [cornerRegion,leftNormal,rightNormal,baseNormal,baseLevel] at hx
      simp only [rayA,rayB,rayC,
        LinearMap.neg_apply,LinearMap.add_apply,LinearMap.sub_apply,
        LinearMap.smul_apply,smul_eq_mul,coord_eval,Set.mem_ofPred_eq] at hx ⊢
      linarith [hx.1,hx.2.1]
    · intro x hx
      dsimp [cornerRegion,leftNormal,rightNormal,baseNormal,baseLevel] at hx
      simp only [rayA,rayB,rayC,
        LinearMap.neg_apply,LinearMap.add_apply,LinearMap.sub_apply,
        LinearMap.smul_apply,smul_eq_mul,coord_eval,Set.mem_ofPred_eq] at hx ⊢
      linarith [hx.1,hx.2.1]
  have h34 : volume (cornerRegion 3 ∩ cornerRegion 4) = 0 := by
    apply measure_inter_zero_of_separation (-rayB) (neg_ne_zero.mpr rayB_ne_zero) 0
    · intro x hx
      dsimp [cornerRegion,leftNormal,rightNormal,baseNormal,baseLevel] at hx
      simp only [rayA,rayB,rayC,
        LinearMap.neg_apply,LinearMap.add_apply,LinearMap.sub_apply,
        LinearMap.smul_apply,smul_eq_mul,coord_eval,Set.mem_ofPred_eq] at hx ⊢
      linarith [hx.1,hx.2.1]
    · intro x hx
      dsimp [cornerRegion,leftNormal,rightNormal,baseNormal,baseLevel] at hx
      simp only [rayA,rayB,rayC,
        LinearMap.neg_apply,LinearMap.add_apply,LinearMap.sub_apply,
        LinearMap.smul_apply,smul_eq_mul,coord_eval,Set.mem_ofPred_eq] at hx ⊢
      linarith [hx.1,hx.2.1]
  have h35 : volume (cornerRegion 3 ∩ cornerRegion 5) = 0 := by
    apply measure_inter_zero_of_separation (-rayB) (neg_ne_zero.mpr rayB_ne_zero) 0
    · intro x hx
      dsimp [cornerRegion,leftNormal,rightNormal,baseNormal,baseLevel] at hx
      simp only [rayA,rayB,rayC,
        LinearMap.neg_apply,LinearMap.add_apply,LinearMap.sub_apply,
        LinearMap.smul_apply,smul_eq_mul,coord_eval,Set.mem_ofPred_eq] at hx ⊢
      linarith [hx.1,hx.2.1]
    · intro x hx
      dsimp [cornerRegion,leftNormal,rightNormal,baseNormal,baseLevel] at hx
      simp only [rayA,rayB,rayC,
        LinearMap.neg_apply,LinearMap.add_apply,LinearMap.sub_apply,
        LinearMap.smul_apply,smul_eq_mul,coord_eval,Set.mem_ofPred_eq] at hx ⊢
      linarith [hx.1,hx.2.1]
  have h45 : volume (cornerRegion 4 ∩ cornerRegion 5) = 0 := by
    apply measure_inter_zero_of_separation (-rayC) (neg_ne_zero.mpr rayC_ne_zero) 0
    · intro x hx
      dsimp [cornerRegion,leftNormal,rightNormal,baseNormal,baseLevel] at hx
      simp only [rayA,rayB,rayC,
        LinearMap.neg_apply,LinearMap.add_apply,LinearMap.sub_apply,
        LinearMap.smul_apply,smul_eq_mul,coord_eval,Set.mem_ofPred_eq] at hx ⊢
      linarith [hx.1,hx.2.1]
    · intro x hx
      dsimp [cornerRegion,leftNormal,rightNormal,baseNormal,baseLevel] at hx
      simp only [rayA,rayB,rayC,
        LinearMap.neg_apply,LinearMap.add_apply,LinearMap.sub_apply,
        LinearMap.smul_apply,smul_eq_mul,coord_eval,Set.mem_ofPred_eq] at hx ⊢
      linarith [hx.1,hx.2.1]
  intro i j hij
  change volume (cornerRegion i ∩ cornerRegion j) = 0
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · exact h01
  · exact h02
  · exact h03
  · exact h04
  · exact h05
  · rw [Set.inter_comm]; exact h01
  · exact (hij rfl).elim
  · exact h12
  · exact h13
  · exact h14
  · exact h15
  · rw [Set.inter_comm]; exact h02
  · rw [Set.inter_comm]; exact h12
  · exact (hij rfl).elim
  · exact h23
  · exact h24
  · exact h25
  · rw [Set.inter_comm]; exact h03
  · rw [Set.inter_comm]; exact h13
  · rw [Set.inter_comm]; exact h23
  · exact (hij rfl).elim
  · exact h34
  · exact h35
  · rw [Set.inter_comm]; exact h04
  · rw [Set.inter_comm]; exact h14
  · rw [Set.inter_comm]; exact h24
  · rw [Set.inter_comm]; exact h34
  · exact (hij rfl).elim
  · exact h45
  · rw [Set.inter_comm]; exact h05
  · rw [Set.inter_comm]; exact h15
  · rw [Set.inter_comm]; exact h25
  · rw [Set.inter_comm]; exact h35
  · rw [Set.inter_comm]; exact h45
  · exact (hij rfl).elim

lemma baseNormal_ne_zero (i : Fin 6) : baseNormal i ≠ 0 := by
  fin_cases i
  · exact rayC_ne_zero
  · exact rayA_ne_zero
  · exact neg_ne_zero.mpr rayB_ne_zero
  · exact neg_ne_zero.mpr rayC_ne_zero
  · exact neg_ne_zero.mpr rayA_ne_zero
  · exact rayB_ne_zero

lemma root_base_bound (i j : Fin 6) : baseNormal i (root j) ≤ baseLevel i := by
  have hs := Real.sqrt_nonneg (3:ℝ)
  fin_cases i <;> fin_cases j <;>
    simp only [baseNormal,baseLevel,root,Matrix.cons_val_zero,Matrix.cons_val_succ,
      rayA,rayB,rayC,LinearMap.neg_apply,LinearMap.add_apply,LinearMap.sub_apply,
      LinearMap.smul_apply,smul_eq_mul,coord_eval] <;>
    dsimp [s0,s1,s2,pt] <;> norm_num <;> linarith

lemma inscribedHexagon_base_bound (i : Fin 6) :
    ∀ x ∈ inscribedHexagon, baseNormal i x ≤ baseLevel i := by
  intro x hx
  obtain ⟨j,hj⟩ := mem_iUnion.1 hx
  have hzero : baseNormal i (0:E) ≤ baseLevel i := by
    rw [map_zero]
    fin_cases i <;> dsimp [baseLevel] <;> positivity
  have h := triangle_sublevel (baseNormal i) (baseLevel i) hzero
    (root_base_bound i j) (root_base_bound i (next j))
  apply h x
  simpa only [triangle,zero_vadd,sub_zero,wedge] using hj

lemma inscribedHexagon_cornerRegion_inter_null (i : Fin 6) :
    volume (cornerRegion i ∩ inscribedHexagon) = 0 := by
  apply measure_inter_zero_of_separation (baseNormal i) (baseNormal_ne_zero i) (baseLevel i)
  · intro x hx; exact hx.2.2
  · exact inscribedHexagon_base_bound i

lemma roots_mem_cornerRegion (i : Fin 6) :
    root i ∈ cornerRegion i ∧ root (next i) ∈ cornerRegion i := by
  have hs := Real.sqrt_nonneg (3:ℝ)
  fin_cases i <;>
    simp only [cornerRegion,leftNormal,rightNormal,baseNormal,baseLevel,root,next,
      Matrix.cons_val_zero,Matrix.cons_val_succ,
      rayA,rayB,rayC,LinearMap.neg_apply,LinearMap.add_apply,LinearMap.sub_apply,
      LinearMap.smul_apply,smul_eq_mul,coord_eval,Set.mem_ofPred_eq] <;>
    dsimp [s0,s1,s2,pt] <;> norm_num <;> (repeat' constructor) <;> linarith

#print axioms cornerRegion_inter_null
#print axioms inscribedHexagon_cornerRegion_inter_null
end Certificate.Packing.HVGeometry
