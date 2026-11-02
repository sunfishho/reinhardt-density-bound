import Certificate.SupportingFormNormalization
import Certificate.MinimizerIrreducibility
import Mathlib.Analysis.SpecificLimits.Basic

/-! Symmetric supporting-slab cuts, with an explicit inner approximation.
These are actual convex discs, not hypothetical shaving data. -/
namespace Certificate.Packing
open Set Filter Topology MeasureTheory
set_option maxHeartbeats 0

noncomputable def supportCut (K : Set E) (ψ : E →ₗ[ℝ] ℝ) (c : ℝ) : Set E :=
  {x | x ∈ K ∧ |ψ x| ≤ c}

lemma supportCut_mono {K : Set E} {ψ : E →ₗ[ℝ] ℝ} {a b : ℝ} (h : a ≤ b) :
    supportCut K ψ a ⊆ supportCut K ψ b := fun _ hx => ⟨hx.1,hx.2.trans h⟩

lemma supportCut_isDisc {K : Set E} (hK : IsSymmetricConvexDisc K)
    (ψ : E →ₗ[ℝ] ℝ) {c : ℝ} (hc : 0 < c) : IsSymmetricConvexDisc (supportCut K ψ c) := by
  have hcont : Continuous (fun x : E => |ψ x|) := ψ.continuous_of_finiteDimensional.abs
  have hzero : (0:E) ∈ interior (supportCut K ψ c) := by
    apply mem_interior_iff_mem_nhds.2
    filter_upwards [mem_interior_iff_mem_nhds.1 (symmetricConvexDisc_zero_interior hK),
      (isOpen_lt hcont continuous_const).mem_nhds (show |ψ (0:E)| < c by simpa using hc)] with x hx hxc
    exact ⟨hx,hxc.le⟩
  refine ⟨?_,hK.2.1.inter_right (isClosed_le hcont continuous_const),⟨0,hzero⟩,?_⟩
  · intro x hx y hy a b ha hb hab
    refine ⟨hK.1 hx.1 hy.1 ha hb hab,?_⟩
    simp only [map_add,map_smul,smul_eq_mul]
    calc
      |a*ψ x+b*ψ y| ≤ |a*ψ x|+|b*ψ y| := abs_add_le _ _
      _ = a*|ψ x|+b*|ψ y| := by rw [abs_mul,abs_mul,abs_of_nonneg ha,abs_of_nonneg hb]
      _ ≤ a*c+b*c := add_le_add (mul_le_mul_of_nonneg_left hx.2 ha) (mul_le_mul_of_nonneg_left hy.2 hb)
      _ = c := by nlinarith
  · intro x
    simp only [supportCut,mem_ofPred_eq,map_neg,abs_neg]
    exact and_congr (hK.2.2.2 x) Iff.rfl

noncomputable def shaveScale (n : ℕ) : ℝ := 1-(1/((n:ℝ)+1))/2

lemma shaveScale_bounds (n : ℕ) : 1/2 ≤ shaveScale n ∧ shaveScale n < 1 := by
  have hn : 0 ≤ (n:ℝ) := Nat.cast_nonneg n
  have hp : 0 < 1/((n:ℝ)+1) := by positivity
  have hle : 1/((n:ℝ)+1) ≤ 1 := (div_le_iff₀ (by positivity)).2 (by linarith)
  unfold shaveScale
  constructor <;> linarith

lemma tendsto_shaveScale : Tendsto shaveScale atTop (𝓝 (1:ℝ)) := by
  have h := (tendsto_const_nhds (x := (1:ℝ)) (f := (atTop : Filter ℕ))).sub
    ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)).div_const 2)
  unfold shaveScale
  convert h using 1 <;> norm_num

lemma smul_mem_supportCut {K : Set E} (hK : IsSymmetricConvexDisc K)
    (ψ : E →ₗ[ℝ] ℝ) (hψ : ∀ x ∈ K, |ψ x| ≤ 1)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) {x : E} (hx : x ∈ K) :
    t • x ∈ supportCut K ψ t := by
  refine ⟨hK.1.smul_mem_of_zero_mem (interior_subset (symmetricConvexDisc_zero_interior hK)) hx ht,?_⟩
  rw [map_smul,smul_eq_mul,abs_mul,abs_of_nonneg ht.1]
  simpa using mul_le_mul_of_nonneg_left (hψ x hx) ht.1

lemma supportCut_proper {K : Set E} {ψ : E →ₗ[ℝ] ℝ} {u : E}
    (hu : u ∈ K) (hψ : ψ u=1) {c : ℝ} (hc : c < 1) : supportCut K ψ c ⊂ K := by
  refine ⟨fun _ hx => hx.1,?_⟩
  intro h
  have hh := (h hu).2
  rw [hψ,abs_one] at hh
  exact (not_le_of_gt hc) hh

#print axioms supportCut_isDisc
#print axioms smul_mem_supportCut
end Certificate.Packing
