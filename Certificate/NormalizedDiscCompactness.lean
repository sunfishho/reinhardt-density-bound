import Certificate.DiscAffineNormalization
import Mathlib.Topology.Sets.VietorisTopology

/-! A compact family containing a linear normalization of every symmetric
convex disc. This is the selection-theorem part of the minimizer construction. -/
namespace Certificate.Packing
open Set Topology TopologicalSpace
set_option maxHeartbeats 0

lemma compact_subset_closed {α : Type*} [TopologicalSpace α]
    (f g : α → Compacts E) (hf : Continuous f) (hg : Continuous g) :
    IsClosed {x | (f x : Set E) ⊆ g x} := by
  have he : {x | (f x : Set E) ⊆ g x} = {x | f x ⊔ g x = g x} := by
    ext x
    change f x ≤ g x ↔ f x ⊔ g x = g x
    exact sup_eq_right.symm
  rw [he]
  exact isClosed_eq (hf.sup hg) hg

lemma isClosed_convex_compacts : IsClosed {K : Compacts E | Convex ℝ (K : Set E)} := by
  have he : {K : Compacts E | Convex ℝ (K : Set E)} =
      ⋂ (a : ℝ) (b : ℝ) (_ : 0 ≤ a) (_ : 0 ≤ b) (_ : a+b=1),
        {K : Compacts E | ((K ×ˢ K).map (fun p : E × E => a • p.1+b • p.2)
          (by fun_prop) : Set E) ⊆ K} := by
    ext K
    simp only [mem_setOf_eq,mem_iInter,Compacts.coe_map,Compacts.coe_prod,image_subset_iff]
    constructor
    · intro h a b ha hb hab p hp
      exact h hp.1 hp.2 ha hb hab
    · intro h x hx y hy a b ha hb hab
      exact h a b ha hb hab (show (x,y) ∈ (K : Set E) ×ˢ (K : Set E) from ⟨hx,hy⟩)
  rw [he]
  repeat apply isClosed_iInter; intro
  apply compact_subset_closed _ _ _ continuous_id
  exact (show Continuous (fun p : E × E => _ • p.1+_ • p.2) from by fun_prop).compacts_map.comp
    (Compacts.continuous_prod.comp (continuous_id.prodMk continuous_id))

lemma isClosed_symmetric_compacts :
    IsClosed {K : Compacts E | IsSymmetricSet (K : Set E)} := by
  have he : {K : Compacts E | IsSymmetricSet (K : Set E)} =
      {K : Compacts E | K.map (fun x : E => -x) continuous_neg = K} := by
    ext K
    simp only [mem_setOf_eq]
    constructor
    · intro h
      apply Compacts.ext
      ext x
      simp only [Compacts.coe_map,mem_image]
      constructor
      · rintro ⟨y,hy,rfl⟩; exact (h y).1 hy
      · intro hx; exact ⟨-x,(h x).1 hx,neg_neg x⟩
    · intro h x
      have heq := congrArg (fun C : Compacts E => (C : Set E)) h
      constructor
      · intro hx
        rw [← heq]
        exact ⟨x,hx,rfl⟩
      · intro hx
        rw [← heq]
        exact ⟨-x,hx,neg_neg x⟩
  rw [he]
  exact isClosed_eq continuous_neg.compacts_map continuous_id

lemma isClosed_contains_diamond :
    IsClosed {K : Compacts E | coordinateDiamond ⊆ (K : Set E)} := by
  have hc : IsCompact coordinateDiamond :=
    (by simp : ({point 1 0,point (-1) 0,point 0 1,point 0 (-1)} : Set E).Finite).isCompact_convexHull ℝ
  exact compact_subset_closed (fun _ : Compacts E => ⟨coordinateDiamond,hc⟩) id
    continuous_const continuous_id

def normalizedDiscs : Set (Compacts E) :=
  {K | Convex ℝ (K : Set E) ∧ IsSymmetricSet (K : Set E) ∧
    coordinateDiamond ⊆ (K : Set E) ∧ (K : Set E) ⊆ square}

theorem isCompact_normalizedDiscs : IsCompact normalizedDiscs := by
  apply (Compacts.isCompact_subsets_of_isCompact isCompact_square).of_isClosed_subset
  · exact isClosed_convex_compacts.inter (isClosed_symmetric_compacts.inter
      (isClosed_contains_diamond.inter (Compacts.isClosed_subsets_of_isClosed isCompact_square.isClosed)))
  · exact fun _ h => h.2.2.2

/-- Every original disc has a representative in this particular compact family.
This does not assert continuity or minimization of a packing objective. -/
theorem exists_normalized_representative (K : Set E) (hK : IsSymmetricConvexDisc K) :
    ∃ L : E ≃ₗ[ℝ] E, ∃ C ∈ normalizedDiscs, (C : Set E) = L '' K := by
  obtain ⟨L,hL,hd,hs⟩ := exists_affine_normalized_disc K hK
  exact ⟨L,⟨L '' K,hL.2.1⟩,⟨hL.1,hL.2.2.2,hd,hs⟩,rfl⟩

#print axioms isCompact_normalizedDiscs
#print axioms exists_normalized_representative
end Certificate.Packing
