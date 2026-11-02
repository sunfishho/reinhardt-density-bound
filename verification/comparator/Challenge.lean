import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! Independent reference: original benchmark definitions and the improved bound.
The final sorry is exclusively a reference placeholder, never an allowed solution axiom. -/
namespace Certificate.Packing
open MeasureTheory Pointwise

def IsSymmetricSet (K : Set (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∀ x, x ∈ K ↔ -x ∈ K

def IsSymmetricConvexDisc (K : Set (EuclideanSpace ℝ (Fin 2))) : Prop :=
  Convex ℝ K
  ∧ IsCompact K
  ∧ (interior K).Nonempty
  ∧ IsSymmetricSet K

def IsPacking (K : Set (EuclideanSpace ℝ (Fin 2)))
    (g : ℕ → (EuclideanSpace ℝ (Fin 2) ≃ᵢ EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∀ i j, i ≠ j → Disjoint (interior (g i '' K)) (interior (g j '' K))

def packedRegion (K : Set (EuclideanSpace ℝ (Fin 2)))
    (g : ℕ → (EuclideanSpace ℝ (Fin 2) ≃ᵢ EuclideanSpace ℝ (Fin 2))) :
    Set (EuclideanSpace ℝ (Fin 2)) :=
  ⋃ i, g i '' K

noncomputable def packingDensityOf (K : Set (EuclideanSpace ℝ (Fin 2)))
    (g : ℕ → EuclideanSpace ℝ (Fin 2) ≃ᵢ EuclideanSpace ℝ (Fin 2)) : ℝ :=
  Filter.limsup
    (fun r : ℝ =>
      (volume (packedRegion K g ∩ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) r)).toReal /
        (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) r)).toReal)
    Filter.atTop

/-- The packing density of `K`: the supremum of the densities of all packings of the plane
    by congruent copies of `K`. -/
noncomputable def packingDensity (K : Set (EuclideanSpace ℝ (Fin 2))) : ℝ :=
  sSup {d | ∃ g : ℕ → EuclideanSpace ℝ (Fin 2) ≃ᵢ EuclideanSpace ℝ (Fin 2),
    IsPacking K g ∧ d = packingDensityOf K g}


abbrev E := EuclideanSpace ℝ (Fin 2)

theorem reinhardt_density_lower_bound (K : Set E) (hK : IsSymmetricConvexDisc K) :
    (8950112 : ℝ)/10000000 < packingDensity K := by sorry

end Certificate.Packing
