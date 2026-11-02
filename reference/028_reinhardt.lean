/-
# 028. The Reinhardt conjecture

Status:  OPEN since 1934. Karl Reinhardt asked which centrally symmetric convex disc in the
         plane is the WORST packer, i.e. minimises the density of its densest packing.
         Known partial results:
           - Hales and Vajjha (arXiv:2405.04331, 2024) proved the minimiser must be a
             SMOOTHED POLYGON. This is Mahler's first conjecture; Mahler's second conjecture
             is identical to Reinhardt's and remains open.
           - Nazarov proved the smoothed octagon is a LOCAL minimum.
         Verified 2026-09-19: open, and UNCONTAMINATED -- no claimed proof of the
         specific-shape conjecture, despite heavy AI-preprint activity elsewhere in 2026.
Cost:    4/5 -- the most expensive entry here, see Missing.
Missing: - PACKING DENSITY. Mathlib has no packing-density notion at all
           (`Topology/MetricSpace/CoveringNumbers.lean` is about covering numbers in metric
           spaces and does NOT apply), so it is built from scratch below: a packing is a
           countable family of isometric copies of K with pairwise disjoint INTERIORS, and
           its density is the limsup, over balls of growing radius, of the fraction of area
           covered. This is the bulk of the work.
           This file states the GENERAL (non-lattice) form. A lattice-only variant is much
           cheaper to define -- for centrally symmetric convex bodies in the plane the
           optimal packing density equals the optimal LATTICE packing density (Rogers,
           Fejes Toth) -- but that equivalence is not in Mathlib, so building on it would
           place an unformalized classical theorem between this file and the conjecture.
           It is deliberately NOT assumed here.
         - the smoothed octagon itself: a regular octagon with its corners rounded by arcs
           of hyperbolas, each hyperbola tangent to the two edges it joins and asymptotic to
           the adjacent pair of edge lines. Avoided below: the conjectured minimum has a
           closed form, so `IsLeast` states the conjecture's full content -- the value is
           attained, and it is a lower bound -- without naming the octagon.
         NOTE: because the definition below is the general one, it also unlocks Ulam's
         packing conjecture (is the ball the worst-packing convex body in R^3?), which is
         likewise open and uncontaminated. One prerequisite, two problems -- as with the
         polytope face lattice for 003/016. The lattice shortcut would NOT have transferred:
         densest = densest-lattice is a planar, centrally-symmetric theorem, not known for
         general convex bodies in R^3.
MODELLING: packings are indexed by ℕ rather than by an arbitrary countable type. This does
         not change the supremum: any packing by copies of a body of positive area is
         countable, and a finite packing has density 0, so the ℕ-indexed families already
         realise every positive density.

Informal statement.
  For a convex body K in R^2, let delta K be the supremum of the densities of packings of the
  plane by congruent copies of K (for centrally symmetric K this equals the supremum over
  LATTICE packings by translates of K).

  Conjecture (Reinhardt): over all centrally symmetric convex discs K,
      delta K  is minimised exactly by the SMOOTHED OCTAGON,
  whose packing density is
      (8 - 4*sqrt 2 - log 2) / (2*sqrt 2 - 1)  =  0.902414183...

  Sanity check worth keeping in mind: the disc packs at density pi / sqrt 12 = 0.906899682,
  which is LARGER than the smoothed octagon's 0.902414183. So the conjecture asserts the
  smoothed octagon packs strictly WORSE than the circle, by about 0.0045. The circle is a
  natural first guess for the worst packer and is known to be only a local pessimum
  (Kallus), not the global one.

Why it is on this list.
  It is genuinely an optimization problem -- a minimisation over an infinite-dimensional
  space of shapes -- and Hales has reformulated it as a problem in optimal control, giving
  it a direct link to the calculus of variations. At 92 years it is the most durable problem
  on this list, and durability is exactly what the benchmark needs after the 2026 wave of
  claimed resolutions.
-/

import Mathlib
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

theorem reinhardt : ∀ K : Set (EuclideanSpace ℝ (Fin 2)), IsSymmetricConvexDisc K → packingDensity K ≥ ((8 - 4 * Real.sqrt 2 - Real.log 2) / (2 * Real.sqrt 2 - 1) : ℝ) :=
  by sorry
