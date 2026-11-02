import Certificate.DiscAffineNormalization
import Mathlib.Analysis.Convex.GaugeRescale

/-! Explicit radial construction of the boundary of any symmetric convex disc.
This provides a continuous, antipodal, one-to-one parametrization by the unit
circle. It makes no claim about differentiability or balanced critical hexagons. -/
namespace Certificate.Packing
open Set Metric Filter Topology Pointwise
set_option maxHeartbeats 0

lemma disc_mem_nhds_zero {K : Set E} (hK : IsSymmetricConvexDisc K) : K ∈ 𝓝 0 :=
  mem_interior_iff_mem_nhds.1 (symmetricConvexDisc_zero_interior hK)

lemma disc_gauge_pos {K : Set E} (hK : IsSymmetricConvexDisc K) {x : E} (hx : x ≠ 0) :
    0 < gauge K x :=
  (gauge_pos (absorbent_nhds_zero (disc_mem_nhds_zero hK))
    (NormedSpace.isVonNBounded_of_isBounded ℝ hK.2.1.isBounded)).2 hx

/-- The ambient radial homeomorphism from the Euclidean unit ball to the body. -/
noncomputable def discRadialHomeomorph (K : Set E) (hK : IsSymmetricConvexDisc K) : E ≃ₜ E :=
  gaugeRescaleHomeomorph (ball 0 1) K (convex_ball 0 1)
    (ball_mem_nhds _ one_pos) (NormedSpace.isVonNBounded_ball ℝ _ _)
    hK.1 (disc_mem_nhds_zero hK) (NormedSpace.isVonNBounded_of_isBounded ℝ hK.2.1.isBounded)

lemma discRadialHomeomorph_interior {K : Set E} (hK : IsSymmetricConvexDisc K) :
    discRadialHomeomorph K hK '' ball 0 1 = interior K := by
  unfold discRadialHomeomorph
  convert! image_gaugeRescaleHomeomorph_interior
    (convex_ball (0:E) 1) (ball_mem_nhds (0:E) one_pos)
    (NormedSpace.isVonNBounded_ball ℝ E 1) hK.1 (disc_mem_nhds_zero hK)
    (NormedSpace.isVonNBounded_of_isBounded ℝ hK.2.1.isBounded) using 1 <;>
    simp [isOpen_ball.interior_eq]

lemma discRadialHomeomorph_closedBall {K : Set E} (hK : IsSymmetricConvexDisc K) :
    discRadialHomeomorph K hK '' closedBall 0 1 = K := by
  unfold discRadialHomeomorph
  convert! image_gaugeRescaleHomeomorph_closure
    (convex_ball (0:E) 1) (ball_mem_nhds (0:E) one_pos)
    (NormedSpace.isVonNBounded_ball ℝ E 1) hK.1 (disc_mem_nhds_zero hK)
    (NormedSpace.isVonNBounded_of_isBounded ℝ hK.2.1.isBounded) using 1 <;>
    simp [closure_ball (0:E) (by norm_num : (1:ℝ) ≠ 0),hK.2.1.isClosed.closure_eq]

/-- The entire boundary is obtained, with no missing directions. -/
theorem discRadialHomeomorph_sphere {K : Set E} (hK : IsSymmetricConvexDisc K) :
    discRadialHomeomorph K hK '' sphere 0 1 = frontier K := by
  rw [← frontier_ball (0:E) (by norm_num : (1:ℝ) ≠ 0)]
  rw [← closure_sdiff_interior, image_sdiff (discRadialHomeomorph K hK).injective,
    closure_ball (0:E) (by norm_num : (1:ℝ) ≠ 0),isOpen_ball.interior_eq,
    discRadialHomeomorph_closedBall hK,discRadialHomeomorph_interior hK,
    hK.2.1.isClosed.frontier_eq]

/-- On the unit circle the construction is exactly division by the body's gauge. -/
lemma discRadialHomeomorph_on_sphere {K : Set E} (hK : IsSymmetricConvexDisc K)
    {u : E} (hu : u ∈ sphere 0 1) : discRadialHomeomorph K hK u = (gauge K u)⁻¹ • u := by
  change (gauge (ball (0:E) 1) u / gauge K u) • u = _
  have hg : gauge (ball (0:E) 1) u = 1 := by
    apply (gauge_eq_one_iff_mem_frontier (convex_ball _ _) (ball_mem_nhds _ one_pos)).2
    simpa only [frontier_ball (0:E) (by norm_num : (1:ℝ) ≠ 0)] using hu
  rw [hg,one_div]

/-- Central symmetry is respected by the constructed parametrization. -/
theorem discRadialHomeomorph_neg {K : Set E} (hK : IsSymmetricConvexDisc K) (u : E) :
    discRadialHomeomorph K hK (-u) = -discRadialHomeomorph K hK u := by
  change (gauge (ball (0:E) 1) (-u)/gauge K (-u)) • (-u) =
    -((gauge (ball (0:E) 1) u/gauge K u) • u)
  rw [gauge_neg (fun x hx => by simpa using hx),gauge_neg (fun x hx => (hK.2.2.2 x).1 hx),smul_neg]

/-- A normalized boundary is constructed, rather than supplied as a hypothesis. -/
theorem exists_radial_boundary (K : Set E) (hK : IsSymmetricConvexDisc K) :
    ∃ b : E → E, Continuous b ∧ Function.Injective b ∧
      b '' sphere 0 1 = frontier K ∧
      (∀ u : E, b (-u) = -b u) ∧
      (∀ u ∈ sphere 0 1, b u = (gauge K u)⁻¹ • u) :=
  ⟨discRadialHomeomorph K hK,(discRadialHomeomorph K hK).continuous,
    (discRadialHomeomorph K hK).injective,discRadialHomeomorph_sphere hK,
    discRadialHomeomorph_neg hK,fun _ hu => discRadialHomeomorph_on_sphere hK hu⟩

#print axioms discRadialHomeomorph_sphere
#print axioms exists_radial_boundary
end Certificate.Packing
