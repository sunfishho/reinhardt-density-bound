import Certificate.HVTriangleGeometry
import Certificate.CompactExclusion

/-! Identification of the published geometric area expression with the exact
scalar expression used by the certificate's compact-exclusion proof. This
is an identity; it does not assume or claim the remaining area lower bound. -/
namespace Certificate.Packing.HVGeometry
open Certificate.Confinement
set_option maxHeartbeats 0

lemma corner_penalty_expression (u v w : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w) :
    max 0 (Real.sqrt 3/4*v*w-Real.sqrt ((Real.sqrt 3*u^2)*(Real.sqrt 3/4*v*w))) =
      Real.sqrt 3/4*areaTerm u v w := by
  have hs : Real.sqrt ((Real.sqrt 3*u^2)*(Real.sqrt 3/4*v*w)) =
      Real.sqrt 3/2*u*Real.sqrt (v*w) := by
    apply (Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)).2
    calc (Real.sqrt 3*u^2)*(Real.sqrt 3/4*v*w) =
        (Real.sqrt 3/2*u)^2*(v*w) := by ring
      _ = (Real.sqrt 3/2*u*Real.sqrt (v*w))^2 := by
        simp only [mul_pow,Real.sq_sqrt (mul_nonneg hv hw)]
  rw [hs,show Real.sqrt 3/4*v*w-Real.sqrt 3/2*u*Real.sqrt (v*w) =
    Real.sqrt 3/4*(v*w-2*u*Real.sqrt (v*w)) by ring]
  unfold areaTerm
  rw [mul_max_of_nonneg _ _ (by positivity : 0 ≤ Real.sqrt 3/4),mul_zero]

/-- The exact RHS of HV 5.0.6, divided by the hexagon's normalized area,
is the `areaScore` used in the final conditional density theorem. -/
theorem geometric_areaScore_identity (u v w : ℝ)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w) (he2 : u*v+v*w+w*u=1) :
    (3*Real.sqrt 3/2+2*(
      max 0 (triangleArea s0 (p0 u v w) s1 - Real.sqrt
        (triangleArea (p1 u v w) (q0 u v w) (p2 u v w) * triangleArea s0 (p0 u v w) s1)) +
      max 0 (triangleArea s1 (p1 u v w) s2 - Real.sqrt
        (triangleArea (p2 u v w) (q1 u v w) (-p0 u v w) * triangleArea s1 (p1 u v w) s2)) +
      max 0 (triangleArea s2 (p2 u v w) (-s0) - Real.sqrt
        (triangleArea (-p0 u v w) (q2 u v w) (-p1 u v w) * triangleArea s2 (p2 u v w) (-s0)))
      ))/(2*Real.sqrt 3) = areaScore u v w := by
  obtain ⟨h0,h1,h2⟩ := interior_triangle_areas u v w hu hv hw he2
  obtain ⟨e0,e1,e2⟩ := exterior_triangle_areas u v w he2
  rw [h0,h1,h2,e0,e1,e2,corner_penalty_expression v u w hv hu hw,
    corner_penalty_expression w u v hw hu hv,corner_penalty_expression u v w hu hv hw]
  unfold areaScore
  have hs : Real.sqrt (3:ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  field_simp
  ring

#print axioms geometric_areaScore_identity
end Certificate.Packing.HVGeometry
