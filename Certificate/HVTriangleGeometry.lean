import Certificate.ParallelCutArea
import Certificate.ConfinementRho

/-! The explicit geometric triangle-area formulas in HV Lemma 5.0.4.
The coordinates below describe the midpoint hexagon in circle representation.
All areas are the Lebesgue areas defined in `ParallelCutArea`. -/
namespace Certificate.Packing.HVGeometry
open MeasureTheory Set Pointwise
set_option maxHeartbeats 0

noncomputable def pt (x y : ℝ) : E := WithLp.toLp 2 ![x,y]
noncomputable def s0 : E := pt 1 0
noncomputable def s1 : E := pt (1/2) (Real.sqrt 3/2)
noncomputable def s2 : E := pt (-1/2) (Real.sqrt 3/2)
noncomputable def p0 (u v w : ℝ) : E := pt (1+w*(u-v)/2) (Real.sqrt 3*w*(u+v)/2)
noncomputable def p1 (u v w : ℝ) : E := 2 • s1-p0 u v w
noncomputable def p2 (u v w : ℝ) : E := 2 • s2-p1 u v w
noncomputable def q0 (u v w : ℝ) : E := p1 u v w + pt (-v^2-2*v*w) (Real.sqrt 3*v^2)
noncomputable def q1 (u v w : ℝ) : E := p2 u v w + pt (-u*w-2*w^2) (-Real.sqrt 3*u*w)
noncomputable def q2 (u v w : ℝ) : E := -p0 u v w + pt (-u*(u-v)) (-Real.sqrt 3*u*(u+v))

lemma midpoints (u v w : ℝ) :
    (1/2:ℝ) • (p0 u v w-p2 u v w) = s0 ∧
    (1/2:ℝ) • (p0 u v w+p1 u v w) = s1 ∧
    (1/2:ℝ) • (p1 u v w+p2 u v w) = s2 := by
  constructor
  · ext i; fin_cases i <;> simp [p0,p1,p2,s0,s1,s2,pt] <;> ring
  · constructor <;> dsimp [p1,p2] <;> module

/-- These are the intersections of the indicated extended edges; positivity
of `u,v,w` makes the scalar factors nonzero. -/
theorem exterior_edge_incidence (u v w : ℝ) (he2 : u*v+v*w+w*u=1) :
    u • (q0 u v w-p1 u v w) = v • (p1 u v w-p0 u v w) ∧
    w • (q0 u v w-p2 u v w) = -v • (-p0 u v w-p2 u v w) ∧
    v • (q1 u v w-p2 u v w) = w • (p2 u v w-p1 u v w) ∧
    u • (q1 u v w+p0 u v w) = -w • (-p1 u v w+p0 u v w) ∧
    w • (q2 u v w+p0 u v w) = u • (-p0 u v w-p2 u v w) ∧
    v • (q2 u v w+p1 u v w) = -u • (-p2 u v w+p1 u v w) := by
  have he (c : ℝ) : c*(u*v+v*w+w*u)=c := by rw [he2]; ring
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  all_goals
    ext i
    fin_cases i <;> simp [p0,p1,p2,q0,q1,q2,s0,s1,s2,pt]
    all_goals nlinarith [he u,he v,he w,he (Real.sqrt 3*u),he (Real.sqrt 3*v),he (Real.sqrt 3*w)]

/-- The three inner corner triangles, in cyclic order. -/
theorem interior_triangle_areas (u v w : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w)
    (he2 : u*v+v*w+w*u=1) :
    triangleArea s0 (p0 u v w) s1 = Real.sqrt 3/4*u*w ∧
    triangleArea s1 (p1 u v w) s2 = Real.sqrt 3/4*u*v ∧
    triangleArea s2 (p2 u v w) (-s0) = Real.sqrt 3/4*v*w := by
  have h0 : det2 (p0 u v w-s0) (s1-s0) = Real.sqrt 3*u*w/2 := by
    simp [det2,p0,s0,s1,pt]; ring
  have h1 : det2 (p1 u v w-s1) (s2-s1) = Real.sqrt 3*u*v/2 := by
    simp [det2,p0,p1,s0,s1,s2,pt]
    linear_combination -(Real.sqrt 3/2)*he2
  have h2 : det2 (p2 u v w-s2) (-s0-s2) = Real.sqrt 3*v*w/2 := by
    simp [det2,p0,p1,p2,s0,s1,s2,pt]; ring
  simp only [triangleArea_eq_det, h0,h1,h2,abs_of_nonneg (show 0 ≤ Real.sqrt 3*u*w/2 by positivity),
    abs_of_nonneg (show 0 ≤ Real.sqrt 3*u*v/2 by positivity),
    abs_of_nonneg (show 0 ≤ Real.sqrt 3*v*w/2 by positivity)]
  constructor; ring
  constructor <;> ring

/-- The exterior triangles opposite the three corners. -/
theorem exterior_triangle_areas (u v w : ℝ) (he2 : u*v+v*w+w*u=1) :
    triangleArea (p1 u v w) (q0 u v w) (p2 u v w) = Real.sqrt 3*v^2 ∧
    triangleArea (p2 u v w) (q1 u v w) (-p0 u v w) = Real.sqrt 3*w^2 ∧
    triangleArea (-p0 u v w) (q2 u v w) (-p1 u v w) = Real.sqrt 3*u^2 := by
  have h0 : det2 (q0 u v w-p1 u v w) (p2 u v w-p1 u v w) = 2*Real.sqrt 3*v^2 := by
    simp [det2,p0,p1,p2,q0,s0,s1,s2,pt]
    linear_combination -2*Real.sqrt 3*v*w*he2
  have h1 : det2 (q1 u v w-p2 u v w) (-p0 u v w-p2 u v w) = 2*Real.sqrt 3*w^2 := by
    simp [det2,p0,p1,p2,q1,s0,s1,s2,pt]
    linear_combination 2*Real.sqrt 3*w^2*he2
  have h2 : det2 (q2 u v w-(-p0 u v w)) (-p1 u v w-(-p0 u v w)) = 2*Real.sqrt 3*u^2 := by
    simp [det2,p0,p1,p2,q2,s0,s1,s2,pt]; ring
  simp only [triangleArea_eq_det,h0,h1,h2,
    abs_of_nonneg (show 0 ≤ 2*Real.sqrt 3*v^2 by positivity),
    abs_of_nonneg (show 0 ≤ 2*Real.sqrt 3*w^2 by positivity),
    abs_of_nonneg (show 0 ≤ 2*Real.sqrt 3*u^2 by positivity)]
  constructor; ring
  constructor <;> ring

theorem interior_area_sum (u v w : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w)
    (he2 : u*v+v*w+w*u=1) :
    triangleArea s0 (p0 u v w) s1 + triangleArea s1 (p1 u v w) s2 +
      triangleArea s2 (p2 u v w) (-s0) = Real.sqrt 3/4 := by
  obtain ⟨h0,h1,h2⟩ := interior_triangle_areas u v w hu hv hw he2
  rw [h0,h1,h2]
  linear_combination (Real.sqrt 3/4)*he2

#print axioms interior_triangle_areas
#print axioms exterior_triangle_areas
#print axioms interior_area_sum
end Certificate.Packing.HVGeometry
