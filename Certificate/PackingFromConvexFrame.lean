import Certificate.ConvexBoundaryCurvature
import Certificate.FrameAcceleration
import Certificate.PackingFromConvexBoundary

/-! Convexity supplies boundary curvature, hence the reconstructed controls.
The frame trajectory supplied here has no curvature or control fields. -/
namespace Certificate
open MeasureTheory Set Filter Packing Confinement HVGeometry Curvature
set_option maxHeartbeats 0

theorem FrameTrace.curvature_nonneg_ae {K : Set E} (hK : IsSymmetricConvexDisc K)
    {path : FrameTrajectory} (data : FrameTrace path K) :
    ∀ᵐ t ∂volume.restrict (Icc 0 path.duration), ∀ k,
      0 ≤ detPair ((path.state t).X.mulVec (direction k))
        ((tangent (stateDa path.state t) (stateDp path.state t)
          (stateDh path.state t)-1).mulVec (direction k)) := by
  rw [ae_restrict_iff' measurableSet_Icc]
  filter_upwards [ae_imp_of_ae_restrict path.derivatives_ae,volume.ae_ne (0:ℝ),
    volume.ae_ne path.duration] with t hder h0 hT ht
  have hti : t ∈ Ioo 0 path.duration :=
    ⟨lt_of_le_of_ne ht.1 (Ne.symm h0),lt_of_le_of_ne ht.2 hT⟩
  obtain ⟨ha,hp,hh⟩ := hder ht
  intro k
  let j : Fin 6 := ![0,2,1] k
  have hroot : WithLp.toLp 2 (direction k) = root j := by
    fin_cases k <;> rfl
  rw [← frame_signed_curvature _ _ _ _ (path.determinant t ht).1 k,hroot]
  apply convex_boundary_curvature_nonneg hK.1 hK.2.1.isClosed
    (symmetricConvexDisc_zero_interior hK) hti
    (fun s hs => data.boundary j s ⟨hs.1.le,hs.2.le⟩)
    (fun s hs => stateAction_hasDerivAt (path.group_derivative s hs) (root j))
    (frame_velocity_hasDerivAt (path.group_derivative t hti)
      (path.determinant t ht).2 ha hp hh (root j))
  rw [det2_stateAction,(path.determinant t ht).1,one_mul]
  obtain ⟨hρ0,hρ1,hρ2⟩ := path.star_nonneg t ht
  exact root_area_integrands_pos_of_normalized _ (path.determinant t ht).2 hρ0 hρ1 hρ2 j

/-- The curvature field is a theorem about the actual convex boundary. -/
noncomputable def FrameTrace.toCurvature {K : Set E} (hK : IsSymmetricConvexDisc K)
    {path : FrameTrajectory} (data : FrameTrace path K) : CurvatureTrajectory where
  state := path.state
  duration := path.duration
  duration_nonneg := path.duration_nonneg
  coordinates_ac := path.coordinates_ac
  determinant := path.determinant
  star_nonneg := path.star_nonneg
  group_ode := path.group_ode
  curvature_nonneg := data.curvature_nonneg_ae hK
  initial := path.initial
  terminal := path.terminal

theorem FrameTrace.toFrameBoundary {K : Set E} (hK : IsSymmetricConvexDisc K)
    {path : FrameTrajectory} (data : FrameTrace path K) :
    FrameBoundary (data.toCurvature hK).toNormalized K where
  boundary := data.boundary
  covers := data.covers
  simple := data.simple

/-- The curvature sign, controls, supporting geometry, and area statements
are derived from the convex boundary and its normalized frame path. -/
theorem Packing.packing_density_bound_of_convex_frame
    (K : Set E) (hK : IsSymmetricConvexDisc K) (path : FrameTrajectory)
    (data : FrameTrace path K) (hmin : HexAreaLowerBound K (2*Real.sqrt 3)) :
    (8950112:ℝ)/10000000 < packingDensity K :=
  packing_density_bound_of_curvature_convex_boundary K hK (data.toCurvature hK)
    (data.toFrameBoundary hK) hmin

#print axioms FrameTrace.curvature_nonneg_ae
#print axioms Packing.packing_density_bound_of_convex_frame
end Certificate
