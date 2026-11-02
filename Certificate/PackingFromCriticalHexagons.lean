import Certificate.NormalizedHexagon
import Certificate.AreaControlledTrajectory
import Certificate.CurvatureTrajectory

/-! Packing bound with the HV area estimate derived from actual critical
hexagon geometry. The remaining presentation/existence obligations are
explicit fields; no existence or boundary theorem is assumed as an axiom. -/
namespace Certificate.Packing
open MeasureTheory Set Confinement HVGeometry
set_option maxHeartbeats 0

/-- The still-required geometric presentation of a normalized balanced disc.
The fields describe frames, supporting strips, boundary midpoints, minimality,
and the area identity. None is the analytic `HasAreaEstimate` conclusion. -/
structure CriticalHexagonFamily (path : NormalizedTrajectory) (K : Set E) where
  frame : ℝ → (E ≃ₗ[ℝ] E)
  frame_det : ∀ t ∈ Icc 0 path.duration,
    |LinearMap.det (frame t : E →ₗ[ℝ] E)| = 1
  star_pos : ∀ t ∈ Icc 0 path.duration,
    0 < rho0 (path.state t) ∧ 0 < rho1 (path.state t) ∧ 0 < rho2 (path.state t)
  enclosed : ∀ t ∈ Icc 0 path.duration,
    InHexagon (frame t '' K) (rho0 (path.state t)) (rho1 (path.state t)) (rho2 (path.state t))
  midpoint0 : ∀ t ∈ Icc 0 path.duration, s0 ∈ frame t '' K
  midpoint1 : ∀ t ∈ Icc 0 path.duration, s1 ∈ frame t '' K
  midpoint2 : ∀ t ∈ Icc 0 path.duration, s2 ∈ frame t '' K
  minimum_area : HexAreaLowerBound K (2*Real.sqrt 3)
  cost_eq_area : path.cost = (volume K).toReal

/-- HV 5.0.6 discharges the former analytic area-estimate assumption. -/
theorem CriticalHexagonFamily.hasAreaEstimate {K : Set E} (hK : IsSymmetricConvexDisc K)
    {path : NormalizedTrajectory} (data : CriticalHexagonFamily path K) :
    path.HasAreaEstimate := by
  intro t ht
  let L := data.frame t
  have hd : |LinearMap.det (L : E →ₗ[ℝ] E)| = 1 := data.frame_det t ht
  have hmin : HexAreaLowerBound (L '' K) (2*Real.sqrt 3) := by
    have hh := data.minimum_area.linear_image L
    rw [hd,one_mul] at hh
    exact hh
  obtain ⟨hu,hv,hw⟩ := data.star_pos t ht
  have hh := hales_vajjha_area_bound (L '' K)
    (hK.2.1.image L.toContinuousLinearEquiv.continuous)
    (hK.1.linear_image (L : E →ₗ[ℝ] E))
    (symmetric_linear_image hK.2.2.2 (L : E →ₗ[ℝ] E))
    (rho0 (path.state t)) (rho1 (path.state t)) (rho2 (path.state t)) hu hv hw
    (rho_e2 (path.state t) (path.determinant t ht).2)
    (data.enclosed t ht) (data.midpoint0 t ht) (data.midpoint1 t ht) (data.midpoint2 t ht) hmin
  have hvol : volume (L '' K) = volume K := by
    have hm := Measure.addHaar_image_linearMap volume (L : E →ₗ[ℝ] E) K
    rw [hd,ENNReal.ofReal_one,one_mul] at hm
    exact hm
  rw [hvol,← data.cost_eq_area] at hh
  exact hh

/-- The density bound now needs only the still-unconstructed balanced-disc
presentation; no separate area estimate or packing comparison is supplied. -/
theorem packing_density_bound_of_critical_hexagon_family
    (K : Set E) (hK : IsSymmetricConvexDisc K) (path : NormalizedTrajectory)
    (data : CriticalHexagonFamily path K) :
    (8950112:ℝ)/10000000 < packingDensity K := by
  apply density_bound_from_control (packingDensity K) path.cost
    (path.cost_lower_bound (data.hasAreaEstimate hK))
  rw [data.cost_eq_area]
  have ht : (0:ℝ) ∈ Icc 0 path.duration := ⟨le_rfl,path.duration_nonneg⟩
  obtain ⟨hu,hv,hw⟩ := data.star_pos 0 ht
  exact packingDensity_ge_area_of_normalized_frame K hK (data.frame 0) (data.frame_det 0 ht)
    (rho0 (path.state 0)) (rho1 (path.state 0)) (rho2 (path.state 0)) hu hv hw
    (rho_e2 (path.state 0) (path.determinant 0 ht).2) (data.enclosed 0 ht)

/-- Controls may still be reconstructed from the previously verified
nonnegative-curvature hypotheses. -/
theorem packing_density_bound_of_curvature_critical_hexagon_family
    (K : Set E) (hK : IsSymmetricConvexDisc K) (path : CurvatureTrajectory)
    (data : CriticalHexagonFamily path.toNormalized K) :
    (8950112:ℝ)/10000000 < packingDensity K :=
  packing_density_bound_of_critical_hexagon_family K hK path.toNormalized data

#print axioms CriticalHexagonFamily.hasAreaEstimate
#print axioms packing_density_bound_of_critical_hexagon_family
#print axioms packing_density_bound_of_curvature_critical_hexagon_family
end Certificate.Packing
