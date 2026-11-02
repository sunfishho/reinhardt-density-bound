import Certificate.RadialBoundaryConstruction

/-! Quantitative regularity of the explicitly constructed radial boundary.
Lipschitz regularity is weaker than the C¹ balanced boundary needed by the
Reinhardt frame, and is proved here without assuming a minimizing body. -/
namespace Certificate.Packing
open Set Metric
open scoped NNReal
set_option maxHeartbeats 0

lemma sphere_unit_norm {u : E} (hu : u ∈ sphere 0 1) : ‖u‖=1 := by
  simpa [mem_sphere,dist_zero_right] using hu

lemma disc_inverse_gauge_le {K : Set E} (hK : IsSymmetricConvexDisc K)
    {R : ℝ} (hR : ∀ x ∈ K, ‖x‖ ≤ R) {u : E} (hu : u ∈ sphere 0 1) :
    (gauge K u)⁻¹ ≤ R := by
  have hn := sphere_unit_norm hu
  have hgu := disc_gauge_pos hK (x:=u) (by intro h; simp [h] at hn)
  have hm : discRadialHomeomorph K hK u ∈ K :=
    frontier_subset_closure.trans hK.2.1.isClosed.closure_subset
      (discRadialHomeomorph_sphere hK ▸ mem_image_of_mem _ hu)
  have hh := hR _ hm
  simpa [discRadialHomeomorph_on_sphere hK hu,norm_smul,Real.norm_eq_abs,
    abs_of_pos hgu,hn] using hh

/-- The boundary parametrization is Lipschitz on the unit circle. -/
theorem discRadialHomeomorph_lipschitz_sphere {K : Set E} (hK : IsSymmetricConvexDisc K) :
    ∃ C : ℝ≥0, LipschitzOnWith C (discRadialHomeomorph K hK) (sphere 0 1) := by
  obtain ⟨R,hR0,hR⟩ := hK.2.1.isBounded.exists_pos_norm_le
  obtain ⟨C,hC⟩ := hK.1.lipschitz_gauge (disc_mem_nhds_zero hK)
  refine ⟨⟨R+R^2*C,by positivity⟩,?_⟩
  apply LipschitzOnWith.of_dist_le_mul
  intro u hu v hv
  have hun := sphere_unit_norm hu
  have hvn := sphere_unit_norm hv
  have hgu := disc_gauge_pos hK (x:=u) (by intro h; simp [h] at hun)
  have hgv := disc_gauge_pos hK (x:=v) (by intro h; simp [h] at hvn)
  have huR := disc_inverse_gauge_le hK hR hu
  have hvR := disc_inverse_gauge_le hK hR hv
  have hgd : |gauge K v-gauge K u| ≤ (C:ℝ)*dist u v := by
    simpa only [Real.dist_eq,dist_comm v u] using hC.dist_le_mul v u
  have hid : |(gauge K u)⁻¹-(gauge K v)⁻¹| ≤ R^2*C*dist u v := by
    rw [inv_sub_inv' hgu.ne' hgv.ne',abs_mul,abs_mul,
      abs_of_pos (inv_pos.2 hgu),abs_of_pos (inv_pos.2 hgv)]
    calc
      (gauge K u)⁻¹ * |gauge K v-gauge K u| * (gauge K v)⁻¹ ≤
          R*((C:ℝ)*dist u v)*R := by gcongr
      _ = _ := by ring
  rw [dist_eq_norm,discRadialHomeomorph_on_sphere hK hu,discRadialHomeomorph_on_sphere hK hv]
  have he : (gauge K u)⁻¹ • u-(gauge K v)⁻¹ • v =
      (gauge K u)⁻¹ • (u-v)+((gauge K u)⁻¹-(gauge K v)⁻¹) • v := by module
  rw [he]
  calc
    ‖(gauge K u)⁻¹ • (u-v)+((gauge K u)⁻¹-(gauge K v)⁻¹) • v‖ ≤
        ‖(gauge K u)⁻¹ • (u-v)‖+‖((gauge K u)⁻¹-(gauge K v)⁻¹) • v‖ := norm_add_le _ _
    _ = (gauge K u)⁻¹*dist u v+|(gauge K u)⁻¹-(gauge K v)⁻¹| := by
      rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,
        abs_of_pos (inv_pos.2 hgu),hvn,mul_one,dist_eq_norm]
    _ ≤ R*dist u v+R^2*C*dist u v := by gcongr
    _ = _ := by change R*dist u v+R^2*C*dist u v = (R+R^2*C)*dist u v; ring

#print axioms discRadialHomeomorph_lipschitz_sphere
end Certificate.Packing
