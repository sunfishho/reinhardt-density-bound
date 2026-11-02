import Certificate.SupportCutLocality
import Certificate.CriticalMidpointNormalContinuity

/-! Every supporting face contains a critical side midpoint. The key extra
input over contact coverage is midpoint contact for the smaller cut bodies. -/
namespace Certificate.Packing
open Set Filter Topology MeasureTheory HexParameters
set_option maxHeartbeats 0

noncomputable def parameterSideMidpoint (d : HexParameters) (i : Fin 6) : E :=
  ![(1/2:ℝ) • (d.vertex 0+d.vertex 1),(1/2:ℝ) • (d.vertex 1+d.vertex 2),
    (1/2:ℝ) • (d.vertex 2-d.vertex 0),-(1/2:ℝ) • (d.vertex 0+d.vertex 1),
    -(1/2:ℝ) • (d.vertex 1+d.vertex 2),-(1/2:ℝ) • (d.vertex 2-d.vertex 0)] i

lemma continuous_parameterSideMidpoint (i : Fin 6) : Continuous (fun d => parameterSideMidpoint d i) := by
  fin_cases i <;> simp only [parameterSideMidpoint,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.head_cons] <;>
    unfold HexParameters.vertex point <;> fun_prop

lemma parameterSideMidpoint_ofHex (H : Hex) (i : Fin 6) : parameterSideMidpoint (ofHex H) i=H.midpoint i := by
  fin_cases i <;> simp [parameterSideMidpoint,vertex_ofHex,Hex.midpoint]

lemma parameterSideMidpoint_toHex (d : HexParameters) (hd : d.Valid) (i : Fin 6) :
    parameterSideMidpoint d i=(d.toHex hd).midpoint i := rfl

lemma Hex.exists_neg_midpoint (H : Hex) (i : Fin 6) : ∃ j : Fin 6, H.midpoint j = -H.midpoint i := by
  fin_cases i
  · exact ⟨3,by simp [Hex.midpoint,neg_smul,add_comm]⟩
  · exact ⟨4,by simp [Hex.midpoint,neg_smul,add_comm]⟩
  · exact ⟨5,by simp [Hex.midpoint,neg_smul,add_comm]⟩
  · exact ⟨0,by simp [Hex.midpoint,neg_smul,add_comm]⟩
  · exact ⟨1,by simp [Hex.midpoint,neg_smul,add_comm]⟩
  · exact ⟨2,by simp [Hex.midpoint,neg_smul,add_comm]⟩

/-- Some midpoint of a critical hexagon lies on one of the two opposite
supporting faces. No boundary coverage assumption occurs in this proof. -/
theorem minimizer_support_faces_midpoint_abs {u : E} (hu : u ∈ ratioMinimizingBody)
    {ψ : E →ₗ[ℝ] ℝ} (hψ : NormalizedSupportAt ratioMinimizingBody u ψ) :
    ∃ H : Hex, ratioMinimizingBody ⊆ H.set ∧
      volume H.set=criticalHexArea ratioMinimizingBody ∧
      ∃ i : Fin 6, |ψ (H.midpoint i)|=1 := by
  let K := ratioMinimizingBody
  have hK := ratioMinimizingBody_properties.1
  have habs := normalizedSupportAt_abs hK.2.2.2 hψ
  let L (n : ℕ) := supportCut K ψ (shaveScale n)
  have hL (n : ℕ) : IsSymmetricConvexDisc (L n) :=
    supportCut_isDisc hK ψ (lt_of_lt_of_le (by norm_num) (shaveScale_bounds n).1)
  let H (n : ℕ) : Hex := Classical.choose (criticalHexArea_attained (L n) (hL n))
  have hH (n : ℕ) : L n ⊆ (H n).set ∧ volume (H n).set=criticalHexArea (L n) :=
    Classical.choose_spec (criticalHexArea_attained (L n) (hL n))
  have hsmall (n : ℕ) : volume (H n).set < criticalHexArea K :=
    (hH n).2.trans_lt (ratioMinimizingBody_irreducible (hL n)
      (supportCut_proper hu hψ.1 (shaveScale_bounds n).2))
  let d (n : ℕ) := ofHex (H n)
  have hcore := supportCut_isDisc hK ψ (by norm_num : (0:ℝ)<1/2)
  obtain ⟨r,hr,h0,h1⟩ := exists_axis_points hcore
  have hdmem (n : ℕ) : d n ∈ boundedEnclosers (supportCut K ψ (1/2)) (criticalHexArea K).toReal := by
    refine ⟨valid_ofHex (H n),encloses_ofHex (fun x hx => (hH n).1 (supportCut_mono (shaveScale_bounds n).1 hx)),?_⟩
    have hh := ENNReal.toReal_mono (criticalHexArea_finite hK) (hsmall n).le
    rw [(H n).volume_eq_covolume,ENNReal.toReal_ofReal (abs_nonneg _)] at hh
    simpa [d,covolume_ofHex] using hh
  obtain ⟨q,hq,f,hf,ht⟩ := (isCompact_boundedEnclosers hr h0 h1 (criticalHexArea K).toReal).isSeqCompact hdmem
  have hs := tendsto_shaveScale.comp hf.tendsto_atTop
  have hen : Encloses K q := encloses_of_limit_scaled ht hs (by
    intro n x hx
    apply (maxStrip_le_iff _ _).2
    exact encloses_ofHex (hH (f n)).1 _ (smul_mem_supportCut hK ψ habs
      ⟨by linarith [(shaveScale_bounds (f n)).1],(shaveScale_bounds (f n)).2.le⟩ hx))
  have hcrit : q ∈ criticalFamily K := critical_of_bounded_encloses hK hq.1 hen hq.2.2
  let G := q.toHex hq.1
  have harea : volume G.set=criticalHexArea K := critical_parameter_area hcrit
  have hGstrict : G.Strict := criticalHexagon_of_minimizer_strict G hen harea
  refine ⟨G,hen,harea,?_⟩
  by_contra hn
  have hall (i : Fin 6) : |ψ (G.midpoint i)| < 1 := by
    have hm := criticalHexagon_of_minimizer_midpoint_frontier G hen harea i
    have hmK := frontier_subset_iff_isClosed.2 hK.2.1.isClosed hm
    exact lt_of_le_of_ne (habs _ hmK) (fun he => hn ⟨i,he⟩)
  have evs : ∀ᶠ n in atTop, (H (f n)).Strict := by
    have h01 := ((continuous_incidence 1 0).abs.tendsto q |>.comp ht).eventually (gt_mem_nhds hGstrict.1)
    have h21 := ((continuous_incidence 2 1).abs.tendsto q |>.comp ht).eventually (gt_mem_nhds hGstrict.2.1)
    have h02 := ((continuous_incidence 0 2).abs.tendsto q |>.comp ht).eventually (gt_mem_nhds hGstrict.2.2)
    filter_upwards [h01,h21,h02] with n hn1 hn2 hn3
    simpa [d,form_ofHex,vertex_ofHex,Hex.Strict] using And.intro hn1 (And.intro hn2 hn3)
  have evm : ∀ᶠ n in atTop, ∀ i : Fin 6, |ψ ((H (f n)).midpoint i)| < shaveScale (f n) := by
    apply Filter.eventually_all.2
    intro i
    have hm := (ψ.continuous_of_finiteDimensional.abs.comp (continuous_parameterSideMidpoint i)).tendsto q |>.comp ht
    have he := hm.eventually_lt hs (hall i)
    simpa [d,parameterSideMidpoint_ofHex] using he
  obtain ⟨n,hnstrict,hnmid⟩ := (evs.and evm).exists
  have hm (i : Fin 6) : (H (f n)).midpoint i ∈ L (f n) :=
    (H (f n)).midpoint_mem_of_strict_critical hnstrict (hL (f n)) (hH (f n)).1
      (fun F hF => by rw [(hH (f n)).2]; exact criticalHexArea_le F hF) i
  have hfull : K ⊆ (H (f n)).set :=
    (H (f n)).encloses_of_supportCut_midpoints hK ψ (hH (f n)).1 (fun i => (hm i).1) hnmid
  exact (not_lt_of_ge (criticalHexArea_le (H (f n)) hfull)) (hsmall (f n))

theorem minimizer_support_face_midpoint {u : E} (hu : u ∈ ratioMinimizingBody)
    {ψ : E →ₗ[ℝ] ℝ} (hψ : NormalizedSupportAt ratioMinimizingBody u ψ) :
    ∃ H : Hex, ratioMinimizingBody ⊆ H.set ∧
      volume H.set=criticalHexArea ratioMinimizingBody ∧
      ∃ i : Fin 6, ψ (H.midpoint i)=1 := by
  obtain ⟨H,hH,ha,i,hi⟩ := minimizer_support_faces_midpoint_abs hu hψ
  rcases (abs_eq (by norm_num : (0:ℝ)≤1)).1 hi with he | he
  · exact ⟨H,hH,ha,i,he⟩
  · obtain ⟨j,hj⟩ := H.exists_neg_midpoint i
    exact ⟨H,hH,ha,j,by rw [hj,map_neg,he]; norm_num⟩

#print axioms minimizer_support_faces_midpoint_abs
#print axioms minimizer_support_face_midpoint
end Certificate.Packing
