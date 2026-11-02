import Certificate.MinimizerSupportFaceMidpoint
import Certificate.CriticalMidpointRegularCurves
import Mathlib.Analysis.Convex.Extreme

/-! Supporting-face endpoints are critical midpoints. Any missing midpoint
on the boundary must lie strictly inside a flat supporting segment. -/
namespace Certificate.Packing
open Set Filter Topology MeasureTheory
set_option maxHeartbeats 0

/-- Every nonzero linear functional attains its maximum over the minimizer
at a side midpoint of an enclosing critical hexagon. -/
theorem minimizer_support_maximum_at_critical_midpoint (ψ : E →ₗ[ℝ] ℝ) (hne : ψ ≠ 0) :
    ∃ x ∈ criticalMidpointSet,
      ∀ y ∈ ratioMinimizingBody, ψ y ≤ ψ x := by
  have hK := ratioMinimizingBody_properties.1
  obtain ⟨u,hu,humax⟩ := hK.2.1.exists_isMaxOn (hK.2.2.1.mono interior_subset)
    ψ.continuous_of_finiteDimensional.continuousOn
  have hpos := support_level_pos (symmetricConvexDisc_zero_interior hK) u ψ hne
    (fun y hy => humax hy)
  have hnorm : NormalizedSupportAt ratioMinimizingBody u ((1/ψ u) • ψ) := by
    refine ⟨?_,?_⟩
    · simp [hpos.ne']
    · intro y hy
      change (1/ψ u)*ψ y ≤ 1
      rw [one_div_mul_eq_div,div_le_one hpos]
      exact humax hy
  obtain ⟨H,hH,ha,i,hval⟩ := minimizer_support_face_midpoint hu hnorm
  let x := H.midpoint i
  have hx : x ∈ criticalMidpointSet := critical_hexagon_midpoint_mem_set H hH ha i
  have hvalue : ψ x=ψ u := by
    change (1/ψ u)*ψ x=1 at hval
    rw [one_div_mul_eq_div,div_eq_one_iff_eq hpos.ne'] at hval
    exact hval
  refine ⟨x,hx,?_⟩
  intro y hy
  rw [hvalue]
  exact humax hy

lemma criticalMidpointSet_nonempty : (criticalMidpointSet).Nonempty := by
  have hne : coord 0 ≠ 0 := by
    intro he
    have hh := LinearMap.congr_fun he (point 1 0)
    norm_num [coord_eval,point] at hh
  obtain ⟨x,hx,_⟩ := minimizer_support_maximum_at_critical_midpoint (coord 0) hne
  exact ⟨x,hx⟩


/-- The zero functional is included, so perturbed support forms need no
separate nonvanishing argument. -/
theorem minimizer_support_maximum_at_midpoint (ψ : E →ₗ[ℝ] ℝ) :
    ∃ x ∈ criticalMidpointSet, ∀ y ∈ ratioMinimizingBody, ψ y ≤ ψ x := by
  by_cases h : ψ = 0
  · obtain ⟨x,hx⟩ := criticalMidpointSet_nonempty
    exact ⟨x,hx,by simp [h]⟩
  · exact minimizer_support_maximum_at_critical_midpoint ψ h

/-- Tilt a support form by a vanishing positive multiple of a second form.
Compactness gives a critical midpoint maximizing the second form on the
original supporting face. -/
theorem criticalMidpoint_support_face_max {u : E} (hu : u ∈ ratioMinimizingBody)
    {ψ : E →ₗ[ℝ] ℝ} (hψ : NormalizedSupportAt ratioMinimizingBody u ψ)
    (χ : E →ₗ[ℝ] ℝ) :
    ∃ p ∈ criticalMidpointSet, ψ p = 1 ∧
      ∀ x ∈ ratioMinimizingBody, ψ x = 1 → χ x ≤ χ p := by
  let ε (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have hεlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  choose p hp hmax using fun n => minimizer_support_maximum_at_midpoint (ψ + ε n • χ)
  obtain ⟨q,hq,f,hf,ht⟩ := isCompact_criticalMidpointSet.isSeqCompact hp
  have hpK (n : ℕ) : p n ∈ ratioMinimizingBody :=
    frontier_subset_iff_isClosed.2 ratioMinimizingBody_properties.1.2.1.isClosed
      (criticalMidpointSet_subset_frontier (hp n))
  have hqK : q ∈ ratioMinimizingBody :=
    frontier_subset_iff_isClosed.2 ratioMinimizingBody_properties.1.2.1.isClosed
      (criticalMidpointSet_subset_frontier hq)
  have htilt (n : ℕ) (x : E) (hx : x ∈ ratioMinimizingBody) :
      ψ x + ε n * χ x ≤ ψ (p n) + ε n * χ (p n) := hmax n x hx
  have hψlim := ψ.continuous_of_finiteDimensional.tendsto q |>.comp ht
  have hχlim := χ.continuous_of_finiteDimensional.tendsto q |>.comp ht
  have helim := hεlim.comp hf.tendsto_atTop
  have hlim : 1 ≤ ψ q := by
    have hh := le_of_tendsto_of_tendsto
      (tendsto_const_nhds.add (helim.mul_const (χ u)))
      (hψlim.add (helim.mul hχlim))
      (Filter.Eventually.of_forall (fun n => htilt (f n) u hu))
    simpa [hψ.1] using hh
  refine ⟨q,hq,le_antisymm (hψ.2 q hqK) hlim,?_⟩
  intro x hx hface
  apply ge_of_tendsto hχlim
  apply Filter.Eventually.of_forall
  intro n
  change χ x ≤ χ (p (f n))
  have hh := htilt (f n) x hx
  have hb := hψ.2 (p (f n)) (hpK (f n))
  have he := hε (f n)
  rw [hface] at hh
  nlinarith

/-- A support face is parametrized by its tangent coordinate at any one
critical midpoint on that face. -/
lemma criticalMidpoint_support_face_decomposition (p : criticalMidpointSet)
    {ψ : E →ₗ[ℝ] ℝ} (hψ : NormalizedSupportAt ratioMinimizingBody p.val ψ)
    {x : E} (hx : ψ x = 1) :
    x = p.val + det2 p.val x • criticalMidpointTangent p := by
  have hg := minimizerGaugeGradient_support (criticalMidpoint_ne_zero p)
  simp only [minimizerRadialFoot, criticalMidpoint_gauge, inv_one, one_smul] at hg
  have hpK := frontier_subset_iff_isClosed.2 ratioMinimizingBody_properties.1.2.1.isClosed
    (criticalMidpointSet_subset_frontier p.property)
  have he := minimizer_normalized_support_unique hpK hg hψ
  have hv := LinearMap.congr_fun he x
  change minimizerGaugeGradient p.val x = ψ x at hv
  simpa only [hv, hx, one_smul] using criticalMidpoint_vector_decomposition p x

/-- Both ends of every supporting face are actual critical midpoints.
The endpoints may coincide when the face is a singleton. -/
theorem minimizer_support_face_segment {u : E} (hu : u ∈ ratioMinimizingBody)
    {ψ : E →ₗ[ℝ] ℝ} (hψ : NormalizedSupportAt ratioMinimizingBody u ψ) :
    ∃ a ∈ criticalMidpointSet, ∃ b ∈ criticalMidpointSet,
      {x ∈ ratioMinimizingBody | ψ x = 1} = segment ℝ a b := by
  obtain ⟨H,hH,harea,i,hi⟩ := minimizer_support_face_midpoint hu hψ
  let p : criticalMidpointSet := ⟨H.midpoint i,critical_hexagon_midpoint_mem_set H hH harea i⟩
  have hpψ : NormalizedSupportAt ratioMinimizingBody p.val ψ := ⟨hi,hψ.2⟩
  let χ := detForm p.val
  obtain ⟨b,hb,hbψ,hmax⟩ := criticalMidpoint_support_face_max hu hψ χ
  obtain ⟨a,ha,haψ,hnegmax⟩ := criticalMidpoint_support_face_max hu hψ (-χ)
  have hmin (x : E) (hx : x ∈ ratioMinimizingBody) (hface : ψ x = 1) : χ a ≤ χ x := by
    have hh := hnegmax x hx hface
    simpa using hh
  have haK := frontier_subset_iff_isClosed.2 ratioMinimizingBody_properties.1.2.1.isClosed
    (criticalMidpointSet_subset_frontier ha)
  have hbK := frontier_subset_iff_isClosed.2 ratioMinimizingBody_properties.1.2.1.isClosed
    (criticalMidpointSet_subset_frontier hb)
  have hdec (x : E) (hx : ψ x = 1) : x = p.val + χ x • criticalMidpointTangent p :=
    criticalMidpoint_support_face_decomposition p hpψ hx
  refine ⟨a,ha,b,hb,?_⟩
  ext x
  constructor
  · rintro ⟨hx,hxψ⟩
    have hscalar : χ x ∈ segment ℝ (χ a) (χ b) :=
      Icc_subset_segment ⟨hmin x hx hxψ,hmax x hx hxψ⟩
    obtain ⟨s,t,hs,ht,hst,he⟩ := hscalar
    change s * χ a + t * χ b = χ x at he
    refine ⟨s,t,hs,ht,hst,?_⟩
    calc
      s • a + t • b = (s+t) • p.val + (s*χ a+t*χ b) • criticalMidpointTangent p := by
        conv_lhs => rw [hdec a haψ,hdec b hbψ]
        module
      _ = x := by rw [hst,he,one_smul,← hdec x hxψ]
  · intro hx
    refine ⟨ratioMinimizingBody_properties.1.1.segment_subset haK hbK hx,?_⟩
    obtain ⟨s,t,hs,ht,hst,rfl⟩ := hx
    simpa [map_add,map_smul,haψ,hbψ] using hst

#print axioms minimizer_support_maximum_at_critical_midpoint
#print axioms minimizer_support_maximum_at_midpoint
#print axioms criticalMidpoint_support_face_max
#print axioms criticalMidpoint_support_face_decomposition
#print axioms minimizer_support_face_segment
end Certificate.Packing
