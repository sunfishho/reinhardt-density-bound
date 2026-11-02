import Certificate.PackingDefinitions

/-! Lattice-density comparison, adapted from the recovered Fable $100 run's
`artifacts/app/scratch/lattice/ReinhardtReduction.lean` (namespace LatticeRed).
All adapted proofs are rechecked in this project against its pinned mathlib.
This proves a lower bound for the original ball-limsup packing density; it
requires neither existence of a minimizing disc nor lattice optimality. -/
namespace Certificate.Packing
open MeasureTheory Filter Set Pointwise
set_option maxHeartbeats 0

abbrev E := EuclideanSpace ℝ (Fin 2)

/-- 2×2 determinant of two vectors. -/
noncomputable def det2 (v w : E) : ℝ := v 0 * w 1 - v 1 * w 0

/-- lattice vector with integer coordinates `p` in the basis `v, w`. -/
noncomputable def lat (v w : E) (p : ℤ × ℤ) : E := (p.1 : ℝ) • v + (p.2 : ℝ) • w

/-- The classical lattice form of Reinhardt's conjecture: every symmetric convex disc admits
a lattice `Λ = ℤv + ℤw` such that the translates `K + λ` have disjoint interiors and
`c · det Λ ≤ area K`. -/
def LatticeCore (c : ℝ) : Prop :=
  ∀ K : Set E, IsSymmetricConvexDisc K →
    ∃ v w : E, det2 v w ≠ 0 ∧
      (∀ p : ℤ × ℤ, p ≠ 0 → Disjoint (interior K) (interior (lat v w p +ᵥ K))) ∧
      c * |det2 v w| ≤ (volume K).toReal

/-- enumeration of ℤ² -/
noncomputable def enum : ℕ ≃ ℤ × ℤ := (Denumerable.eqv (ℤ × ℤ)).symm

/-- the packing by lattice translates -/
noncomputable def latPacking (v w : E) (i : ℕ) : E ≃ᵢ E :=
  IsometryEquiv.addLeft (lat v w (enum i))

lemma latPacking_image (v w : E) (K : Set E) (i : ℕ) :
    latPacking v w i '' K = lat v w (enum i) +ᵥ K := by
  rw [← Set.image_vadd]; rfl

lemma lat_sub (v w : E) (p q : ℤ × ℤ) : lat v w p - lat v w q = lat v w (p - q) := by
  simp only [lat, Prod.fst_sub, Prod.snd_sub, Int.cast_sub, sub_smul]; abel

theorem isPacking_lat (K : Set E) (v w : E)
    (h : ∀ p : ℤ × ℤ, p ≠ 0 → Disjoint (interior K) (interior (lat v w p +ᵥ K))) :
    IsPacking K (latPacking v w) := by
  intro i j hij
  rw [latPacking_image, latPacking_image, interior_vadd, interior_vadd]
  have hne : enum j - enum i ≠ 0 := sub_ne_zero.mpr (fun h' => hij (enum.injective h').symm)
  have h1 := h _ hne
  rw [interior_vadd] at h1
  have h2 : Disjoint (lat v w (enum i) +ᵥ interior K)
      (lat v w (enum i) +ᵥ (lat v w (enum j - enum i) +ᵥ interior K)) := by
    rw [← Set.image_vadd, ← Set.image_vadd]
    exact (Set.disjoint_image_iff (add_right_injective _)).2 h1
  rwa [vadd_vadd, ← lat_sub, add_sub_cancel] at h2

/-! ### glue: densities lie in [0,1] -/

noncomputable def ratio (K : Set E) (g : ℕ → E ≃ᵢ E) (r : ℝ) : ℝ :=
  (volume (packedRegion K g ∩ Metric.ball (0 : E) r)).toReal /
    (volume (Metric.ball (0 : E) r)).toReal

lemma ratio_nonneg (K : Set E) (g : ℕ → E ≃ᵢ E) (r : ℝ) : 0 ≤ ratio K g r := by
  unfold ratio; positivity

lemma ratio_le_one (K : Set E) (g : ℕ → E ≃ᵢ E) (r : ℝ) : ratio K g r ≤ 1 := by
  unfold ratio
  apply div_le_one_of_le₀
  · apply ENNReal.toReal_mono
    · exact measure_ball_lt_top.ne
    · exact measure_mono inter_subset_right
  · exact ENNReal.toReal_nonneg

lemma packingDensityOf_eq (K : Set E) (g : ℕ → E ≃ᵢ E) :
    packingDensityOf K g = limsup (ratio K g) atTop := rfl

lemma density_le_one (K : Set E) (g : ℕ → E ≃ᵢ E) : packingDensityOf K g ≤ 1 := by
  rw [packingDensityOf_eq]
  apply Filter.limsup_le_of_le
  · exact isCoboundedUnder_le_of_le atTop (fun r => ratio_nonneg K g r)
  · exact Eventually.of_forall (ratio_le_one K g)

lemma bddAbove_densities (K : Set E) :
    BddAbove {d | ∃ g : ℕ → E ≃ᵢ E, IsPacking K g ∧ d = packingDensityOf K g} :=
  ⟨1, fun _ ⟨g, _, hd⟩ => hd ▸ density_le_one K g⟩

/-! ### The density of a lattice packing -/

/-- fundamental parallelepiped -/
noncomputable def F (v w : E) : Set E := parallelepiped ![v, w]

lemma volume_F (v w : E) : volume (F v w) = ENNReal.ofReal |det2 v w| := by
  have hb := OrthonormalBasis.addHaar_eq_volume (EuclideanSpace.basisFun (Fin 2) ℝ)
  rw [← hb, F, Measure.addHaar_parallelepiped]
  congr 2
  rw [Module.Basis.det_apply, Matrix.det_fin_two]
  simp only [Module.Basis.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
    EuclideanSpace.basisFun_repr, Matrix.cons_val_zero, Matrix.cons_val_one, det2]
  ring

lemma cramer (v w : E) (hd : det2 v w ≠ 0) (x : E) :
    x = (det2 x w / det2 v w) • v + (det2 v x / det2 v w) • w := by
  have key : ∀ xi vi wi : ℝ, xi * det2 v w = det2 x w * vi + det2 v x * wi →
      xi = det2 x w / det2 v w * vi + det2 v x / det2 v w * wi := by
    intro xi vi wi hxi
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, eq_div_iff hd]
    exact hxi
  ext i
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  apply key
  fin_cases i <;> simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, det2] <;> ring

lemma lat_eq (v w : E) (p : ℤ × ℤ) : lat v w p = (p.1 : ℝ) • v + (p.2 : ℝ) • w := rfl

lemma norm_lat_le_of_mem_F (v w : E) {f : E} (hf : f ∈ F v w) : ‖f‖ ≤ ‖v‖ + ‖w‖ := by
  obtain ⟨t, ht, rfl⟩ := hf
  rw [Set.mem_Icc] at ht
  have h0 : ∀ i, 0 ≤ t i := fun i => ht.1 i
  have h1 : ∀ i, t i ≤ 1 := fun i => ht.2 i
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  calc ‖t 0 • v + t 1 • w‖ ≤ ‖t 0 • v‖ + ‖t 1 • w‖ := norm_add_le _ _
    _ = |t 0| * ‖v‖ + |t 1| * ‖w‖ := by rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ 1 * ‖v‖ + 1 * ‖w‖ := by
        gcongr
        · rw [abs_le]; constructor <;> linarith [h0 0, h1 0]
        · rw [abs_le]; constructor <;> linarith [h0 1, h1 1]
    _ = ‖v‖ + ‖w‖ := by ring

/-- the set of lattice indices with `‖lat p‖ ≤ ρ` -/
def S (v w : E) (ρ : ℝ) : Type := {p : ℤ × ℤ // ‖lat v w p‖ ≤ ρ}

instance (v w : E) (ρ : ℝ) : Countable (S v w ρ) := by unfold S; infer_instance

lemma cover (v w : E) (hd : det2 v w ≠ 0) (ρ : ℝ) :
    Metric.ball (0 : E) (ρ - (‖v‖ + ‖w‖)) ⊆ ⋃ p : S v w ρ, (lat v w p.1 +ᵥ F v w) := by
  intro x hx
  rw [Metric.mem_ball, dist_zero_right] at hx
  set s := det2 x w / det2 v w with hs
  set t := det2 v x / det2 v w with ht
  have hx' : x = s • v + t • w := cramer v w hd x
  let p : ℤ × ℤ := (⌊s⌋, ⌊t⌋)
  have hf : x - lat v w p ∈ F v w := by
    refine ⟨![s - ⌊s⌋, t - ⌊t⌋], ?_, ?_⟩
    · rw [Set.mem_Icc]
      constructor
      · intro i; fin_cases i <;> simp
      · intro i; fin_cases i <;> simp <;>
          linarith [Int.lt_floor_add_one s, Int.lt_floor_add_one t, Int.fract_lt_one s, Int.fract_lt_one t]
    · simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, lat_eq]
      rw [hx']
      simp only [p, sub_smul]
      abel
  have hnorm : ‖x - lat v w p‖ ≤ ‖v‖ + ‖w‖ := norm_lat_le_of_mem_F v w hf
  have hp : ‖lat v w p‖ ≤ ρ := by
    calc ‖lat v w p‖ = ‖x - (x - lat v w p)‖ := by rw [sub_sub_cancel]
      _ ≤ ‖x‖ + ‖x - lat v w p‖ := norm_sub_le _ _
      _ ≤ ρ := by linarith
  refine Set.mem_iUnion.2 ⟨⟨p, hp⟩, Set.mem_vadd_set.2 ⟨x - lat v w p, hf, ?_⟩⟩
  simp

lemma count_lower (v w : E) (hd : det2 v w ≠ 0) (ρ : ℝ) :
    volume (Metric.ball (0 : E) (ρ - (‖v‖ + ‖w‖))) ≤
      (∑' _ : S v w ρ, (1 : ENNReal)) * ENNReal.ofReal |det2 v w| := by
  calc volume (Metric.ball (0 : E) (ρ - (‖v‖ + ‖w‖)))
      ≤ volume (⋃ p : S v w ρ, (lat v w p.1 +ᵥ F v w)) := measure_mono (cover v w hd ρ)
    _ ≤ ∑' p : S v w ρ, volume (lat v w p.1 +ᵥ F v w) := measure_iUnion_le _
    _ = ∑' _ : S v w ρ, (1 : ENNReal) * ENNReal.ofReal |det2 v w| := by
        congr 1; ext p; rw [measure_vadd, volume_F, one_mul]
    _ = _ := ENNReal.tsum_mul_right

lemma disjoint_lat (K : Set E) (v w : E)
    (h : ∀ p : ℤ × ℤ, p ≠ 0 → Disjoint (interior K) (interior (lat v w p +ᵥ K)))
    {p q : ℤ × ℤ} (hpq : p ≠ q) :
    Disjoint (interior (lat v w p +ᵥ K)) (interior (lat v w q +ᵥ K)) := by
  rw [interior_vadd, interior_vadd]
  have hne : q - p ≠ 0 := sub_ne_zero.mpr (Ne.symm hpq)
  have h1 := h _ hne
  rw [interior_vadd] at h1
  have h2 : Disjoint (lat v w p +ᵥ interior K)
      (lat v w p +ᵥ (lat v w (q - p) +ᵥ interior K)) := by
    rw [← Set.image_vadd, ← Set.image_vadd]
    exact (Set.disjoint_image_iff (add_right_injective _)).2 h1
  rwa [vadd_vadd, ← lat_sub, add_sub_cancel] at h2

lemma volume_interior_eq (K : Set E) (hK : IsSymmetricConvexDisc K) :
    volume (interior K) = volume K := by
  apply le_antisymm (measure_mono interior_subset)
  calc volume K ≤ volume (interior K ∪ frontier K) := by
        apply measure_mono
        rw [← closure_eq_interior_union_frontier]
        exact subset_closure
    _ ≤ volume (interior K) + volume (frontier K) := measure_union_le _ _
    _ = volume (interior K) := by rw [Convex.addHaar_frontier volume hK.1, add_zero]

lemma packed_lower (K : Set E) (hK : IsSymmetricConvexDisc K) (v w : E)
    (h : ∀ p : ℤ × ℤ, p ≠ 0 → Disjoint (interior K) (interior (lat v w p +ᵥ K)))
    (R : ℝ) (hKR : K ⊆ Metric.ball 0 R) (r : ℝ) :
    (∑' _ : S v w (r - R), (1 : ENNReal)) * volume K ≤
      volume (packedRegion K (latPacking v w) ∩ Metric.ball 0 r) := by
  calc (∑' _ : S v w (r - R), (1 : ENNReal)) * volume K
      = ∑' p : S v w (r - R), volume (interior (lat v w p.1 +ᵥ K)) := by
        rw [← ENNReal.tsum_mul_right]
        congr 1; ext p
        rw [one_mul, interior_vadd, measure_vadd, volume_interior_eq K hK]
    _ = volume (⋃ p : S v w (r - R), interior (lat v w p.1 +ᵥ K)) := by
        refine (measure_iUnion ?_ ?_).symm
        · intro p q hpq
          exact disjoint_lat K v w h (fun e => hpq (Subtype.ext e))
        · intro p; exact isOpen_interior.measurableSet
    _ ≤ volume (packedRegion K (latPacking v w) ∩ Metric.ball 0 r) := by
        apply measure_mono
        intro x hx
        obtain ⟨p, hp⟩ := Set.mem_iUnion.1 hx
        have hx' : x ∈ lat v w p.1 +ᵥ K := interior_subset hp
        obtain ⟨k, hk, rfl⟩ := Set.mem_vadd_set.1 hx'
        constructor
        · refine Set.mem_iUnion.2 ⟨enum.symm p.1, ?_⟩
          rw [latPacking_image, Equiv.apply_symm_apply]
          exact hx'
        · rw [Metric.mem_ball, dist_zero_right, vadd_eq_add]
          have hk' : ‖k‖ < R := by
            have := hKR hk; rwa [Metric.mem_ball, dist_zero_right] at this
          calc ‖lat v w p.1 + k‖ ≤ ‖lat v w p.1‖ + ‖k‖ := norm_add_le _ _
            _ < (r - R) + R := by linarith [p.2]
            _ = r := by ring

/-- The unit-ball constant cancels in the density limit; computing pi is unnecessary. -/
noncomputable def unitBallArea : ℝ := (volume (Metric.ball (0 : E) 1)).toReal

lemma unitBallArea_pos : 0 < unitBallArea :=
  ENNReal.toReal_pos (ne_of_gt (Metric.measure_ball_pos volume (0 : E) (by norm_num)))
    measure_ball_lt_top.ne

lemma volume_ball_toReal (ρ : ℝ) (hρ : 0 ≤ ρ) :
    (volume (Metric.ball (0 : E) ρ)).toReal = ρ ^ 2 * unitBallArea := by
  rw [Measure.addHaar_ball volume (0 : E) hρ, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity)]
  simp [unitBallArea, E]

theorem density_lat (K : Set E) (hK : IsSymmetricConvexDisc K) (v w : E) (hd : det2 v w ≠ 0)
    (h : ∀ p : ℤ × ℤ, p ≠ 0 → Disjoint (interior K) (interior (lat v w p +ᵥ K))) :
    (volume K).toReal / |det2 v w| ≤ packingDensityOf K (latPacking v w) := by
  obtain ⟨R, hR0, hKR⟩ := hK.2.1.isBounded.subset_ball_lt 0 0
  set dF := ‖v‖ + ‖w‖ with hdF
  set C := R + dF with hC
  set D := (volume K).toReal / |det2 v w| with hD
  have hdet_pos : 0 < |det2 v w| := abs_pos.mpr hd
  have hunit := unitBallArea_pos
  -- key pointwise bound
  have key : ∀ r : ℝ, C < r → D * ((r - C) / r) ^ 2 ≤ ratio K (latPacking v w) r := by
    intro r hr
    have hr0 : 0 < r := by linarith [norm_nonneg v, norm_nonneg w]
    have hrC : 0 ≤ r - C := by linarith
    have hB := count_lower v w hd (r - R)
    have hP := packed_lower K hK v w h R hKR r
    have hfin : volume (packedRegion K (latPacking v w) ∩ Metric.ball 0 r) ≠ ⊤ :=
      (measure_mono inter_subset_right).trans_lt measure_ball_lt_top |>.ne
    have hρ : r - R - (‖v‖ + ‖w‖) = r - C := by rw [hC, hdF]; ring
    rw [hρ] at hB
    have hdiv : volume (Metric.ball (0 : E) (r - C)) / ENNReal.ofReal |det2 v w| ≤
        ∑' _ : S v w (r - R), (1 : ENNReal) := by
      rw [ENNReal.div_le_iff_le_mul (Or.inl (by simpa using hdet_pos.ne')) (Or.inl ENNReal.ofReal_ne_top)]
      exact hB
    have h3 : volume (Metric.ball (0 : E) (r - C)) / ENNReal.ofReal |det2 v w| * volume K ≤
        volume (packedRegion K (latPacking v w) ∩ Metric.ball 0 r) :=
      (mul_le_mul' hdiv le_rfl).trans hP
    have h4 := ENNReal.toReal_mono hfin h3
    rw [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_ofReal hdet_pos.le,
      volume_ball_toReal _ hrC] at h4
    unfold ratio
    rw [volume_ball_toReal _ hr0.le, le_div_iff₀ (by positivity)]
    calc D * ((r - C) / r) ^ 2 * (r ^ 2 * unitBallArea)
        = (r - C) ^ 2 * unitBallArea / |det2 v w| * (volume K).toReal := by
          rw [hD]; field_simp
      _ ≤ _ := h4
  -- the lower bound tends to D
  have hlim : Tendsto (fun r : ℝ => D * ((r - C) / r) ^ 2) atTop (nhds D) := by
    have h1 : Tendsto (fun r : ℝ => (r - C) / r) atTop (nhds 1) := by
      have h2 : Tendsto (fun r : ℝ => 1 - C / r) atTop (nhds (1 - 0)) :=
        tendsto_const_nhds.sub (tendsto_const_nhds.div_atTop tendsto_id)
      rw [sub_zero] at h2
      refine h2.congr' ?_
      filter_upwards [eventually_ne_atTop (0 : ℝ)] with r hr
      rw [sub_div, div_self hr]
    have := (h1.pow 2).const_mul D
    simpa using this
  rw [packingDensityOf_eq]
  apply le_of_forall_lt_imp_le_of_dense
  intro b hb
  apply Filter.le_limsup_of_frequently_le _
    (isBoundedUnder_of_eventually_le (Eventually.of_forall (ratio_le_one _ _)))
  apply Eventually.frequently
  have h1 : ∀ᶠ r in atTop, b < D * ((r - C) / r) ^ 2 :=
    hlim.eventually (lt_mem_nhds (by linarith))
  filter_upwards [h1, eventually_gt_atTop C] with r h1 h2
  exact h1.le.trans (key r h2)

/-- A concrete lattice packing gives a lower bound on unrestricted packing density. -/
theorem packingDensity_ge_lattice (K : Set E) (hK : IsSymmetricConvexDisc K)
    (v w : E) (hd : det2 v w ≠ 0)
    (h : ∀ p : ℤ × ℤ, p ≠ 0 → Disjoint (interior K) (interior (lat v w p +ᵥ K))) :
    (volume K).toReal / |det2 v w| ≤ packingDensity K :=
  (density_lat K hK v w hd h).trans
    (le_csSup (bddAbove_densities K) ⟨_, isPacking_lat K v w h, rfl⟩)

#print axioms packingDensity_ge_lattice
end Certificate.Packing
