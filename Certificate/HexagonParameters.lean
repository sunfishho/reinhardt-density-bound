import Certificate.HexagonCompactness

/-! Closed finite-dimensional parameters for enclosing hexagons. The lattice
nondegeneracy condition follows from the closed incidence and strip constraints;
it does not have to be preserved as an open condition in a limiting argument. -/
namespace Certificate.Packing
open Set MeasureTheory
set_option maxHeartbeats 0

abbrev HexParameters := (Fin 3 → Fin 2 → ℝ) × (Fin 3 → Fin 2 → ℝ)
namespace HexParameters
noncomputable def form (d : HexParameters) (i : Fin 3) : E →ₗ[ℝ] ℝ :=
  d.1 i 0 • coord 0+d.1 i 1 • coord 1
noncomputable def vertex (d : HexParameters) (i : Fin 3) : E := point (d.2 i 0) (d.2 i 1)

def Valid (d : HexParameters) : Prop :=
  d.form 0 (d.vertex 0)=1 ∧ d.form 2 (d.vertex 0)= -1 ∧
  d.form 0 (d.vertex 1)=1 ∧ d.form 1 (d.vertex 1)=1 ∧
  d.form 1 (d.vertex 2)=1 ∧ d.form 2 (d.vertex 2)=1 ∧
  |d.form 1 (d.vertex 0)|≤1 ∧ |d.form 2 (d.vertex 1)|≤1 ∧ |d.form 0 (d.vertex 2)|≤1

def Encloses (K : Set E) (d : HexParameters) : Prop :=
  ∀ x ∈ K, |d.form 0 x|≤1 ∧ |d.form 1 x|≤1 ∧ |d.form 2 x|≤1

lemma valid_det_ne_zero {d : HexParameters} (h : d.Valid) :
    det2 (d.vertex 0+d.vertex 1) (d.vertex 1+d.vertex 2) ≠ 0 := by
  obtain ⟨ha1,ha3,hb1,hb2,hc2,hc3,ha,hb,hc⟩ := h
  let F := HVGeometry.pairLinear (d.form 0+d.form 1) (d.form 2)
  have he : det2 (F (d.vertex 0+d.vertex 1)) (F (d.vertex 1+d.vertex 2)) =
      4+(1-d.form 2 (d.vertex 1))*(1+d.form 0 (d.vertex 2))+
        (1+d.form 2 (d.vertex 1))*(1+d.form 1 (d.vertex 0)) := by
    simp [F,HVGeometry.pairLinear,det2,point,map_add,ha1,ha3,hb1,hb2,hc2,hc3]
    ring
  have hp : 0 < det2 (F (d.vertex 0+d.vertex 1)) (F (d.vertex 1+d.vertex 2)) := by
    rw [he]
    have hsa := abs_le.1 ha
    have hsb := abs_le.1 hb
    have hsc := abs_le.1 hc
    nlinarith [mul_nonneg (show 0≤1-d.form 2 (d.vertex 1) by linarith)
      (show 0≤1+d.form 0 (d.vertex 2) by linarith),
      mul_nonneg (show 0≤1+d.form 2 (d.vertex 1) by linarith)
      (show 0≤1+d.form 1 (d.vertex 0) by linarith)]
  intro hd
  rw [det2_linearMap,hd,mul_zero] at hp
  exact lt_irrefl _ hp

noncomputable def toHex (d : HexParameters) (h : d.Valid) : Hex where
  φ₁ := d.form 0
  φ₂ := d.form 1
  φ₃ := d.form 2
  a := d.vertex 0
  b := d.vertex 1
  c := d.vertex 2
  ha₁ := h.1
  ha₃ := h.2.1
  hb₁ := h.2.2.1
  hb₂ := h.2.2.2.1
  hc₂ := h.2.2.2.2.1
  hc₃ := h.2.2.2.2.2.1
  hin_a := h.2.2.2.2.2.2.1
  hin_b := h.2.2.2.2.2.2.2.1
  hin_c := h.2.2.2.2.2.2.2.2
  hdet := valid_det_ne_zero h

noncomputable def covolume (d : HexParameters) : ℝ :=
  |det2 (d.vertex 0+d.vertex 1) (d.vertex 1+d.vertex 2)|

lemma volume_toHex (d : HexParameters) (h : d.Valid) :
    volume (d.toHex h).set = ENNReal.ofReal d.covolume := (d.toHex h).volume_eq_covolume

lemma continuous_incidence (i j : Fin 3) : Continuous (fun d : HexParameters => d.form i (d.vertex j)) := by
  simp only [form,vertex,LinearMap.add_apply,LinearMap.smul_apply,smul_eq_mul,coord_eval,
    point_zero,point_one]
  fun_prop

lemma isClosed_valid : IsClosed {d : HexParameters | d.Valid} := by
  exact (isClosed_eq (continuous_incidence 0 0) continuous_const).inter
    ((isClosed_eq (continuous_incidence 2 0) continuous_const).inter
    ((isClosed_eq (continuous_incidence 0 1) continuous_const).inter
    ((isClosed_eq (continuous_incidence 1 1) continuous_const).inter
    ((isClosed_eq (continuous_incidence 1 2) continuous_const).inter
    ((isClosed_eq (continuous_incidence 2 2) continuous_const).inter
    ((isClosed_le (continuous_incidence 1 0).abs continuous_const).inter
    ((isClosed_le (continuous_incidence 2 1).abs continuous_const).inter
      (isClosed_le (continuous_incidence 0 2).abs continuous_const))))))))

lemma isClosed_encloses (K : Set E) : IsClosed {d : HexParameters | Encloses K d} := by
  have he : {d : HexParameters | Encloses K d} =
      ⋂ x ∈ K, {d | |d.form 0 x|≤1 ∧ |d.form 1 x|≤1 ∧ |d.form 2 x|≤1} := by
    ext d; simp [Encloses]
  rw [he]
  apply isClosed_iInter; intro x
  apply isClosed_iInter; intro hx
  have hc (i : Fin 3) : Continuous (fun d : HexParameters => d.form i x) := by
    simp only [form,LinearMap.add_apply,LinearMap.smul_apply,smul_eq_mul,coord_eval]
    fun_prop
  exact (isClosed_le (hc 0).abs continuous_const).inter
    ((isClosed_le (hc 1).abs continuous_const).inter (isClosed_le (hc 2).abs continuous_const))

lemma continuous_covolume : Continuous (covolume : HexParameters → ℝ) := by
  unfold covolume det2 vertex
  simp only [PiLp.add_apply,point_zero,point_one]
  fun_prop

noncomputable def ofHex (H : Hex) : HexParameters :=
  (fun i j => (![H.φ₁,H.φ₂,H.φ₃] i) (if j=0 then point 1 0 else point 0 1),
   fun i j => (![H.a,H.b,H.c] i) j)

lemma form_coordinates (φ : E →ₗ[ℝ] ℝ) (x : E) :
    φ (point 1 0)*x 0+φ (point 0 1)*x 1=φ x := by
  have he : x=x 0 • point 1 0+x 1 • point 0 1 := by
    ext i; fin_cases i <;> simp [point]
  conv_rhs => rw [he,map_add,map_smul,map_smul]
  simp only [smul_eq_mul]; ring

lemma form_ofHex (H : Hex) (i : Fin 3) : (ofHex H).form i = ![H.φ₁,H.φ₂,H.φ₃] i := by
  ext x
  fin_cases i
  · exact form_coordinates H.φ₁ x
  · exact form_coordinates H.φ₂ x
  · exact form_coordinates H.φ₃ x

lemma vertex_ofHex (H : Hex) (i : Fin 3) : (ofHex H).vertex i = ![H.a,H.b,H.c] i := by
  ext j; fin_cases i <;> fin_cases j <;> rfl

lemma valid_ofHex (H : Hex) : (ofHex H).Valid := by
  simp only [Valid,form_ofHex,vertex_ofHex,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two]
  exact ⟨H.ha₁,H.ha₃,H.hb₁,H.hb₂,H.hc₂,H.hc₃,H.hin_a,H.hin_b,H.hin_c⟩

lemma encloses_ofHex {H : Hex} {K : Set E} (h : K ⊆ H.set) : Encloses K (ofHex H) := by
  intro x hx
  simpa [form_ofHex,Hex.set] using h hx

lemma covolume_ofHex (H : Hex) : (ofHex H).covolume = |det2 H.v H.w| := by
  simp [covolume,vertex_ofHex,Hex.v,Hex.w]

#print axioms valid_det_ne_zero
#print axioms isClosed_valid
end HexParameters
end Certificate.Packing
