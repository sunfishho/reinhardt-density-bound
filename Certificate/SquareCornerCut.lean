import Certificate.CriticalHexagonAttainment
import Certificate.NormalizedMinimizer

/-! Cutting a missing pair of opposite square corners produces a strictly
smaller enclosing hexagon. No optimization routine is part of the proof. -/
namespace Certificate.Packing
open Set MeasureTheory
set_option maxHeartbeats 0

noncomputable def cutSquareHex (d : ℝ) (hd : 1 < d) (hd2 : d < 2) : Hex where
  φ₁ := coord 0
  φ₂ := (1/d) • (coord 0+coord 1)
  φ₃ := coord 1
  a := point 1 (-1)
  b := point 1 (d-1)
  c := point (d-1) 1
  ha₁ := by simp [point]
  ha₃ := by simp [point]
  hb₁ := by simp [point]
  hb₂ := by simp [point]; field_simp; ring
  hc₂ := by simp [point]; field_simp; ring
  hc₃ := by simp [point]
  hin_a := by norm_num [point]
  hin_b := by simp only [coord_eval,point_one]; rw [abs_le]; constructor <;> linarith
  hin_c := by simp only [coord_eval,point_zero]; rw [abs_le]; constructor <;> linarith
  hdet := by
    have he : det2 (point 1 (-1)+point 1 (d-1)) (point 1 (d-1)+point (d-1) 1)=d*(4-d) := by
      simp [det2,point]; ring
    rw [he]
    exact (mul_pos (by linarith) (by linarith)).ne'

lemma cutSquareHex_volume_lt (d : ℝ) (hd : 1 < d) (hd2 : d < 2) :
    volume (cutSquareHex d hd hd2).set < 4 := by
  rw [Hex.volume_eq_covolume]
  have he : det2 (cutSquareHex d hd hd2).v (cutSquareHex d hd hd2).w=d*(4-d) := by
    simp [cutSquareHex,Hex.v,Hex.w,det2,point]; ring
  have hp : 0 < d*(4-d) := mul_pos (by linarith) (by linarith)
  have hlt : d*(4-d) < 4 := by nlinarith [sq_pos_of_pos (show 0 < 2-d by linarith)]
  rw [he,abs_of_pos hp]
  exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hp.le).2 hlt |>.trans_eq (by norm_num)

lemma criticalHexArea_lt_four_of_missing_corner {K : Set E} (hK : IsSymmetricConvexDisc K)
    (hsub : K ⊆ square) (hcorner : point 1 1 ∉ K) : criticalHexArea K < 4 := by
  obtain ⟨z,hz,hmax⟩ := hK.2.1.exists_isMaxOn
    (hK.2.2.1.mono interior_subset) (show ContinuousOn (fun x : E => x 0+x 1) K from by fun_prop)
  have hzbd := hsub hz
  change |z 0| ≤ 1 ∧ |z 1| ≤ 1 at hzbd
  have h0 := abs_le.1 hzbd.1
  have h1 := abs_le.1 hzbd.2
  have hzlt : z 0+z 1 < 2 := by
    by_contra h
    have he : z=point 1 1 := by
      ext i; fin_cases i <;> simp [point] <;> linarith
    exact hcorner (he ▸ hz)
  let d := (max (z 0+z 1) 1+2)/2
  have hmaxlt : max (z 0+z 1) 1 < 2 := max_lt hzlt (by norm_num)
  have hd : 1 < d := by dsimp [d]; linarith [le_max_right (z 0+z 1) 1]
  have hd2 : d < 2 := by dsimp [d]; linarith
  have hzd : z 0+z 1 ≤ d := by dsimp [d]; linarith [le_max_left (z 0+z 1) 1]
  have hs : K ⊆ (cutSquareHex d hd hd2).set := by
    intro x hx
    have hxb := hsub hx
    change |x 0| ≤ 1 ∧ |x 1| ≤ 1 at hxb
    refine ⟨hxb.1,?_,hxb.2⟩
    have hp := (hmax hx).trans hzd
    have hn := (hmax ((hK.2.2.2 x).1 hx)).trans hzd
    change -x 0 + -x 1 ≤ d at hn
    change |(1/d)*(x 0+x 1)| ≤ 1
    rw [one_div_mul_eq_div,abs_div,abs_of_pos (by linarith : 0 < d),div_le_one (by linarith : 0 < d)]
    exact abs_le.2 ⟨by linarith,hp⟩
  exact (criticalHexArea_le _ hs).trans_lt (cutSquareHex_volume_lt d hd hd2)

lemma square_subset_of_corners {K : Set E} (hK : Convex ℝ K) (hs : IsSymmetricSet K)
    (hq : point 1 1 ∈ K) (hp : point 1 (-1) ∈ K) : square ⊆ K := by
  have hnq : point (-1) (-1) ∈ K := by
    have he : -(point 1 1)=point (-1) (-1) := by ext i; fin_cases i <;> norm_num [point]
    simpa only [he] using (hs _).1 hq
  have hnp : point (-1) 1 ∈ K := by
    have he : -(point 1 (-1))=point (-1) 1 := by ext i; fin_cases i <;> norm_num [point]
    simpa only [he] using (hs _).1 hp
  intro x hx
  change |x 0| ≤ 1 ∧ |x 1| ≤ 1 at hx
  obtain ⟨hx0,hx1⟩ := abs_le.1 hx.1
  obtain ⟨hy0,hy1⟩ := abs_le.1 hx.2
  have hr : point 1 (x 1) ∈ K := by
    have hh := hK hq hp (a:=(1+x 1)/2) (b:=(1-x 1)/2)
      (by linarith) (by linarith) (by ring)
    convert hh using 1 <;> ext i <;> fin_cases i <;> simp [point] <;> ring
  have hl : point (-1) (x 1) ∈ K := by
    have hh := hK hnp hnq (a:=(1+x 1)/2) (b:=(1-x 1)/2)
      (by linarith) (by linarith) (by ring)
    convert hh using 1 <;> ext i <;> fin_cases i <;> simp [point] <;> ring
  have hh := hK hr hl (a:=(1+x 0)/2) (b:=(1-x 0)/2)
    (by linarith) (by linarith) (by ring)
  convert hh using 1 <;> ext i <;> fin_cases i <;> simp [point] <;> ring

noncomputable def reflectSquare : E ≃ₗ[ℝ] E :=
  pairFrame (point 1 0) (point 0 (-1)) (by norm_num [det2,point])

lemma reflectSquare_apply (x : E) : reflectSquare x=point (x 0) (-x 1) := by
  ext i; fin_cases i <;> simp [reflectSquare,point]

lemma reflectSquare_abs_det : |LinearMap.det (reflectSquare : E →ₗ[ℝ] E)|=1 := by
  change |LinearMap.det (pairFrameLinear (point 1 0) (point 0 (-1)))|=1
  rw [pairFrameLinear_det]; norm_num [det2,point]

theorem criticalHexArea_lt_four_of_proper_square {K : Set E} (hK : IsSymmetricConvexDisc K)
    (hsub : K ⊂ square) : criticalHexArea K < 4 := by
  by_cases hq : point 1 1 ∈ K
  · have hp : point 1 (-1) ∉ K := fun hp => hsub.2 (square_subset_of_corners hK.1 hK.2.2.2 hq hp)
    have hs : reflectSquare '' K ⊆ square := by
      rintro x ⟨y,hy,rfl⟩
      simpa [reflectSquare_apply,square,point] using hsub.1 hy
    have hc : point 1 1 ∉ reflectSquare '' K := by
      rintro ⟨x,hx,he⟩
      have hx0 := congrArg (fun z : E => z 0) he
      have hx1 := congrArg (fun z : E => z 1) he
      simp [reflectSquare_apply,point] at hx0 hx1
      have hh : x=point 1 (-1) := by
        ext i; fin_cases i <;> simp [point,hx0] <;> linarith
      exact hp (hh ▸ hx)
    have hh := criticalHexArea_lt_four_of_missing_corner
      (symmetricConvexDisc_linear_image hK reflectSquare) hs hc
    rwa [criticalHexArea_linear_image,reflectSquare_abs_det,ENNReal.ofReal_one,one_mul] at hh
  · exact criticalHexArea_lt_four_of_missing_corner hK hsub.1 hq

#print axioms criticalHexArea_lt_four_of_proper_square
end Certificate.Packing
