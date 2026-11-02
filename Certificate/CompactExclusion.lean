import Certificate.ConfinementRho
import Certificate.NumericBound

/-! Elementary exclusion estimates for the published area lower bound.

The geometric area inequality (HV Theorem 5.0.6) is not proved in this file.
Its scalar right-hand side is analyzed here, without numerical interval grids.
Outside the compact domain that right-hand side is at least 269/300, already
strictly above the new certificate bound. This weaker exclusion threshold
suffices for the present result and avoids the smoothed-octagon logarithm. -/
namespace Certificate.Confinement
set_option maxHeartbeats 0

noncomputable def areaTerm (u v w : ℝ) : ℝ :=
  max 0 (v*w - 2*u*Real.sqrt (v*w))

noncomputable def areaScore (u v w : ℝ) : ℝ :=
  3/4 + (areaTerm u v w + areaTerm v u w + areaTerm w u v)/4

theorem areaTerm_nonneg (u v w : ℝ) : 0 ≤ areaTerm u v w := le_max_left _ _

theorem areaScore_swap (u v w : ℝ) : areaScore u v w = areaScore v u w := by
  simp only [areaScore, areaTerm, mul_comm u v]
  ring

theorem areaScore_cycle (u v w : ℝ) : areaScore u v w = areaScore v w u := by
  simp only [areaScore, areaTerm]
  simp only [mul_comm w u, mul_comm v u]
  ring

/-- Two small star coordinates force a large area, even with generous rational slack. -/
theorem areaScore_cusp (u v w : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w)
    (he : u*v + v*w + w*u = 1) (hs : u+v ≤ 13/50) :
    (269:ℝ)/300 ≤ areaScore u v w := by
  have huvw : 0 ≤ u*v := mul_nonneg hu hv
  have huw : 0 ≤ u*w := mul_nonneg hu hw
  have hvw : 0 ≤ v*w := mul_nonneg hv hw
  have hr1 := Real.sq_sqrt huw
  have hr2 := Real.sq_sqrt hvw
  have hn1 := Real.sqrt_nonneg (u*w)
  have hn2 := Real.sqrt_nonneg (v*w)
  have hcross := sq_nonneg (v*Real.sqrt (u*w)-u*Real.sqrt (v*w))
  have hsquare :
      (v*Real.sqrt (u*w)+u*Real.sqrt (v*w))^2 ≤ 2*u*v*w*(u+v) := by
    have hq1 : (v*Real.sqrt (u*w))^2=v^2*(u*w) := by rw [mul_pow,hr1]
    have hq2 : (u*Real.sqrt (v*w))^2=u^2*(v*w) := by rw [mul_pow,hr2]
    nlinarith only [hcross, hq1, hq2]
  have hprod : 4*u*v ≤ (u+v)^2 := by nlinarith only [sq_nonneg (u-v)]
  have hprod2 := mul_nonneg (sub_nonneg.mpr hprod) (show 0 ≤ w*(u+v) by positivity)
  have hprod3 := mul_nonneg huvw (sq_nonneg (u+v))
  have hsquare2 :
      2*(v*Real.sqrt (u*w)+u*Real.sqrt (v*w))^2 ≤ (u+v)^2 := by
    have he2 := congrArg (fun r : ℝ => r*(u+v)^2) he
    nlinarith only [hsquare,hprod2,hprod3,he2]
  have hcross_nonneg : 0 ≤ v*Real.sqrt (u*w)+u*Real.sqrt (v*w) := by positivity
  have hcross_bound : v*Real.sqrt (u*w)+u*Real.sqrt (v*w) ≤ 3/4*(u+v) := by
    nlinarith only [hsquare2,hcross_nonneg,hu,hv,sq_nonneg (u+v)]
  have hsquare_bound : (u+v)^2 ≤ (13/50:ℝ)^2 := by nlinarith only [hs,hu,hv]
  have hterm1 : v*w-2*u*Real.sqrt (v*w) ≤ areaTerm u v w := le_max_right _ _
  have hterm2 : u*w-2*v*Real.sqrt (u*w) ≤ areaTerm v u w := le_max_right _ _
  have hterm3 := areaTerm_nonneg w u v
  unfold areaScore
  nlinarith only [hterm1,hterm2,hterm3,he,hcross_bound,hprod,hsquare_bound,hs]

/-- Away from a cusp, a small least coordinate forces the opposite product above 18/25. -/
theorem opposite_product_lower (u v w : ℝ)
    (hu : 0 ≤ u) (hu1 : u ≤ 1/15) (huv : u ≤ v) (hvw : v ≤ w)
    (hs : (32:ℝ)/125 ≤ u+v) (he : u*v+v*w+w*u=1) :
    (18:ℝ)/25 ≤ v*w := by
  have hv : 0 ≤ v := hu.trans huv
  have hw : 0 ≤ w := hv.trans hvw
  have hsquare : 3*(u+v)^2 ≤ 4 := by
    have h1 := mul_nonneg (sub_nonneg.mpr huv) (show 0 ≤ v+3*u by positivity)
    have h2 := mul_nonneg (show 0 ≤ u+v by positivity) (sub_nonneg.mpr hvw)
    nlinarith only [h1,h2,he]
  have hs1 : u+v ≤ 6/5 := by nlinarith only [hsquare]
  have hsegment := mul_nonneg (sub_nonneg.mpr hs) (sub_nonneg.mpr hs1)
  have hsmall := mul_nonneg (sub_nonneg.mpr hu1) (show 0 ≤ 1+(u+v)^2 by positivity)
  have hsqgap : 0 ≤ u*((u+v)^2-v^2) :=
    mul_nonneg hu (by nlinarith [mul_nonneg hu hv])
  have he_mul : (u+v)*(v*w)=v-u*v^2 := by
    have he1 := congrArg (fun r : ℝ => v*r) he
    nlinarith only [he1]
  have hgap : 0 < (u+v)*(v*w-18/25) := by
    nlinarith only [hsegment,hsmall,hsqgap,he_mul,hs]
  by_contra hn
  have hnonpos := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ u+v by positivity)
    (show v*w-18/25 ≤ 0 by linarith)
  linarith

theorem areaScore_wall (u v w : ℝ)
    (hu : 0 ≤ u) (hu1 : u ≤ 1/15) (huv : u ≤ v) (hvw : v ≤ w)
    (hs : (32:ℝ)/125 ≤ u+v) (he : u*v+v*w+w*u=1) :
    (269:ℝ)/300 ≤ areaScore u v w := by
  have hv : 0 ≤ v := hu.trans huv
  have hw : 0 ≤ w := hv.trans hvw
  have hprod := opposite_product_lower u v w hu hu1 huv hvw hs he
  have hp1 : v*w ≤ 1 := by nlinarith only [he,mul_nonneg hu hv,mul_nonneg hw hu]
  have hroot : Real.sqrt (v*w) ≤ 1 := (Real.sqrt_le_one).2 hp1
  have hroot0 := Real.sqrt_nonneg (v*w)
  have hr := mul_le_mul hu1 hroot hroot0 (by norm_num : (0:ℝ) ≤ 1/15)
  have ht1 : v*w-2*u*Real.sqrt (v*w) ≤ areaTerm u v w := le_max_right _ _
  have ht2 := areaTerm_nonneg v u w
  have ht3 := areaTerm_nonneg w u v
  unfold areaScore
  nlinarith only [hprod,hr,ht1,ht2,ht3]

/-- Ordered form of compactness, with a threshold sufficient for this certificate. -/
theorem ordered_compact_of_areaScore (u v w : ℝ)
    (hu : 0 ≤ u) (huv : u ≤ v) (hvw : v ≤ w)
    (he : u*v+v*w+w*u=1) (ha : areaScore u v w < 269/300) :
    1/15 ≤ u ∧ 4*Real.sqrt 3/27 ≤ u+v := by
  have hv : 0 ≤ v := hu.trans huv
  have hw : 0 ≤ w := hv.trans hvw
  have hc : 13/50 < u+v := by
    by_contra hn
    exact (not_le_of_gt ha) (areaScore_cusp u v w hu hv hw he (le_of_not_gt hn))
  have hlo : 1/15 ≤ u := by
    by_contra hn
    exact (not_le_of_gt ha) (areaScore_wall u v w hu (le_of_not_ge hn) huv hvw
      (by linarith) he)
  have hs3 : Real.sqrt (3:ℝ) ≤ 351/200 := by
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num),Real.sqrt_nonneg (3:ℝ)]
  exact ⟨hlo,by linarith⟩

/-- The symmetric scalar bound implies all six published compact-domain inequalities. -/
theorem compact_of_areaScore (x : State) (hd : x.h^2-x.a^2-x.p^2=1)
    (h0 : 0 ≤ rho0 x) (h1 : 0 ≤ rho1 x) (h2 : 0 ≤ rho2 x)
    (ha : areaScore (rho0 x) (rho1 x) (rho2 x) < 269/300) : HVCompact x := by
  have he := rho_e2 x hd
  have hperm1 : areaScore (rho0 x) (rho2 x) (rho1 x) < 269/300 := by
    rw [areaScore_cycle,← areaScore_swap,← areaScore_cycle]; exact ha
  have hperm2 : areaScore (rho1 x) (rho0 x) (rho2 x) < 269/300 := by
    rw [← areaScore_swap]; exact ha
  have hperm3 : areaScore (rho1 x) (rho2 x) (rho0 x) < 269/300 := by
    rw [← areaScore_cycle]; exact ha
  have hperm4 : areaScore (rho2 x) (rho0 x) (rho1 x) < 269/300 := by
    rw [← areaScore_cycle]; exact hperm3
  have hperm5 : areaScore (rho2 x) (rho1 x) (rho0 x) < 269/300 := by
    rw [← areaScore_swap]; exact hperm3
  unfold HVCompact
  rcases le_total (rho0 x) (rho1 x) with h01 | h10
  · rcases le_total (rho1 x) (rho2 x) with h12 | h21
    · have hh := ordered_compact_of_areaScore _ _ _ h0 h01 h12 he ha
      exact ⟨hh.1,by linarith [hh.1],by linarith [hh.1],hh.2,by linarith [hh.2],by linarith [hh.2]⟩
    · rcases le_total (rho0 x) (rho2 x) with h02 | h20
      · have hh := ordered_compact_of_areaScore _ _ _ h0 h02 h21 (by nlinarith only [he]) hperm1
        exact ⟨hh.1,by linarith [hh.1],by linarith [hh.1],by linarith [hh.2],hh.2,by linarith [hh.2]⟩
      · have hh := ordered_compact_of_areaScore _ _ _ h2 h20 h01 (by nlinarith only [he]) hperm4
        exact ⟨by linarith [hh.1],by linarith [hh.1],hh.1,by linarith [hh.2],by linarith [hh.2],by linarith [hh.2]⟩
  · rcases le_total (rho0 x) (rho2 x) with h02 | h20
    · have hh := ordered_compact_of_areaScore _ _ _ h1 h10 h02 (by nlinarith only [he]) hperm2
      exact ⟨by linarith [hh.1],hh.1,by linarith [hh.1],by linarith [hh.2],by linarith [hh.2],by linarith [hh.2]⟩
    · rcases le_total (rho1 x) (rho2 x) with h12 | h21
      · have hh := ordered_compact_of_areaScore _ _ _ h1 h12 h20 (by nlinarith only [he]) hperm3
        exact ⟨by linarith [hh.1],hh.1,by linarith [hh.1],by linarith [hh.2],by linarith [hh.2],hh.2⟩
      · have hh := ordered_compact_of_areaScore _ _ _ h2 h21 h10 (by nlinarith only [he]) hperm5
        exact ⟨by linarith [hh.1],by linarith [hh.1],hh.1,by linarith [hh.2],by linarith [hh.2],by linarith [hh.2]⟩

theorem certified_density_lt_exclusion_threshold : gamma/(2*Real.sqrt 3) < (269:ℝ)/300 := by
  have hs : 0 < Real.sqrt (3:ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hu : Real.sqrt (3:ℝ) ≤ 17321/10000 := by
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)]
  apply (div_lt_iff₀ (by positivity : 0 < 2*Real.sqrt (3:ℝ))).mpr
  dsimp [gamma]
  nlinarith only [hu]

#print axioms compact_of_areaScore
#print axioms certified_density_lt_exclusion_threshold
end Certificate.Confinement
