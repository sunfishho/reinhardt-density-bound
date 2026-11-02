import Certificate.PackingHexagon
import Certificate.GeometricCoordinates

/-! Determinant and density normalization from actual hexagon side midpoints.
The packing construction is independent of minimizer existence and optimality. -/
namespace Certificate.Packing
open MeasureTheory Set
set_option maxHeartbeats 0

noncomputable def stateAction (x : State) (v : E) : E :=
  WithLp.toLp 2 ![x.g11*v 0+x.g12*v 1,x.g21*v 0+x.g22*v 1]

theorem det2_stateAction (x : State) (v w : E) :
    det2 (stateAction x v) (stateAction x w) =
      (x.g11*x.g22-x.g12*x.g21)*det2 v w := by
  dsimp [det2,stateAction]
  ring

noncomputable def circlePoint0 : E := WithLp.toLp 2 ![1,0]
noncomputable def circlePoint1 : E := WithLp.toLp 2 ![1/2,Real.sqrt 3/2]

/-- Two consecutive midpoint positions determine the hexagon's packing lattice.
The remaining vertices and supporting lines need not form a regular hexagon. -/
theorem Hex.det_of_midpoints (H : Hex) (x : State)
    (hd : x.g11*x.g22-x.g12*x.g21=1)
    (h0 : (1/2:ℝ) • (H.a+H.b)=stateAction x circlePoint0)
    (h1 : (1/2:ℝ) • (H.b+H.c)=stateAction x circlePoint1) :
    |det2 H.v H.w|=2*Real.sqrt 3 := by
  have hm := det2_stateAction x circlePoint0 circlePoint1
  rw [← h0,← h1,hd] at hm
  have he : det2 H.v H.w=2*Real.sqrt 3 := by
    dsimp [det2,circlePoint0,circlePoint1] at hm
    dsimp [det2,Hex.v,Hex.w]
    linarith only [hm]
  rw [he,abs_of_nonneg (by positivity)]

theorem packingDensity_ge_normalized_area (K : Set E) (hK : IsSymmetricConvexDisc K)
    (H : Hex) (hKH : K ⊆ H.set) (x : State)
    (hd : x.g11*x.g22-x.g12*x.g21=1)
    (h0 : (1/2:ℝ) • (H.a+H.b)=stateAction x circlePoint0)
    (h1 : (1/2:ℝ) • (H.b+H.c)=stateAction x circlePoint1) :
    (volume K).toReal/(2*Real.sqrt 3) ≤ packingDensity K := by
  have hh := packingDensity_ge_hexagon K hK H hKH
  rwa [H.det_of_midpoints x hd h0 h1] at hh

#print axioms Hex.det_of_midpoints
#print axioms packingDensity_ge_normalized_area
end Certificate.Packing
