import Certificate.FrameTrajectory
import Certificate.StateLinearFrame

/-! The actual second derivative of a frame arc, and its signed curvature. -/
namespace Certificate.Packing
open Confinement Curvature
set_option maxHeartbeats 0

noncomputable def tangentRate (da dp dh : ℝ) (v : E) : E :=
  point (da*v 0+(dp-dh)*v 1) ((dp+dh)*v 0-da*v 1)

theorem stateTangent_hasDerivAt {x : ℝ → State} {t da dp dh : ℝ}
    (ha : HasDerivAt (fun s => (x s).a) da t)
    (hp : HasDerivAt (fun s => (x s).p) dp t)
    (hh : HasDerivAt (fun s => (x s).h) dh t) (v : E) :
    HasDerivAt (fun s => stateTangent (x s) v) (tangentRate da dp dh v) t := by
  have hd := (((ha.mul_const (v 0)).add ((hp.sub hh).mul_const (v 1))).smul_const
    (point 1 0)).add
    ((((hp.add hh).mul_const (v 0)).sub (ha.mul_const (v 1))).smul_const (point 0 1))
  convert! hd using 1
  · ext s i; fin_cases i <;> simp [stateTangent,point]
  · ext i; fin_cases i <;> simp [tangentRate,point]

theorem stateAction_variable_hasDerivAt {x : ℝ → State} {v : ℝ → E} {v' : E} {t : ℝ}
    (hg : GroupDerivative x t) (hv : HasDerivAt v v' t) :
    HasDerivAt (fun s => stateAction (x s) (v s))
      (stateAction (x t) (stateTangent (x t) (v t)+v')) t := by
  have h0 : HasDerivAt (fun s => v s 0) (v' 0) t := by
    convert! (coord 0).toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t hv using 1
  have h1 : HasDerivAt (fun s => v s 1) (v' 1) t := by
    convert! (coord 1).toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t hv using 1
  have hd := (((hg.g11.mul h0).add (hg.g12.mul h1)).smul_const (point 1 0)).add
    (((hg.g21.mul h0).add (hg.g22.mul h1)).smul_const (point 0 1))
  convert! hd using 1
  · ext s i; fin_cases i <;> simp [stateAction,point]
  · ext i; fin_cases i <;> simp [stateAction,stateTangent,point] <;> ring

lemma stateTangent_square (x : State) (hd : x.h^2-x.a^2-x.p^2=1) (v : E) :
    stateTangent x (stateTangent x v) = -v := by
  ext i
  fin_cases i <;> simp [stateTangent,point]
  · nlinarith only [congrArg (fun z : ℝ => z * v 0) hd]
  · nlinarith only [congrArg (fun z : ℝ => z * v 1) hd]

noncomputable def stateAcceleration (x : State) (da dp dh : ℝ) (v : E) : E :=
  stateAction x (tangentRate da dp dh v-v)

theorem frame_velocity_hasDerivAt {x : ℝ → State} {t da dp dh : ℝ}
    (hg : GroupDerivative x t) (hdet : (x t).h^2-(x t).a^2-(x t).p^2=1)
    (ha : HasDerivAt (fun s => (x s).a) da t)
    (hp : HasDerivAt (fun s => (x s).p) dp t)
    (hh : HasDerivAt (fun s => (x s).h) dh t) (v : E) :
    HasDerivAt (fun s => stateAction (x s) (stateTangent (x s) v))
      (stateAcceleration (x t) da dp dh v) t := by
  have hd := stateAction_variable_hasDerivAt hg (stateTangent_hasDerivAt ha hp hh v)
  simpa only [stateTangent_square _ hdet,neg_add_eq_sub,stateAcceleration] using hd

theorem frame_signed_curvature (x : State) (da dp dh : ℝ)
    (hg : x.g11*x.g22-x.g12*x.g21=1) (k : Fin 3) :
    det2 (stateAction x (stateTangent x (WithLp.toLp 2 (direction k))))
      (stateAcceleration x da dp dh (WithLp.toLp 2 (direction k))) =
    detPair (x.X.mulVec (direction k)) ((tangent da dp dh-1).mulVec (direction k)) := by
  rw [stateAcceleration,det2_stateAction,hg,one_mul]
  simp [det2,stateTangent,tangentRate,point,detPair,State.X,tangent,
    Matrix.mulVec,dotProduct,Fin.sum_univ_two]
  ring

#print axioms frame_velocity_hasDerivAt
#print axioms frame_signed_curvature
end Certificate.Packing
