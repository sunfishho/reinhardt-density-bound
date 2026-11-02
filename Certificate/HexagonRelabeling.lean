import Certificate.HexagonSideVariation

/-! Cyclic and orientation-reversing relabelings preserve the actual hexagon. -/
namespace Certificate.Packing
open Set
namespace Hex

noncomputable def rotate (H : Hex) : Hex where
  φ₁ := H.φ₂
  φ₂ := H.φ₃
  φ₃ := -H.φ₁
  a := H.b
  b := H.c
  c := -H.a
  ha₁ := H.hb₂
  ha₃ := by simp [H.hb₁]
  hb₁ := H.hc₂
  hb₂ := H.hc₃
  hc₂ := by simp [H.ha₃]
  hc₃ := by simp [H.ha₁]
  hin_a := H.hin_b
  hin_b := by simpa using H.hin_c
  hin_c := by simpa using H.hin_a
  hdet := by
    have he : det2 (H.b+H.c) (H.c+-H.a)=det2 H.v H.w := by
      simp [det2,Hex.v,Hex.w]; ring
    rw [he]
    exact H.hdet

lemma rotate_set (H : Hex) : H.rotate.set=H.set := by
  ext x; simp [rotate,Hex.set,and_comm,and_left_comm]

lemma rotate_det (H : Hex) : det2 H.rotate.v H.rotate.w=det2 H.v H.w := by
  simp [rotate,Hex.v,Hex.w,det2]; ring

lemma rotate_strict (H : Hex) (h : H.Strict) : H.rotate.Strict := by
  simpa [Strict,rotate] using And.intro h.2.1 (And.intro h.2.2 h.1)

/-- Reverse the first edge while retaining its midpoint. -/
noncomputable def flip (H : Hex) : Hex := H.reverse.rotate

lemma flip_set (H : Hex) : H.flip.set=H.set := by
  rw [flip,rotate_set,reverse_set]

lemma flip_det (H : Hex) : det2 H.flip.v H.flip.w= -det2 H.v H.w := by
  rw [flip,rotate_det,reverse_det]

lemma flip_strict (H : Hex) (h : H.Strict) : H.flip.Strict := by
  apply rotate_strict
  simpa [Strict,reverse] using And.intro h.2.2 (And.intro h.2.1 h.1)

lemma flip_first (H : Hex) : H.flip.a+H.flip.b=H.a+H.b := by
  change H.b+H.a=H.a+H.b
  exact add_comm _ _

end Hex
end Certificate.Packing
