import Mathlib

noncomputable section

namespace ProofGraderGenerated

abbrev Point3 := ℝ × ℝ × ℝ
abbrev Point2 := ℝ × ℝ

def diff {α : Type} (_ : α) : ℝ := 0
def DefInt (_ _ : ℝ) (_ : ℝ) : ℝ := 0
def VectorSurfaceInt (_ : Set Point3) (_ : ℝ) : ℝ := 0
def ScalarSurfaceInt (_ : Set Point3) (_ : ℝ) : ℝ := 0
def VectorCurveInt (_ : Set Point3) (_ : ℝ) : ℝ := 0
def VolumeInt (_ : Set Point2) (_ : ℝ) : ℝ := 0
def ScalarSurfaceInt2 (_ : Set Point2) (_ : ℝ) : ℝ := 0
def SurfaceElem (_ : Set Point3) : ℝ := 0
def CurveOn (_ : ℝ → Point3) (_ : Set Point3) : Prop := True
def ContinuousOnInterval (_ : ℝ → ℝ) (_ _ : ℝ) : Prop := True

def frac (x y : ℝ) : ℝ := x / y
def sqrtn (_ : ℕ) (x : ℝ) : ℝ := Real.sqrt x


/- exercise_4363, gaps 1-17. Outward surface integral over rectangular box with f,g,h continuous on coordinate intervals. -/
variable (f g hfun : ℝ → ℝ) (S : Set Point3) (a b c I Ix Iy Iz : ℝ)

def boxSetup4363 : Prop := 0 < a ∧ 0 < b ∧ 0 < c ∧ ContinuousOnInterval f 0 a ∧ ContinuousOnInterval g 0 b ∧ ContinuousOnInterval hfun 0 c ∧ S = {p : Point3 | 0 ≤ p.1 ∧ p.1 ≤ a ∧ 0 ≤ p.2.1 ∧ p.2.1 ≤ b ∧ 0 ≤ p.2.2 ∧ p.2.2 ≤ c}
def total4363 : Prop := I = VectorSurfaceInt S 0
def zpart4363 : Prop := Iz = VectorSurfaceInt S 0
def zsplit4363 : Prop := Iz = DefInt 0 a (diff a) * DefInt 0 b (hfun c * diff b) - DefInt 0 a (diff a) * DefInt 0 b (hfun 0 * diff b)
def zeval4363 : Prop := DefInt 0 a (diff a) * DefInt 0 b (hfun c * diff b) - DefInt 0 a (diff a) * DefInt 0 b (hfun 0 * diff b) = a*b*(hfun c - hfun 0)
def zscale4363 : Prop := a*b*(hfun c - hfun 0) = a*b*c*frac (hfun c - hfun 0) c
def xpart4363 : Prop := Ix = VectorSurfaceInt S 0
def xeval4363 : Prop := VectorSurfaceInt S 0 = b*c*(f a - f 0)
def xscale4363 : Prop := b*c*(f a - f 0) = a*b*c*frac (f a - f 0) a
def ypart4363 : Prop := Iy = VectorSurfaceInt S 0
def yeval4363 : Prop := VectorSurfaceInt S 0 = a*c*(g b - g 0)
def yscale4363 : Prop := a*c*(g b - g 0) = a*b*c*frac (g b - g 0) b
def decomp4363 : Prop := I = Ix + Iy + Iz

theorem proof_gap_exercise_4363_1 (hs : boxSetup4363 f g hfun S a b c) : total4363 S I := by sorry
theorem proof_gap_exercise_4363_2 (hs : boxSetup4363 f g hfun S a b c) (h1 : total4363 S I) : zpart4363 S Iz := by sorry
theorem proof_gap_exercise_4363_3 (hs : boxSetup4363 f g hfun S a b c) (h2 : zpart4363 S Iz) : zsplit4363 hfun a b c Iz := by sorry
theorem proof_gap_exercise_4363_4 (h3 : zsplit4363 hfun a b c Iz) : zeval4363 hfun a b c := by sorry
theorem proof_gap_exercise_4363_5 (hs : boxSetup4363 f g hfun S a b c) (h4 : zeval4363 hfun a b c) : zscale4363 hfun a b c := by sorry
theorem proof_gap_exercise_4363_6 (h3 : zsplit4363 hfun a b c Iz) (h4 : zeval4363 hfun a b c) (h5 : zscale4363 hfun a b c) : Iz = a*b*c*frac (hfun c - hfun 0) c := by sorry
theorem proof_gap_exercise_4363_7 (hs : boxSetup4363 f g hfun S a b c) : xpart4363 S Ix := by sorry
theorem proof_gap_exercise_4363_8 (hs : boxSetup4363 f g hfun S a b c) (h7 : xpart4363 S Ix) : xeval4363 f S b c a := by sorry
theorem proof_gap_exercise_4363_9 (hs : boxSetup4363 f g hfun S a b c) (h8 : xeval4363 f S b c a) : xscale4363 f a b c := by sorry
theorem proof_gap_exercise_4363_10 (h7 : xpart4363 S Ix) (h8 : xeval4363 f S b c a) (h9 : xscale4363 f a b c) : Ix = a*b*c*frac (f a - f 0) a := by sorry
theorem proof_gap_exercise_4363_11 (hs : boxSetup4363 f g hfun S a b c) : ypart4363 S Iy := by sorry
theorem proof_gap_exercise_4363_12 (hs : boxSetup4363 f g hfun S a b c) (h11 : ypart4363 S Iy) : yeval4363 g S a c b := by sorry
theorem proof_gap_exercise_4363_13 (hs : boxSetup4363 f g hfun S a b c) (h12 : yeval4363 g S a c b) : yscale4363 g a b c := by sorry
theorem proof_gap_exercise_4363_14 (h11 : ypart4363 S Iy) (h12 : yeval4363 g S a c b) (h13 : yscale4363 g a b c) : Iy = a*b*c*frac (g b - g 0) b := by sorry
theorem proof_gap_exercise_4363_15 (h1 : total4363 S I) (hx : xpart4363 S Ix) (hy : ypart4363 S Iy) (hz : zpart4363 S Iz) : decomp4363 I Ix Iy Iz := by sorry
theorem proof_gap_exercise_4363_16 (h10 : Ix = a*b*c*frac (f a - f 0) a) (h14 : Iy = a*b*c*frac (g b - g 0) b) (h6 : Iz = a*b*c*frac (hfun c - hfun 0) c) : Ix + Iy + Iz = a*b*c*(frac (f a - f 0) a + frac (g b - g 0) b + frac (hfun c - hfun 0) c) := by sorry
theorem proof_gap_exercise_4363_17 (h15 : decomp4363 I Ix Iy Iz) (h16 : Ix + Iy + Iz = a*b*c*(frac (f a - f 0) a + frac (g b - g 0) b + frac (hfun c - hfun 0) c)) : I = a*b*c*(frac (f a - f 0) a + frac (g b - g 0) b + frac (hfun c - hfun 0) c) := by sorry

end ProofGraderGenerated
