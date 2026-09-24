import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4363

noncomputable section

open scoped Interval

def zFaceFlux (a b c : ℝ) (h : ℝ → ℝ) : ℝ :=
  a * b * (h c - h 0)

def xFaceFlux (b c a : ℝ) (f : ℝ → ℝ) : ℝ :=
  b * c * (f a - f 0)

def yFaceFlux (a c b : ℝ) (g : ℝ → ℝ) : ℝ :=
  a * c * (g b - g 0)

def totalFlux (a b c : ℝ) (f g h : ℝ → ℝ) : ℝ :=
  xFaceFlux b c a f + yFaceFlux a c b g + zFaceFlux a b c h

theorem gap1 (a b c : ℝ) (h : ℝ → ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hh : Continuous h) :
    zFaceFlux a b c h =
      (∫ x in (0 : ℝ)..a, ∫ y in (0 : ℝ)..b, h c) -
        ∫ x in (0 : ℝ)..a, ∫ y in (0 : ℝ)..b, h 0 := by
  simp [zFaceFlux] <;> ring

theorem gap2 (a b c : ℝ) (h : ℝ → ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    zFaceFlux a b c h =
      a * b * c * ((h c - h 0) / c) := by
  have hc0 : c ≠ 0 := ne_of_gt hc
  unfold zFaceFlux
  field_simp [hc0] <;> ring

theorem gap3 (a b c : ℝ) (f : ℝ → ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    xFaceFlux b c a f =
      a * b * c * ((f a - f 0) / a) := by
  have ha0 : a ≠ 0 := ne_of_gt ha
  unfold xFaceFlux
  field_simp [ha0] <;> ring

theorem gap4 (a b c : ℝ) (g : ℝ → ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    yFaceFlux a c b g =
      a * b * c * ((g b - g 0) / b) := by
  have hb0 : b ≠ 0 := ne_of_gt hb
  unfold yFaceFlux
  field_simp [hb0] <;> ring

theorem gap5 (a b c : ℝ) (f g h : ℝ → ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hf : Continuous f) (hg : Continuous g) (hh : Continuous h) :
    totalFlux a b c f g h =
      a * b * c *
        ((f a - f 0) / a + (g b - g 0) / b +
          (h c - h 0) / c) := by
  unfold totalFlux
  rw [gap3 a b c f ha hb hc, gap4 a b c g ha hb hc,
    gap2 a b c h ha hb hc]
  ring

end

end ProofGap.Exercise4363
