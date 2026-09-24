import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace ProofGap.Exercise4454_1

noncomputable section

open scoped Interval

abbrev Vec3 := ℝ × ℝ × ℝ

def dot (p q : Vec3) : ℝ :=
  p.1 * q.1 + p.2.1 * q.2.1 + p.2.2 * q.2.2

def circle (t : ℝ) : Vec3 :=
  (Real.cos t, Real.sin t, 0)

def circleVelocity (t : ℝ) : Vec3 :=
  (-Real.sin t, Real.cos t, 0)

def swirlField (c : ℝ) (p : Vec3) : Vec3 :=
  (-p.2.1, p.1, c)

def workPullback (c t : ℝ) : ℝ :=
  dot (swirlField c (circle t)) (circleVelocity t)

def lineIntegral (c : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..2 * Real.pi, workPullback c t

theorem gap1 (t : ℝ) :
    circle t = (Real.cos t, Real.sin t, 0) := by
  rfl

theorem gap2 (c t : ℝ) :
    workPullback c t =
      dot (-Real.sin t, Real.cos t, c)
        (-Real.sin t, Real.cos t, 0) := by
  rfl

theorem gap3 (c t : ℝ) :
    dot (-Real.sin t, Real.cos t, c)
        (-Real.sin t, Real.cos t, 0) = 1 := by
  simp [dot, ← pow_two, Real.sin_sq_add_cos_sq]

theorem gap4 (c t : ℝ) :
    workPullback c t = 1 := by
  rw [gap2, gap3]

theorem gap5 (c : ℝ) :
    lineIntegral c = ∫ t in (0 : ℝ)..2 * Real.pi, (1 : ℝ) := by
  unfold lineIntegral
  simp only [gap4]

theorem gap6 :
    (∫ _t in (0 : ℝ)..2 * Real.pi, (1 : ℝ)) =
      2 * Real.pi := by
  simp

theorem gap7 (c : ℝ) :
    lineIntegral c = 2 * Real.pi := by
  rw [gap5, gap6]

end

end ProofGap.Exercise4454_1
