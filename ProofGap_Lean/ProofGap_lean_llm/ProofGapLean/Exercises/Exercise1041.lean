import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1041

noncomputable section

def x (a : ℝ) (t : ℝ) : ℝ := a * Real.cos t
def y (b : ℝ) (t : ℝ) : ℝ := b * Real.sin t
def cot (t : ℝ) : ℝ := Real.cos t / Real.sin t
def slope (a b t : ℝ) : ℝ := deriv (y b) t / deriv (x a) t

theorem gap1 (b t : ℝ) :
    HasDerivAt (y b) (b * Real.cos t) t := by
  simpa [y] using (Real.hasDerivAt_sin t).const_mul b

theorem gap2 (a t : ℝ) :
    HasDerivAt (x a) (-a * Real.sin t) t := by
  simpa [x] using (Real.hasDerivAt_cos t).const_mul a

theorem gap3 (a b t : ℝ) (ha : a ≠ 0) (ht : Real.sin t ≠ 0) :
    slope a b t = b * Real.cos t / (-a * Real.sin t) := by
  rw [slope, (gap1 b t).deriv, (gap2 a t).deriv]

theorem gap4 (a b t : ℝ) (ha : a ≠ 0) (ht : Real.sin t ≠ 0) :
    b * Real.cos t / (-a * Real.sin t) = -(b / a) * cot t := by
  rw [cot]
  field_simp [ha, ht] <;> ring

theorem gap5 (a b t : ℝ) (ha : a ≠ 0) (ht : Real.sin t ≠ 0) :
    slope a b t = -(b / a) * cot t := by
  calc
    slope a b t = b * Real.cos t / (-a * Real.sin t) := gap3 a b t ha ht
    _ = -(b / a) * cot t := gap4 a b t ha ht

end

end ProofGap.Exercise1041
