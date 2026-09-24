import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1043

noncomputable section

def x (a : ℝ) (t : ℝ) : ℝ := a * Real.cos t ^ 3
def y (a : ℝ) (t : ℝ) : ℝ := a * Real.sin t ^ 3
def slope (a t : ℝ) : ℝ := deriv (y a) t / deriv (x a) t

def regular (a t : ℝ) : Prop :=
  a ≠ 0 ∧ Real.sin t ≠ 0 ∧ Real.cos t ≠ 0

theorem gap1 (a t : ℝ) :
    HasDerivAt (y a) (3 * a * Real.sin t ^ 2 * Real.cos t) t := by
  convert ((Real.hasDerivAt_sin t).pow 3).const_mul a using 1 <;> ring

theorem gap2 (a t : ℝ) :
    HasDerivAt (x a) (-3 * a * Real.cos t ^ 2 * Real.sin t) t := by
  convert ((Real.hasDerivAt_cos t).pow 3).const_mul a using 1 <;> simp [x] <;> ring

theorem gap3 (a t : ℝ) (h : regular a t) :
    slope a t =
      (3 * a * Real.sin t ^ 2 * Real.cos t) /
        (-3 * a * Real.cos t ^ 2 * Real.sin t) := by
  unfold slope
  rw [(gap1 a t).deriv, (gap2 a t).deriv]

theorem gap4 (a t : ℝ) (h : regular a t) :
    (3 * a * Real.sin t ^ 2 * Real.cos t) /
      (-3 * a * Real.cos t ^ 2 * Real.sin t) = -Real.tan t := by
  rcases h with ⟨ha, hs, hc⟩
  rw [Real.tan_eq_sin_div_cos]
  field_simp [ha, hs, hc] <;> ring

theorem gap5 (a t : ℝ) (h : regular a t) :
    slope a t = -Real.tan t := by
  rw [gap3 a t h, gap4 a t h]

end

end ProofGap.Exercise1043
