import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise1040

noncomputable section

def x (t : ℝ) : ℝ := Real.sin t ^ 2
def y (t : ℝ) : ℝ := Real.cos t ^ 2
def slope (t : ℝ) : ℝ := deriv y t / deriv x t

theorem gap1 (t : ℝ) :
    HasDerivAt y (-2 * Real.cos t * Real.sin t) t := by
  unfold y
  convert (Real.hasDerivAt_cos t).pow 2 using 1 <;> ring

theorem gap2 (t : ℝ) :
    HasDerivAt x (2 * Real.sin t * Real.cos t) t := by
  unfold x
  convert (Real.hasDerivAt_sin t).pow 2 using 1 <;> ring

theorem gap3 (t : ℝ) (h : Real.sin t * Real.cos t ≠ 0) :
    slope t =
      (-2 * Real.cos t * Real.sin t) /
        (2 * Real.cos t * Real.sin t) := by
  unfold slope
  rw [(gap1 t).deriv, (gap2 t).deriv]
  congr 1 <;> ring

theorem gap4 (t : ℝ) (h : Real.sin t * Real.cos t ≠ 0) :
    (-2 * Real.cos t * Real.sin t) /
      (2 * Real.cos t * Real.sin t) = -1 := by
  have hs : Real.sin t ≠ 0 := by
    intro hs
    apply h
    rw [hs, zero_mul]
  have hc : Real.cos t ≠ 0 := by
    intro hc
    apply h
    rw [hc, mul_zero]
  have hd : 2 * Real.cos t * Real.sin t ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) hc) hs
  apply (div_eq_iff hd).2
  ring

theorem gap5 (t : ℝ) (h : Real.sin t * Real.cos t ≠ 0) :
    slope t = -1 := by
  calc
    slope t =
        (-2 * Real.cos t * Real.sin t) /
          (2 * Real.cos t * Real.sin t) := gap3 t h
    _ = -1 := gap4 t h

end

end ProofGap.Exercise1040
