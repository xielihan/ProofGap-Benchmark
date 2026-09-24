import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1044

noncomputable section

def x (a : ℝ) (t : ℝ) : ℝ := a * (t - Real.sin t)
def y (a : ℝ) (t : ℝ) : ℝ := a * (1 - Real.cos t)
def cot (t : ℝ) : ℝ := Real.cos t / Real.sin t
def slope (a t : ℝ) : ℝ := deriv (y a) t / deriv (x a) t

def regular (a t : ℝ) : Prop :=
  a ≠ 0 ∧ 1 - Real.cos t ≠ 0 ∧ Real.sin (t / 2) ≠ 0

theorem gap1 (a t : ℝ) :
    HasDerivAt (y a) (a * Real.sin t) t := by
  simpa [y] using
    (((hasDerivAt_const (x := t) (c := (1 : ℝ))).sub
      (Real.hasDerivAt_cos t)).const_mul a)

theorem gap2 (a t : ℝ) :
    HasDerivAt (x a) (a * (1 - Real.cos t)) t := by
  simpa [x] using
    (((hasDerivAt_id t).sub (Real.hasDerivAt_sin t)).const_mul a)

theorem gap3 (a t : ℝ) (h : regular a t) :
    slope a t = a * Real.sin t / (a * (1 - Real.cos t)) := by
  simp only [slope, (gap1 a t).deriv, (gap2 a t).deriv]

theorem gap4 (a t : ℝ) (h : regular a t) :
    a * Real.sin t / (a * (1 - Real.cos t)) = cot (t / 2) := by
  rcases h with ⟨ha, _, hs⟩
  have ht : 2 * (t / 2) = t := by ring
  have hsin :
      Real.sin t = 2 * Real.sin (t / 2) * Real.cos (t / 2) := by
    calc
      Real.sin t = Real.sin (2 * (t / 2)) := by rw [ht]
      _ = 2 * Real.sin (t / 2) * Real.cos (t / 2) := by
        rw [Real.sin_two_mul]
  have hcos :
      1 - Real.cos t = 2 * Real.sin (t / 2) ^ 2 := by
    calc
      1 - Real.cos t = 1 - Real.cos (2 * (t / 2)) := by rw [ht]
      _ = 2 * Real.sin (t / 2) ^ 2 := by
        rw [Real.cos_two_mul']
        nlinarith [Real.sin_sq_add_cos_sq (t / 2)]
  rw [hsin, hcos]
  unfold cot
  field_simp [ha, hs] <;> ring

theorem gap5 (a t : ℝ) (h : regular a t) :
    slope a t = cot (t / 2) := by
  calc
    slope a t = a * Real.sin t / (a * (1 - Real.cos t)) := gap3 a t h
    _ = cot (t / 2) := gap4 a t h

end

end ProofGap.Exercise1044
