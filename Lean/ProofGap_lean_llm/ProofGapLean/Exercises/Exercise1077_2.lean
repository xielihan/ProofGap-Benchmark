import ProofGapLean.Prelude.Core
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow

namespace ProofGap.Exercise1077_2

noncomputable section

def x (t : ℝ) : ℝ := 2 * t - t ^ 2
def y (t : ℝ) : ℝ := 3 * t - t ^ 3
def slope (t : ℝ) : ℝ := deriv y t / deriv x t
def resolvedSlope (t : ℝ) : ℝ := (3 / 2 : ℝ) * (1 + t)

def tangent : Set (ℝ × ℝ) := {p | 3 * p.1 - p.2 - 1 = 0}
def normal : Set (ℝ × ℝ) := {p | p.1 + 3 * p.2 - 7 = 0}

theorem gap1 (t : ℝ) (ht : t ≠ 1) :
    slope t = (3 - 3 * t ^ 2) / (2 - 2 * t) := by
  have hy : HasDerivAt y (3 - 3 * t ^ 2) t := by
    unfold y
    convert
      ((hasDerivAt_id t).const_mul 3).sub ((hasDerivAt_id t).pow 3)
      using 1 <;> simp [id] <;> ring
  have hx : HasDerivAt x (2 - 2 * t) t := by
    unfold x
    convert
      ((hasDerivAt_id t).const_mul 2).sub ((hasDerivAt_id t).pow 2)
      using 1 <;> simp [id] <;> ring
  unfold slope
  rw [hy.deriv, hx.deriv]

theorem gap2 (t : ℝ) (ht : t ≠ 1) :
    (3 - 3 * t ^ 2) / (2 - 2 * t) = resolvedSlope t := by
  unfold resolvedSlope
  field_simp [sub_ne_zero.mpr ht.symm]
  ring

theorem gap3 (t : ℝ) (ht : t ≠ 1) :
    slope t = resolvedSlope t := by
  rw [gap1 t ht, gap2 t ht]

theorem gap4 (t : ℝ) (ht : t = 1) : x t = 1 := by
  subst t
  norm_num [x]

theorem gap5 (t : ℝ) (ht : t = 1) : y t = 2 := by
  subst t
  norm_num [y]

theorem gap6 : resolvedSlope 1 = 3 := by
  norm_num [resolvedSlope]

theorem gap7 :
    tangent = {p : ℝ × ℝ | 3 * p.1 - p.2 - 1 = 0} := by
  rfl

theorem gap8 :
    normal = {p : ℝ × ℝ | p.1 + 3 * p.2 - 7 = 0} := by
  rfl

end

end ProofGap.Exercise1077_2
