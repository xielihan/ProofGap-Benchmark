import ProofGapLean.Prelude.Core
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1078_1

noncomputable section

def x (t : ℝ) : ℝ := (2 * t + t ^ 2) / (1 + t ^ 3)
def y (t : ℝ) : ℝ := (2 * t - t ^ 2) / (1 + t ^ 3)
def slope (t : ℝ) : ℝ := deriv y t / deriv x t

def regular (t : ℝ) : Prop :=
  1 + t ^ 3 ≠ 0 ∧ 2 + 2 * t - 4 * t ^ 3 - t ^ 4 ≠ 0

def tangent : Set (ℝ × ℝ) := {p | p.2 = p.1}
def normal : Set (ℝ × ℝ) := {p | p.2 = -p.1}

theorem gap1 (t : ℝ) (ht : regular t) :
    slope t =
      (2 - 2 * t - 4 * t ^ 3 + t ^ 4) /
        (2 + 2 * t - 4 * t ^ 3 - t ^ 4) := by
  rcases ht with ⟨hden_ne, hxnum_ne⟩
  have hden :
      HasDerivAt (fun u : ℝ => 1 + u ^ 3) (3 * t ^ 2) t := by
    convert (hasDerivAt_const t (1 : ℝ)).add ((hasDerivAt_id t).pow 3) using 1 <;>
      simp [id] <;> ring
  have hx_num :
      HasDerivAt (fun u : ℝ => 2 * u + u ^ 2) (2 + 2 * t) t := by
    convert ((hasDerivAt_id t).const_mul (2 : ℝ)).add ((hasDerivAt_id t).pow 2) using 1 <;>
      simp [id] <;> ring
  have hy_num :
      HasDerivAt (fun u : ℝ => 2 * u - u ^ 2) (2 - 2 * t) t := by
    convert ((hasDerivAt_id t).const_mul (2 : ℝ)).sub ((hasDerivAt_id t).pow 2) using 1 <;>
      simp [id] <;> ring
  have hx_raw :
      HasDerivAt x
        (((2 + 2 * t) * (1 + t ^ 3) - (2 * t + t ^ 2) * (3 * t ^ 2)) /
          (1 + t ^ 3) ^ 2) t := by
    unfold x
    convert hx_num.div hden hden_ne using 1 <;> ring
  have hy_raw :
      HasDerivAt y
        (((2 - 2 * t) * (1 + t ^ 3) - (2 * t - t ^ 2) * (3 * t ^ 2)) /
          (1 + t ^ 3) ^ 2) t := by
    unfold y
    convert hy_num.div hden hden_ne using 1 <;> ring
  have hx_deriv :
      deriv x t =
        (2 + 2 * t - 4 * t ^ 3 - t ^ 4) / (1 + t ^ 3) ^ 2 := by
    calc
      deriv x t =
          ((2 + 2 * t) * (1 + t ^ 3) - (2 * t + t ^ 2) * (3 * t ^ 2)) /
            (1 + t ^ 3) ^ 2 := hx_raw.deriv
      _ = (2 + 2 * t - 4 * t ^ 3 - t ^ 4) / (1 + t ^ 3) ^ 2 := by ring
  have hy_deriv :
      deriv y t =
        (2 - 2 * t - 4 * t ^ 3 + t ^ 4) / (1 + t ^ 3) ^ 2 := by
    calc
      deriv y t =
          ((2 - 2 * t) * (1 + t ^ 3) - (2 * t - t ^ 2) * (3 * t ^ 2)) /
            (1 + t ^ 3) ^ 2 := hy_raw.deriv
      _ = (2 - 2 * t - 4 * t ^ 3 + t ^ 4) / (1 + t ^ 3) ^ 2 := by ring
  unfold slope
  rw [hy_deriv, hx_deriv]
  field_simp [hden_ne, hxnum_ne] <;> ring

theorem gap2 : x 0 = 0 := by
  norm_num [x]

theorem gap3 : y 0 = 0 := by
  norm_num [y]

theorem gap4 : slope 0 = 1 := by
  have hreg : regular 0 := by
    norm_num [regular]
  rw [gap1 0 hreg]
  norm_num

theorem gap5 :
    tangent = {p : ℝ × ℝ | p.2 = p.1} := by
  rfl

theorem gap6 :
    normal = {p : ℝ × ℝ | p.2 = -p.1} := by
  rfl

end

end ProofGap.Exercise1078_1
