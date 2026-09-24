import ProofGapLean.Prelude.Core
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp

namespace ProofGap.Exercise1078_2

noncomputable section

def x (t : ℝ) : ℝ := (2 * t + t ^ 2) / (1 + t ^ 3)
def y (t : ℝ) : ℝ := (2 * t - t ^ 2) / (1 + t ^ 3)
def slope (t : ℝ) : ℝ := deriv y t / deriv x t

def regular (t : ℝ) : Prop :=
  1 + t ^ 3 ≠ 0 ∧ 2 + 2 * t - 4 * t ^ 3 - t ^ 4 ≠ 0

def tangent : Set (ℝ × ℝ) := {p | 3 * p.1 - p.2 - 4 = 0}
def normal : Set (ℝ × ℝ) := {p | p.1 + 3 * p.2 - 3 = 0}

theorem gap1 (t : ℝ) (ht : regular t) :
    slope t =
      (2 - 2 * t - 4 * t ^ 3 + t ^ 4) /
        (2 + 2 * t - 4 * t ^ 3 - t ^ 4) := by
  have ht2 : HasDerivAt (fun u : ℝ => u ^ 2) (2 * t) t := by
    have hraw := (hasDerivAt_id t).mul (hasDerivAt_id t)
    have hfun : (fun u : ℝ => u ^ 2) = (id : ℝ → ℝ) * id := by
      funext u
      simp [pow_two]
    rw [hfun]
    convert hraw using 1 <;> simp <;> ring
  have ht3 : HasDerivAt (fun u : ℝ => u ^ 3) (3 * t ^ 2) t := by
    have hraw := ht2.mul (hasDerivAt_id t)
    have hfun :
        (fun u : ℝ => u ^ 3) = (fun u : ℝ => u ^ 2) * id := by
      funext u
      simp [pow_succ]
    rw [hfun]
    convert hraw using 1 <;> simp <;> ring
  have hlin : HasDerivAt (fun u : ℝ => 2 * u) 2 t := by
    simpa using (hasDerivAt_id t).const_mul 2
  have hnumx :
      HasDerivAt (fun u : ℝ => 2 * u + u ^ 2) (2 + 2 * t) t := by
    simpa using hlin.add ht2
  have hnumy :
      HasDerivAt (fun u : ℝ => 2 * u - u ^ 2) (2 - 2 * t) t := by
    simpa using hlin.sub ht2
  have hden :
      HasDerivAt (fun u : ℝ => 1 + u ^ 3) (3 * t ^ 2) t := by
    exact ht3.const_add 1
  have hx' :
      HasDerivAt x
        ((2 + 2 * t - 4 * t ^ 3 - t ^ 4) / (1 + t ^ 3) ^ 2) t := by
    convert hnumx.mul (hden.inv ht.1) using 1 <;>
      simp [x, div_eq_mul_inv] <;>
      field_simp [ht.1] <;>
      ring
  have hy' :
      HasDerivAt y
        ((2 - 2 * t - 4 * t ^ 3 + t ^ 4) / (1 + t ^ 3) ^ 2) t := by
    convert hnumy.mul (hden.inv ht.1) using 1 <;>
      simp [y, div_eq_mul_inv] <;>
      field_simp [ht.1] <;>
      ring
  have hdx :
      deriv x t =
        (2 + 2 * t - 4 * t ^ 3 - t ^ 4) / (1 + t ^ 3) ^ 2 :=
    hx'.deriv
  have hdy :
      deriv y t =
        (2 - 2 * t - 4 * t ^ 3 + t ^ 4) / (1 + t ^ 3) ^ 2 :=
    hy'.deriv
  unfold slope
  rw [hdy, hdx]
  field_simp [ht.1, ht.2] <;> ring

theorem gap2 : x 1 = (3 / 2 : ℝ) := by
  norm_num [x]

theorem gap3 : y 1 = (1 / 2 : ℝ) := by
  norm_num [y]

theorem gap4 : slope 1 = 3 := by
  have hreg : regular 1 := by
    norm_num [regular]
  rw [gap1 1 hreg]
  norm_num

theorem gap5 :
    tangent = {p : ℝ × ℝ | 3 * p.1 - p.2 - 4 = 0} := by
  rfl

theorem gap6 :
    normal = {p : ℝ × ℝ | p.1 + 3 * p.2 - 3 = 0} := by
  rfl

end

end ProofGap.Exercise1078_2
