import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1030

noncomputable section

def area (x y : ℝ → ℝ) (t : ℝ) : ℝ := x t * y t
def diagonal (x y : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.sqrt (x t ^ 2 + y t ^ 2)

theorem gap1 (x y : ℝ → ℝ) (t : ℝ) :
    area x y t = x t * y t := by
  rfl

theorem gap2 (x y : ℝ → ℝ) (t : ℝ) :
    diagonal x y t = Real.sqrt (x t ^ 2 + y t ^ 2) := by
  rfl

theorem gap3 (x y : ℝ → ℝ) (t : ℝ)
    (hx : HasDerivAt x (-1) t) (hy : HasDerivAt y 2 t) :
    HasDerivAt (area x y)
      (x t * deriv y t + y t * deriv x t) t := by
  convert hx.mul hy using 1 <;>
    simp [area, hx.deriv, hy.deriv] <;>
    ring

theorem gap4 (x y : ℝ → ℝ) (t : ℝ)
    (hx : HasDerivAt x (-1) t) (hy : HasDerivAt y 2 t)
    (hpos : 0 < x t ^ 2 + y t ^ 2) :
    HasDerivAt (diagonal x y)
      ((x t * deriv x t + y t * deriv y t) /
        Real.sqrt (x t ^ 2 + y t ^ 2)) t := by
  have hsqrt : Real.sqrt (x t ^ 2 + y t ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hpos)
  have hx2 :
      HasDerivAt (fun s => x s ^ 2) (2 * x t * (-1)) t := by
    simpa using hx.pow 2
  have hy2 :
      HasDerivAt (fun s => y s ^ 2) (2 * y t * 2) t := by
    simpa using hy.pow 2
  have hinner0 :
      HasDerivAt (fun s => x s ^ 2 + y s ^ 2)
        (2 * x t * (-1) + 2 * y t * 2) t :=
    HasDerivAt.add hx2 hy2
  have hinner :
      HasDerivAt (fun s => x s ^ 2 + y s ^ 2)
        (2 * (x t * (-1) + y t * 2)) t := by
    convert hinner0 using 1
    ring
  have hcomp :
      HasDerivAt (fun s => Real.sqrt (x s ^ 2 + y s ^ 2))
        ((1 / (2 * Real.sqrt (x t ^ 2 + y t ^ 2))) *
          (2 * (x t * (-1) + y t * 2))) t :=
    (Real.hasDerivAt_sqrt (ne_of_gt hpos)).comp t hinner
  rw [hx.deriv, hy.deriv]
  change HasDerivAt (fun s => Real.sqrt (x s ^ 2 + y s ^ 2))
    ((x t * (-1) + y t * 2) / Real.sqrt (x t ^ 2 + y t ^ 2)) t
  have hcoef :
      (x t * (-1) + y t * 2) / Real.sqrt (x t ^ 2 + y t ^ 2) =
        (1 / (2 * Real.sqrt (x t ^ 2 + y t ^ 2))) *
          (2 * (x t * (-1) + y t * 2)) := by
    field_simp [hsqrt]
  rw [hcoef]
  exact hcomp

theorem gap5 (x y : ℝ → ℝ) (t : ℝ)
    (hx : HasDerivAt x (-1) t) (hy : HasDerivAt y 2 t)
    (hxv : x t = 20) (hyv : y t = 15) :
    deriv (area x y) t = 20 * 2 + (-1) * 15 := by
  have h := (gap3 x y t hx hy).deriv
  rw [hx.deriv, hy.deriv, hxv, hyv] at h
  convert h using 1 <;> ring

theorem gap6 : (20 : ℝ) * 2 + (-1) * 15 = 25 := by
  norm_num

theorem gap7 (x y : ℝ → ℝ) (t : ℝ)
    (hx : HasDerivAt x (-1) t) (hy : HasDerivAt y 2 t)
    (hxv : x t = 20) (hyv : y t = 15) :
    HasDerivAt (area x y) 25 t := by
  have h := gap3 x y t hx hy
  rw [hx.deriv, hy.deriv, hxv, hyv] at h
  convert h using 1 <;> norm_num

theorem gap8 (x y : ℝ → ℝ) (t : ℝ)
    (hx : HasDerivAt x (-1) t) (hy : HasDerivAt y 2 t)
    (hxv : x t = 20) (hyv : y t = 15) :
    deriv (diagonal x y) t =
      (-20 + 2 * 15) / Real.sqrt (20 ^ 2 + 15 ^ 2) := by
  have hpos : 0 < x t ^ 2 + y t ^ 2 := by
    rw [hxv, hyv]
    norm_num
  have h := (gap4 x y t hx hy hpos).deriv
  rw [hx.deriv, hy.deriv, hxv, hyv] at h
  convert h using 1 <;> ring

theorem gap9 :
    ((-20 + 2 * 15) / Real.sqrt (20 ^ 2 + 15 ^ 2) : ℝ) = 2 / 5 := by
  have hsqrt :
      Real.sqrt ((20 : ℝ) ^ 2 + 15 ^ 2) = 25 := by
    rw [show (20 : ℝ) ^ 2 + 15 ^ 2 = 25 ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  rw [hsqrt]
  norm_num

theorem gap10 (x y : ℝ → ℝ) (t : ℝ)
    (hx : HasDerivAt x (-1) t) (hy : HasDerivAt y 2 t)
    (hxv : x t = 20) (hyv : y t = 15) :
    HasDerivAt (diagonal x y) (2 / 5) t := by
  have hpos : 0 < x t ^ 2 + y t ^ 2 := by
    rw [hxv, hyv]
    norm_num
  have h := gap4 x y t hx hy hpos
  rw [hx.deriv, hy.deriv, hxv, hyv] at h
  have hcoef :
      ((20 * (-1) + 15 * 2) /
        Real.sqrt (20 ^ 2 + 15 ^ 2) : ℝ) = 2 / 5 := by
    calc
      ((20 * (-1) + 15 * 2) /
          Real.sqrt (20 ^ 2 + 15 ^ 2) : ℝ) =
          (-20 + 2 * 15) / Real.sqrt (20 ^ 2 + 15 ^ 2) := by ring
      _ = 2 / 5 := gap9
  rw [hcoef] at h
  exact h

end

end ProofGap.Exercise1030
