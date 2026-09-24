import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1111

noncomputable section

def y (x : ℝ) : ℝ := x * Real.sqrt (1 + x ^ 2)

def secondDeriv (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  deriv (fun t => deriv f t) x

def threeHalves (x : ℝ) : ℝ := Real.rpow x (3 / 2 : ℝ)

theorem gap1 (x : ℝ) :
    deriv y x =
      Real.sqrt (1 + x ^ 2) + x ^ 2 / Real.sqrt (1 + x ^ 2) := by
  unfold y
  have hpos : 0 < 1 + x ^ 2 := by positivity
  have hsqrt_ne : Real.sqrt (1 + x ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hpos)
  have hid : HasDerivAt (fun t : ℝ => t) 1 x := hasDerivAt_id x
  have hinner : HasDerivAt (fun t : ℝ => 1 + t ^ 2) (2 * x) x := by
    convert HasDerivAt.add (hasDerivAt_const x (1 : ℝ)) (hid.pow 2) using 1 <;>
      ring
  have hsqrt : HasDerivAt (fun t : ℝ => Real.sqrt (1 + t ^ 2))
      (x / Real.sqrt (1 + x ^ 2)) x := by
    convert (Real.hasDerivAt_sqrt hpos.ne').comp x hinner using 1 <;>
      field_simp [hsqrt_ne] <;> ring
  convert (HasDerivAt.mul hid hsqrt).deriv using 1 <;>
    field_simp [hsqrt_ne] <;> ring

theorem gap2 (x : ℝ) :
    Real.sqrt (1 + x ^ 2) + x ^ 2 / Real.sqrt (1 + x ^ 2) =
      (1 + 2 * x ^ 2) / Real.sqrt (1 + x ^ 2) := by
  have hpos : 0 < 1 + x ^ 2 := by positivity
  have hsqrt_ne : Real.sqrt (1 + x ^ 2) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hpos)
  have hsqrt_sq : Real.sqrt (1 + x ^ 2) ^ 2 = 1 + x ^ 2 := by
    exact Real.sq_sqrt hpos.le
  field_simp [hsqrt_ne]
  nlinarith

theorem gap3 (x : ℝ) :
    deriv y x = (1 + 2 * x ^ 2) / Real.sqrt (1 + x ^ 2) := by
  rw [gap1, gap2]

theorem gap4 (x : ℝ) :
    secondDeriv y x =
      (4 * x * Real.sqrt (1 + x ^ 2) -
          x * (1 + 2 * x ^ 2) / Real.sqrt (1 + x ^ 2)) /
        (1 + x ^ 2) := by
  unfold secondDeriv
  have hfun : (fun t : ℝ => deriv y t) =
      (fun t : ℝ => (1 + 2 * t ^ 2) / Real.sqrt (1 + t ^ 2)) := by
    funext t
    exact gap3 t
  rw [hfun]
  have hpos : 0 < 1 + x ^ 2 := by positivity
  have hsqrt_ne : Real.sqrt (1 + x ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hpos)
  have hbase_ne : 1 + x ^ 2 ≠ 0 := ne_of_gt hpos
  have hsqrt_sq : Real.sqrt (1 + x ^ 2) ^ 2 = 1 + x ^ 2 :=
    Real.sq_sqrt hpos.le
  have hid : HasDerivAt (fun t : ℝ => t) 1 x := hasDerivAt_id x
  have hinner : HasDerivAt (fun t : ℝ => 1 + t ^ 2) (2 * x) x := by
    convert HasDerivAt.add (hasDerivAt_const x (1 : ℝ)) (hid.pow 2) using 1 <;>
      ring
  have hsqrt : HasDerivAt (fun t : ℝ => Real.sqrt (1 + t ^ 2))
      (x / Real.sqrt (1 + x ^ 2)) x := by
    convert (Real.hasDerivAt_sqrt hpos.ne').comp x hinner using 1 <;>
      field_simp [hsqrt_ne] <;> ring
  have hnum : HasDerivAt (fun t : ℝ => 1 + 2 * t ^ 2) (4 * x) x := by
    have hscaled : HasDerivAt (fun t : ℝ => 2 * t ^ 2) (4 * x) x := by
      convert HasDerivAt.mul (hasDerivAt_const x (2 : ℝ)) (hid.pow 2) using 1 <;>
        ring
    convert HasDerivAt.add (hasDerivAt_const x (1 : ℝ)) hscaled using 1 <;>
      ring
  convert (HasDerivAt.div hnum hsqrt hsqrt_ne).deriv using 1 <;>
    field_simp [hsqrt_ne, hbase_ne] <;>
    simp [hsqrt_sq] <;> ring

theorem gap5 (x : ℝ) :
    (4 * x * Real.sqrt (1 + x ^ 2) -
          x * (1 + 2 * x ^ 2) / Real.sqrt (1 + x ^ 2)) /
        (1 + x ^ 2) =
      x * (3 + 2 * x ^ 2) / threeHalves (1 + x ^ 2) := by
  have hpos : 0 < 1 + x ^ 2 := by positivity
  have hsqrt_pos : 0 < Real.sqrt (1 + x ^ 2) := Real.sqrt_pos.2 hpos
  have hsqrt_ne : Real.sqrt (1 + x ^ 2) ≠ 0 := ne_of_gt hsqrt_pos
  have hbase_ne : 1 + x ^ 2 ≠ 0 := ne_of_gt hpos
  have hsqrt_sq : Real.sqrt (1 + x ^ 2) ^ 2 = 1 + x ^ 2 := Real.sq_sqrt hpos.le
  have hrpow_exp : threeHalves (1 + x ^ 2) =
      Real.exp (Real.log (1 + x ^ 2) * (3 / 2 : ℝ)) := by
    unfold threeHalves
    exact Real.rpow_def_of_pos hpos (3 / 2 : ℝ)
  have hsqrt_exp : Real.sqrt (1 + x ^ 2) =
      Real.exp (Real.log (1 + x ^ 2) * (1 / 2 : ℝ)) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_def_of_pos hpos (1 / 2 : ℝ)
  have hrpow : threeHalves (1 + x ^ 2) =
      (1 + x ^ 2) * Real.sqrt (1 + x ^ 2) := by
    rw [hrpow_exp, hsqrt_exp]
    calc
      Real.exp (Real.log (1 + x ^ 2) * (3 / 2 : ℝ)) =
          Real.exp (Real.log (1 + x ^ 2) +
            Real.log (1 + x ^ 2) * (1 / 2 : ℝ)) := by
        congr 1
        ring
      _ = Real.exp (Real.log (1 + x ^ 2)) *
          Real.exp (Real.log (1 + x ^ 2) * (1 / 2 : ℝ)) := by
        rw [Real.exp_add]
      _ = (1 + x ^ 2) *
          Real.exp (Real.log (1 + x ^ 2) * (1 / 2 : ℝ)) := by
        rw [Real.exp_log hpos]
  rw [hrpow]
  field_simp [hsqrt_ne, hbase_ne]
  rw [hsqrt_sq]
  ring

theorem gap6 (x : ℝ) :
    secondDeriv y x =
      x * (3 + 2 * x ^ 2) / threeHalves (1 + x ^ 2) := by
  rw [gap4, gap5]

end

end ProofGap.Exercise1111
