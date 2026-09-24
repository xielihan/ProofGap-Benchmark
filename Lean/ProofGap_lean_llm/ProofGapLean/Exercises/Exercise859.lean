import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise859

noncomputable section

def y (x : ℝ) : ℝ :=
  1 / (Real.sqrt (1 + x ^ 2) * (x + Real.sqrt (1 + x ^ 2)))

/-- Source: `proof_gap/exercise_859/1.txt`. -/
theorem gap1 (x : ℝ) :
    HasDerivAt y
      (-(1 / ((1 + x ^ 2) * (x + Real.sqrt (1 + x ^ 2)) ^ 2)) *
        (Real.sqrt (1 + x ^ 2) +
          x ^ 2 / Real.sqrt (1 + x ^ 2) + 2 * x)) x := by
  unfold y
  have hp : 0 < 1 + x ^ 2 := by
    nlinarith [sq_nonneg x]
  have hu_ne : 1 + x ^ 2 ≠ 0 := ne_of_gt hp
  have hs_ne : Real.sqrt (1 + x ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hp)
  have hs_sq : Real.sqrt (1 + x ^ 2) ^ 2 = 1 + x ^ 2 :=
    Real.sq_sqrt (le_of_lt hp)
  have ht_pos : 0 < x + Real.sqrt (1 + x ^ 2) := by
    by_contra h
    have ht_nonpos : x + Real.sqrt (1 + x ^ 2) ≤ 0 := le_of_not_gt h
    have hfactor_nonneg : 0 ≤ Real.sqrt (1 + x ^ 2) - x := by
      nlinarith [Real.sqrt_nonneg (1 + x ^ 2)]
    have hproduct_nonpos :
        (Real.sqrt (1 + x ^ 2) - x) *
            (Real.sqrt (1 + x ^ 2) + x) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hfactor_nonneg (by linarith)
    nlinarith [hs_sq]
  have ht_ne : x + Real.sqrt (1 + x ^ 2) ≠ 0 := ne_of_gt ht_pos
  have hsq : HasDerivAt (fun z : ℝ => z ^ 2) (2 * x) x := by
    convert (hasDerivAt_id x).pow 2 using 1 <;>
      simp [id, mul_comm]
  have hu : HasDerivAt (fun z : ℝ => 1 + z ^ 2) (2 * x) x :=
    hsq.const_add 1
  have hs_comp :
      HasDerivAt (Real.sqrt ∘ fun z : ℝ => 1 + z ^ 2)
        ((1 / (2 * Real.sqrt (1 + x ^ 2))) * (2 * x)) x :=
    (Real.hasDerivAt_sqrt hu_ne).comp x hu
  have hcoef :
      (1 / (2 * Real.sqrt (1 + x ^ 2))) * (2 * x) =
        x / Real.sqrt (1 + x ^ 2) := by
    field_simp [hs_ne] <;> ring
  have hs : HasDerivAt (fun z : ℝ => Real.sqrt (1 + z ^ 2))
      (x / Real.sqrt (1 + x ^ 2)) x := by
    simpa only [Function.comp_apply, hcoef] using hs_comp
  have hd : HasDerivAt
      (fun z : ℝ =>
        Real.sqrt (1 + z ^ 2) * (z + Real.sqrt (1 + z ^ 2)))
      ((x / Real.sqrt (1 + x ^ 2)) *
          (x + Real.sqrt (1 + x ^ 2)) +
        Real.sqrt (1 + x ^ 2) *
          (1 + x / Real.sqrt (1 + x ^ 2))) x :=
    hs.mul ((hasDerivAt_id x).add hs)
  have hden_ne :
      Real.sqrt (1 + x ^ 2) * (x + Real.sqrt (1 + x ^ 2)) ≠ 0 :=
    mul_ne_zero hs_ne ht_ne
  have hinv : HasDerivAt
      (fun z : ℝ =>
        1 / (Real.sqrt (1 + z ^ 2) *
          (z + Real.sqrt (1 + z ^ 2))))
      (-((x / Real.sqrt (1 + x ^ 2)) *
            (x + Real.sqrt (1 + x ^ 2)) +
          Real.sqrt (1 + x ^ 2) *
            (1 + x / Real.sqrt (1 + x ^ 2))) /
        (Real.sqrt (1 + x ^ 2) *
          (x + Real.sqrt (1 + x ^ 2))) ^ 2) x := by
    simpa only [one_div] using hd.inv hden_ne
  have hdval :
      (x / Real.sqrt (1 + x ^ 2)) *
          (x + Real.sqrt (1 + x ^ 2)) +
        Real.sqrt (1 + x ^ 2) *
          (1 + x / Real.sqrt (1 + x ^ 2)) =
      Real.sqrt (1 + x ^ 2) +
        x ^ 2 / Real.sqrt (1 + x ^ 2) + 2 * x := by
    field_simp [hs_ne] <;> ring
  have hden :
      (Real.sqrt (1 + x ^ 2) *
        (x + Real.sqrt (1 + x ^ 2))) ^ 2 =
      (1 + x ^ 2) * (x + Real.sqrt (1 + x ^ 2)) ^ 2 := by
    rw [mul_pow, hs_sq]
  rw [hdval, hden] at hinv
  convert hinv using 1 <;> ring

/-- Source: `proof_gap/exercise_859/2.txt`. -/
theorem gap2 (x : ℝ) :
    -(1 / ((1 + x ^ 2) * (x + Real.sqrt (1 + x ^ 2)) ^ 2)) *
          (Real.sqrt (1 + x ^ 2) +
            x ^ 2 / Real.sqrt (1 + x ^ 2) + 2 * x) =
      -(1 / Real.rpow (1 + x ^ 2) (3 / 2 : ℝ)) := by
  have hp : 0 < 1 + x ^ 2 := by
    nlinarith [sq_nonneg x]
  have hu_ne : 1 + x ^ 2 ≠ 0 := ne_of_gt hp
  have hs_ne : Real.sqrt (1 + x ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hp)
  have hs_sq : Real.sqrt (1 + x ^ 2) ^ 2 = 1 + x ^ 2 :=
    Real.sq_sqrt (le_of_lt hp)
  have ht_pos : 0 < x + Real.sqrt (1 + x ^ 2) := by
    by_contra h
    have ht_nonpos : x + Real.sqrt (1 + x ^ 2) ≤ 0 := le_of_not_gt h
    have hfactor_nonneg : 0 ≤ Real.sqrt (1 + x ^ 2) - x := by
      nlinarith [Real.sqrt_nonneg (1 + x ^ 2)]
    have hproduct_nonpos :
        (Real.sqrt (1 + x ^ 2) - x) *
            (Real.sqrt (1 + x ^ 2) + x) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hfactor_nonneg (by linarith)
    nlinarith [hs_sq]
  have ht_ne : x + Real.sqrt (1 + x ^ 2) ≠ 0 := ne_of_gt ht_pos
  have hnum :
      Real.sqrt (1 + x ^ 2) +
          x ^ 2 / Real.sqrt (1 + x ^ 2) + 2 * x =
        (x + Real.sqrt (1 + x ^ 2)) ^ 2 /
          Real.sqrt (1 + x ^ 2) := by
    field_simp [hs_ne]
    nlinarith [hs_sq]
  have hrpow :
      Real.rpow (1 + x ^ 2) (3 / 2 : ℝ) =
        (1 + x ^ 2) * Real.sqrt (1 + x ^ 2) := by
    change (1 + x ^ 2) ^ (3 / 2 : ℝ) =
      (1 + x ^ 2) * Real.sqrt (1 + x ^ 2)
    calc
      (1 + x ^ 2) ^ (3 / 2 : ℝ) =
          (1 + x ^ 2) ^ (1 + 1 / 2 : ℝ) := by norm_num
      _ = (1 + x ^ 2) ^ (1 : ℝ) *
          (1 + x ^ 2) ^ (1 / 2 : ℝ) := by
            rw [Real.rpow_add hp]
      _ = (1 + x ^ 2) * Real.sqrt (1 + x ^ 2) := by
            rw [Real.rpow_one, ← Real.sqrt_eq_rpow]
  rw [hnum, hrpow]
  field_simp [hu_ne, hs_ne, ht_ne] <;> ring

/-- Source: `proof_gap/exercise_859/3.txt`. -/
theorem gap3 (x : ℝ) :
    HasDerivAt y (-(1 / Real.rpow (1 + x ^ 2) (3 / 2 : ℝ))) x := by
  simpa only [gap2 x] using gap1 x

end

end ProofGap.Exercise859
