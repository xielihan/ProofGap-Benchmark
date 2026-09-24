import ProofGapLean.Prelude.Analysis
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open scoped Interval

namespace ProofGap.Exercise2535

noncomputable section

def mesh (i : ℕ) : ℝ := 1 + 2 * i
def sample (i : ℕ) : ℝ := Real.sqrt (mesh i)
def simpsonApprox : ℝ :=
  2 / 3 * (sample 0 + sample 4 +
    4 * (sample 1 + sample 3) + 2 * sample 2)
def integralValue : ℝ := ∫ x in (1 : ℝ)..9, Real.sqrt x

private theorem nine_rpow_three_halves :
    (9 : ℝ) ^ (3 / 2 : ℝ) = 27 := by
  calc
    (9 : ℝ) ^ (3 / 2 : ℝ) =
        (9 : ℝ) ^ ((3 : ℝ) * (1 / 2 : ℝ)) := by norm_num
    _ = ((9 : ℝ) ^ (3 : ℝ)) ^ (1 / 2 : ℝ) := by
      rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 9)]
    _ = ((9 : ℝ) ^ (3 : ℕ)) ^ (1 / 2 : ℝ) := by
      exact congrArg (fun z : ℝ => z ^ (1 / 2 : ℝ))
        (Real.rpow_natCast (9 : ℝ) 3)
    _ = (729 : ℝ) ^ (1 / 2 : ℝ) := by norm_num
    _ = Real.sqrt 729 := by rw [Real.sqrt_eq_rpow]
    _ = 27 := by
      rw [show (729 : ℝ) = 27 ^ 2 by norm_num, Real.sqrt_sq_eq_abs]
      norm_num

private theorem integralValue_formula :
    integralValue =
      2 / 3 * (9 : ℝ) ^ (3 / 2 : ℝ) -
        2 / 3 * (1 : ℝ) ^ (3 / 2 : ℝ) := by
  unfold integralValue
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun x : ℝ => 2 / 3 * x ^ (3 / 2 : ℝ))
    (f' := fun x : ℝ => Real.sqrt x)
    (a := 1) (b := 9)
    (by
      intro x _
      convert
        (Real.hasDerivAt_rpow_const (p := (3 / 2 : ℝ))
          (Or.inr (by norm_num))).const_mul (2 / 3 : ℝ)
        using 1 <;> norm_num [Real.sqrt_eq_rpow] <;> ring)
    (Real.continuous_sqrt.intervalIntegrable _ _)

theorem gap1 : mesh 0 = 1 := by
  norm_num [mesh]
theorem gap2 : sample 0 = 1 := by
  norm_num [sample, mesh]
theorem gap3 : mesh 1 = 3 := by
  norm_num [mesh]
theorem gap4 : sample 1 = Real.sqrt 3 := by
  simp [sample, gap3]
theorem gap5 : |Real.sqrt 3 - 1.732| < 0.001 := by
  have hs : 0 ≤ Real.sqrt (3 : ℝ) := Real.sqrt_nonneg _
  have hs2 : (Real.sqrt (3 : ℝ)) ^ 2 = 3 :=
    Real.sq_sqrt (by norm_num)
  rw [abs_lt]
  constructor <;> nlinarith
theorem gap6 : mesh 2 = 5 := by
  norm_num [mesh]
theorem gap7 : sample 2 = Real.sqrt 5 := by
  simp [sample, gap6]
theorem gap8 : |Real.sqrt 5 - 2.236| < 0.001 := by
  have hs : 0 ≤ Real.sqrt (5 : ℝ) := Real.sqrt_nonneg _
  have hs2 : (Real.sqrt (5 : ℝ)) ^ 2 = 5 :=
    Real.sq_sqrt (by norm_num)
  rw [abs_lt]
  constructor <;> nlinarith
theorem gap9 : mesh 3 = 7 := by
  norm_num [mesh]
theorem gap10 : sample 3 = Real.sqrt 7 := by
  simp [sample, gap9]
theorem gap11 : |Real.sqrt 7 - 2.646| < 0.001 := by
  have hs : 0 ≤ Real.sqrt (7 : ℝ) := Real.sqrt_nonneg _
  have hs2 : (Real.sqrt (7 : ℝ)) ^ 2 = 7 :=
    Real.sq_sqrt (by norm_num)
  rw [abs_lt]
  constructor <;> nlinarith
theorem gap12 : mesh 4 = 9 := by
  norm_num [mesh]
theorem gap13 : sample 4 = 3 := by
  rw [sample, gap12]
  rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq_eq_abs]
  norm_num

theorem gap14 :
    simpsonApprox =
      2 / 3 * (sample 0 + sample 4 +
        4 * (sample 1 + sample 3) + 2 * sample 2) := by
  rfl

theorem gap15 :
    |simpsonApprox -
      2 / 3 * (4 + 4 * (1.732 + 2.646) + 2 * 2.236)| <
        0.02 := by
  rw [gap14, gap2, gap4, gap7, gap10, gap13]
  rcases abs_lt.mp gap5 with ⟨h3l, h3u⟩
  rcases abs_lt.mp gap8 with ⟨h5l, h5u⟩
  rcases abs_lt.mp gap11 with ⟨h7l, h7u⟩
  rw [abs_lt]
  constructor <;> norm_num at * <;> linarith

theorem gap16 :
    |(2 / 3 : ℝ) * (4 + 4 * (1.732 + 2.646) + 2 * 2.236) -
      17.323| < 0.001 := by
  norm_num [abs_lt]

theorem gap17 : |integralValue - 17.323| < 0.02 := by
  rw [integralValue_formula, nine_rpow_three_halves]
  norm_num [abs_lt]

theorem gap18 :
    integralValue =
      2 / 3 * (9 : ℝ) ^ (3 / 2 : ℝ) -
        2 / 3 * (1 : ℝ) ^ (3 / 2 : ℝ) := by
  exact integralValue_formula

theorem gap19 :
    2 / 3 * (9 : ℝ) ^ (3 / 2 : ℝ) -
      2 / 3 * (1 : ℝ) ^ (3 / 2 : ℝ) =
      52 / 3 := by
  rw [nine_rpow_three_halves]
  norm_num

theorem gap20 : |(52 / 3 : ℝ) - 17.333| < 0.001 := by
  norm_num [abs_lt]

theorem gap21 : |integralValue - 17.333| < 0.001 := by
  rw [gap18, gap19]
  exact gap20

end

end ProofGap.Exercise2535
