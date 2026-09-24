import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Complex.ExponentialBounds

namespace ProofGap.Exercise2931_2

noncomputable section

open scoped BigOperators

def logIncrementTerm (k : ℕ) : ℝ :=
  1 /
    (((2 * k + 1 : ℕ) : ℝ) * (5 : ℝ) ^ (2 * k + 1))

def incrementPartial : ℝ :=
  2 * ∑ k ∈ Finset.range 5, logIncrementTerm k

def Approx (u v ε : ℝ) : Prop :=
  |u - v| < ε

theorem gap1 :
    Real.log 3 =
      Real.log 2 + 2 * ∑' k : ℕ, logIncrementTerm k := by
  have hs := Real.hasSum_log_one_add_inv (a := (2 : ℝ)) (by norm_num)
  have hs' :
      HasSum (fun k : ℕ => 2 * logIncrementTerm k)
        (Real.log (1 + (2 : ℝ)⁻¹)) := by
    convert hs using 1
    funext k
    simp only [logIncrementTerm]
    norm_num
    simp [one_div, mul_comm, mul_assoc]
  rw [← tsum_mul_left, hs'.tsum_eq]
  rw [← Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
      (by norm_num : (1 + (2 : ℝ)⁻¹) ≠ 0)]
  norm_num

theorem gap2 :
    Approx incrementPartial (405465 / 1000000 : ℝ)
      (1 / 10 ^ 6 : ℝ) := by
  norm_num [Approx, incrementPartial, logIncrementTerm, Finset.sum_range_succ]

theorem gap3 :
    Approx (Real.log 3)
      ((693146 + 405465) / 1000000 : ℝ)
      (2 / 10 ^ 6 : ℝ) := by
  have htail := Real.sum_range_sub_log_div_le
    (x := (1 / 5 : ℝ)) (by norm_num) 5
  norm_num [Finset.sum_range_succ] at htail
  have htail' := abs_le.mp htail
  have hlog :
      Real.log 3 = Real.log 2 + Real.log (3 / 2 : ℝ) := by
    calc
      Real.log 3 = Real.log ((2 : ℝ) * (3 / 2 : ℝ)) := by norm_num
      _ = Real.log 2 + Real.log (3 / 2 : ℝ) :=
        Real.log_mul (by norm_num) (by norm_num)
  unfold Approx
  rw [hlog, abs_lt]
  constructor <;>
    norm_num at htail' ⊢ <;>
    linarith [Real.log_two_gt_d9, Real.log_two_lt_d9]

theorem gap4 :
    ((693146 + 405465) / 1000000 : ℝ) =
      1098611 / 1000000 := by
  norm_num

theorem gap5 :
    Approx (Real.log 3) (109861 / 100000 : ℝ)
      (1 / 10 ^ 5 : ℝ) := by
  have h := gap3
  unfold Approx at h ⊢
  rw [abs_lt] at h ⊢
  norm_num at h ⊢
  constructor <;> linarith

theorem gap6 :
    Approx (Real.log 3)
      ((69315 + 40546) / 100000 : ℝ)
      (1 / 10 ^ 5 : ℝ) := by
  convert gap5 using 1
  norm_num

theorem gap7 :
    ((69315 + 40546) / 100000 : ℝ) =
      109861 / 100000 := by
  norm_num

theorem gap8 :
    Approx (Real.log 3) (109861 / 100000 : ℝ)
      (1 / 10 ^ 5 : ℝ) := by
  exact gap5

end

end ProofGap.Exercise2931_2
