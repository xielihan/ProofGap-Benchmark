import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3003

noncomputable section

def coefficient (n : ℕ) : ℝ :=
  (n : ℝ) ^ 3 / (Nat.factorial (n + 1) : ℝ)

def splitCoefficient (n : ℕ) : ℝ :=
  1 / (Nat.factorial (n - 2) : ℝ) +
    1 / (Nat.factorial n : ℝ) -
    1 / (Nat.factorial (n + 1) : ℝ)

def alternatingSeries (x : ℝ) : ℝ :=
  ∑' n : ℕ,
    (-1 : ℝ) ^ n * coefficient n * x ^ n

def negativePowerSeries (x : ℝ) : ℝ :=
  ∑' n : ℕ, coefficient n * (-x) ^ n

def firstTail (x : ℝ) : ℝ :=
  ∑' k : ℕ,
    (-x) ^ (k + 2) / (Nat.factorial k : ℝ)

def secondTail (x : ℝ) : ℝ :=
  ∑' k : ℕ,
    (-x) ^ (k + 2) / (Nat.factorial (k + 2) : ℝ)

def thirdTail (x : ℝ) : ℝ :=
  ∑' k : ℕ,
    (-x) ^ (k + 2) / (Nat.factorial (k + 3) : ℝ)

def shiftedFirstTail (x : ℝ) : ℝ :=
  ∑' k : ℕ,
    (-x) ^ k / (Nat.factorial k : ℝ)

def shiftedThirdTail (x : ℝ) : ℝ :=
  ∑' k : ℕ,
    (-x) ^ (k + 3) / (Nat.factorial (k + 3) : ℝ)

private theorem real_exp_hasSum (x : ℝ) :
    HasSum (fun n : ℕ => x ^ n / (Nat.factorial n : ℝ)) (Real.exp x) := by
  simpa [Real.exp_eq_exp_ℝ] using
    (NormedSpace.expSeries_div_hasSum_exp x)

private theorem shiftedFirstTail_eq_exp (x : ℝ) :
    shiftedFirstTail x = Real.exp (-x) := by
  rw [shiftedFirstTail]
  exact (real_exp_hasSum (-x)).tsum_eq

private theorem secondTail_eq_exp (x : ℝ) :
    secondTail x = Real.exp (-x) - 1 + x := by
  rw [secondTail]
  have htail := (hasSum_nat_add_iff' 2).2 (real_exp_hasSum (-x))
  convert htail.tsum_eq using 1 <;>
    norm_num [Finset.sum_range_succ] <;> ring

private theorem shiftedThirdTail_eq_exp (x : ℝ) :
    shiftedThirdTail x = Real.exp (-x) - 1 + x - x ^ 2 / 2 := by
  rw [shiftedThirdTail]
  have htail := (hasSum_nat_add_iff' 3).2 (real_exp_hasSum (-x))
  convert htail.tsum_eq using 1 <;>
    norm_num [Finset.sum_range_succ] <;> ring

private theorem firstTail_eq_shifted (x : ℝ) :
    firstTail x = x ^ 2 * shiftedFirstTail x := by
  rw [firstTail, shiftedFirstTail, ← tsum_mul_left]
  apply tsum_congr
  intro k
  rw [pow_add]
  norm_num
  ring

private theorem neg_thirdTail_eq_shifted (x : ℝ) (hx : x ≠ 0) :
    -thirdTail x = 1 / x * shiftedThirdTail x := by
  rw [thirdTail, shiftedThirdTail, ← tsum_neg, ← tsum_mul_left]
  apply tsum_congr
  intro k
  have hp :
      (-x) ^ (k + 3) = (-x) ^ (k + 2) * (-x) := by
    rw [show k + 3 = (k + 2) + 1 by rfl, pow_succ]
  rw [hp]
  field_simp [hx]

theorem gap1 :
    ∀ n : ℕ, 2 ≤ n → coefficient n = splitCoefficient n := by
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [Nat.add_comm 2 k]
  rw [coefficient, splitCoefficient]
  simp only [Nat.add_sub_cancel, Nat.factorial_succ]
  push_cast
  field_simp
  ring

theorem gap2 :
    ∀ x, alternatingSeries x = negativePowerSeries x := by
  intro x
  rw [alternatingSeries, negativePowerSeries]
  apply tsum_congr
  intro n
  rw [neg_pow]
  ring

theorem gap3 :
    ∀ x,
      negativePowerSeries x =
        -(x / 2) + firstTail x + secondTail x - thirdTail x := by
  intro x
  by_cases hx : x = 0
  · subst x
    have hz :
        (fun n : ℕ => coefficient n * (-(0 : ℝ)) ^ n) = 0 := by
      funext n
      cases n <;> simp [coefficient]
    rw [negativePowerSeries, hz]
    simp [firstTail, secondTail, thirdTail]
    exact (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℝ)) 0).tsum_eq
  · have hbase :
        Summable (fun n : ℕ =>
          (-x) ^ n / (Nat.factorial n : ℝ)) :=
      (real_exp_hasSum (-x)).summable
    have hfirst :
        Summable (fun k : ℕ =>
          (-x) ^ (k + 2) / (Nat.factorial k : ℝ)) := by
      have h := hbase.mul_left (x ^ 2)
      refine h.congr (fun k => ?_)
      rw [pow_add]
      norm_num
      ring
    have hsecond :
        Summable (fun k : ℕ =>
          (-x) ^ (k + 2) / (Nat.factorial (k + 2) : ℝ)) := by
      simpa using (summable_nat_add_iff 2).2 hbase
    have hshiftedThird :
        Summable (fun k : ℕ =>
          (-x) ^ (k + 3) / (Nat.factorial (k + 3) : ℝ)) := by
      simpa using (summable_nat_add_iff 3).2 hbase
    have hthird :
        Summable (fun k : ℕ =>
          (-x) ^ (k + 2) / (Nat.factorial (k + 3) : ℝ)) := by
      have h := hshiftedThird.mul_left ((-x)⁻¹)
      refine h.congr (fun k => ?_)
      have hp :
          (-x) ^ (k + 3) = (-x) ^ (k + 2) * (-x) := by
        rw [show k + 3 = (k + 2) + 1 by rfl, pow_succ]
      rw [hp]
      field_simp [hx]
    have hparts :
        HasSum
          (fun k : ℕ =>
            (-x) ^ (k + 2) / (Nat.factorial k : ℝ) +
              (-x) ^ (k + 2) / (Nat.factorial (k + 2) : ℝ) -
              (-x) ^ (k + 2) / (Nat.factorial (k + 3) : ℝ))
          (firstTail x + secondTail x - thirdTail x) := by
      simpa [firstTail, secondTail, thirdTail] using
        (hfirst.hasSum.add hsecond.hasSum).sub hthird.hasSum
    have htail :
        HasSum
          (fun k : ℕ => coefficient (k + 2) * (-x) ^ (k + 2))
          (firstTail x + secondTail x - thirdTail x) := by
      apply hparts.congr_fun
      intro k
      rw [gap1 (k + 2)
        (by simpa [Nat.add_comm] using Nat.le_add_left 2 k)]
      simp only [splitCoefficient, Nat.add_sub_cancel]
      ring
    have hfull :
        HasSum (fun n : ℕ => coefficient n * (-x) ^ n)
          (-(x / 2) + firstTail x + secondTail x - thirdTail x) := by
      apply (hasSum_nat_add_iff' 2).mp
      convert htail using 1 <;>
        norm_num [coefficient, Finset.sum_range_succ] <;> ring
    rw [negativePowerSeries]
    exact hfull.tsum_eq

theorem gap4 :
    ∀ x, x ≠ 0 →
      negativePowerSeries x =
        -(x / 2) +
          x ^ 2 * shiftedFirstTail x +
          secondTail x +
          1 / x * shiftedThirdTail x := by
  intro x hx
  rw [gap3 x, firstTail_eq_shifted, sub_eq_add_neg,
    neg_thirdTail_eq_shifted x hx]

theorem gap5 :
    ∀ x, x ≠ 0 →
      alternatingSeries x =
        -(x / 2) +
          x ^ 2 * Real.exp (-x) +
          Real.exp (-x) - 1 + x +
          1 / x * (Real.exp (-x) - 1 + x - x ^ 2 / 2) := by
  intro x hx
  rw [gap2 x, gap4 x hx, shiftedFirstTail_eq_exp,
    secondTail_eq_exp, shiftedThirdTail_eq_exp]
  ring

theorem gap6 :
    ∀ x, x ≠ 0 →
      alternatingSeries x =
        Real.exp (-x) * (x ^ 2 + 1 + 1 / x) - 1 / x := by
  intro x hx
  rw [gap5 x hx]
  field_simp [hx]
  ring

end

end ProofGap.Exercise3003
