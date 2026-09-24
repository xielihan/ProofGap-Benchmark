import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Complex.Exponential

namespace ProofGap.Exercise1396_4

noncomputable section

def Approx (x y ε : ℝ) : Prop := |x - y| < ε
def expPartial (x : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), x ^ k / (Nat.factorial k : ℝ)
def remainder : ℝ := |Real.exp (1 / 2) - expPartial (1 / 2) 6|
def remainderBound : ℝ :=
  (1 / (Nat.factorial 7 : ℝ)) * (1 / 2 : ℝ) ^ 7 /
    (1 - (1 / 8 : ℝ) * (1 / 2 : ℝ))

private theorem exp_half_approximations :
    Approx (Real.exp (1 / 2)) (expPartial (1 / 2) 6)
        (2 / 1000000 : ℝ) ∧
      Approx (Real.exp (1 / 2)) 1.64872
        (2 / 1000000 : ℝ) := by
  let s9 : ℝ :=
    ∑ k ∈ Finset.range 9,
      (1 / 2 : ℝ) ^ k / (Nat.factorial k : ℝ)
  have hexp :
      |Real.exp (1 / 2) - s9| ≤
        |(1 / 2 : ℝ)| ^ 9 *
          ((10 : ℝ) / ((Nat.factorial 9 : ℝ) * 9)) := by
    simpa [s9] using
      (Real.exp_bound (x := (1 / 2 : ℝ)) (n := 9)
        (by norm_num) (by norm_num))
  constructor
  · unfold Approx
    calc
      |Real.exp (1 / 2) - expPartial (1 / 2) 6| ≤
          |Real.exp (1 / 2) - s9| +
            |s9 - expPartial (1 / 2) 6| :=
        abs_sub_le _ _ _
      _ < (2 / 1000000 : ℝ) := by
        norm_num [s9, expPartial, Finset.sum_range_succ] at hexp ⊢
        linarith
  · unfold Approx
    calc
      |Real.exp (1 / 2) - 1.64872| ≤
          |Real.exp (1 / 2) - s9| + |s9 - 1.64872| :=
        abs_sub_le _ _ _
      _ < (2 / 1000000 : ℝ) := by
        norm_num [s9, Finset.sum_range_succ] at hexp ⊢
        linarith

theorem gap1 :
    Approx (Real.sqrt (Real.exp 1)) (expPartial (1 / 2) 6)
      (2 / 1000000 : ℝ) := by
  rw [← Real.exp_half 1]
  exact exp_half_approximations.1
theorem gap2 :
    Approx (expPartial (1 / 2) 6) 1.64872 (1 / 1000000 : ℝ) := by
  norm_num [Approx, expPartial, Finset.sum_range_succ, abs_lt]
theorem gap3 :
    Approx (Real.sqrt (Real.exp 1)) 1.64872 (2 / 1000000 : ℝ) := by
  rw [← Real.exp_half 1]
  exact exp_half_approximations.2
theorem gap4 : ∃ Δ : ℝ, Δ = remainder := by
  exact ⟨remainder, rfl⟩
theorem gap5 : remainder < remainderBound := by
  let s9 : ℝ :=
    ∑ k ∈ Finset.range 9,
      (1 / 2 : ℝ) ^ k / (Nat.factorial k : ℝ)
  have hexp :
      |Real.exp (1 / 2) - s9| ≤
        |(1 / 2 : ℝ)| ^ 9 *
          ((10 : ℝ) / ((Nat.factorial 9 : ℝ) * 9)) := by
    simpa [s9] using
      (Real.exp_bound (x := (1 / 2 : ℝ)) (n := 9)
        (by norm_num) (by norm_num))
  have htail :
      s9 - expPartial (1 / 2) 6 =
        (1 / 2 : ℝ) ^ 7 / (Nat.factorial 7 : ℝ) +
          (1 / 2 : ℝ) ^ 8 / (Nat.factorial 8 : ℝ) := by
    norm_num [s9, expPartial, Finset.sum_range_succ]
  unfold remainder
  calc
    |Real.exp (1 / 2) - expPartial (1 / 2) 6| =
        |(Real.exp (1 / 2) - s9) +
          (s9 - expPartial (1 / 2) 6)| := by ring_nf
    _ ≤ |Real.exp (1 / 2) - s9| +
        |s9 - expPartial (1 / 2) 6| := abs_add_le _ _
    _ ≤
        |(1 / 2 : ℝ)| ^ 9 *
            ((10 : ℝ) / ((Nat.factorial 9 : ℝ) * 9)) +
          |s9 - expPartial (1 / 2) 6| :=
      by
        simpa [add_comm] using
          add_le_add_right hexp |s9 - expPartial (1 / 2) 6|
    _ < remainderBound := by
      rw [htail]
      norm_num [remainderBound, abs_of_nonneg]
theorem gap6 :
    Approx remainderBound (1.7 * 10 ^ (-6 : ℤ)) (1 / 10000000 : ℝ) := by
  norm_num [Approx, remainderBound, abs_lt]

end
end ProofGap.Exercise1396_4
