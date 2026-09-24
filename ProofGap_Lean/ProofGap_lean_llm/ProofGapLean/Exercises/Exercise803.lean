import ProofGapLean.Prelude.Core
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise803

noncomputable section

def square (x : ℝ) : ℝ := x ^ 2

def cell (n k : ℕ) : Set ℝ :=
  Set.Icc (1 + 9 * (k : ℝ) / (n : ℝ))
    (1 + 9 * ((k + 1 : ℕ) : ℝ) / (n : ℝ))

def GridOscillationSmall (n : ℕ) : Prop :=
  ∀ k < n, ∀ x₁ ∈ cell n k, ∀ x₂ ∈ cell n k,
    |square x₁ - square x₂| < 0.0001

/-- Exercise 803, gap 1; make the omitted equal-subinterval partition explicit. -/
theorem gap1 (n k : ℕ) (hn : 0 < n) (hk : k < n) :
    ∀ x₁ ∈ cell n k, ∀ x₂ ∈ cell n k,
      |x₁ - x₂| ≤ 9 / (n : ℝ) := by
  intro x₁ hx₁ x₂ hx₂
  simp only [cell, Set.mem_Icc] at hx₁ hx₂
  have hwidth :
      (1 + 9 * ((k + 1 : ℕ) : ℝ) / (n : ℝ)) -
          (1 + 9 * (k : ℝ) / (n : ℝ)) =
        9 / (n : ℝ) := by
    rw [Nat.cast_add, Nat.cast_one]
    ring
  rw [abs_le]
  constructor <;> linarith

/-- Exercise 803, gap 2; remove the irrelevant oscillation premise. -/
theorem gap2 (x₁ x₂ : ℝ) :
    |x₁ ^ 2 - x₂ ^ 2| = |x₁ + x₂| * |x₁ - x₂| := by
  calc
    |x₁ ^ 2 - x₂ ^ 2| = |(x₁ + x₂) * (x₁ - x₂)| := by
      congr 1
      ring
    _ = |x₁ + x₂| * |x₁ - x₂| := by
      rw [abs_mul]

/-- Exercise 803, gap 3; add the omitted interval and mesh hypotheses. -/
theorem gap3 (x₁ x₂ : ℝ) (n : ℕ)
    (hx₁ : x₁ ∈ Set.Icc (1 : ℝ) 10) (hx₂ : x₂ ∈ Set.Icc (1 : ℝ) 10)
    (hmesh : |x₁ - x₂| ≤ 9 / (n : ℝ)) :
    |x₁ + x₂| * |x₁ - x₂| ≤ ((10 + 10 : ℝ) * 9) / (n : ℝ) := by
  rcases hx₁ with ⟨hx₁l, hx₁u⟩
  rcases hx₂ with ⟨hx₂l, hx₂u⟩
  have hsum_nonneg : 0 ≤ x₁ + x₂ := by
    linarith
  have hsum : |x₁ + x₂| ≤ (20 : ℝ) := by
    rw [abs_of_nonneg hsum_nonneg]
    linarith
  calc
    |x₁ + x₂| * |x₁ - x₂| ≤ 20 * |x₁ - x₂| :=
      mul_le_mul_of_nonneg_right hsum (abs_nonneg _)
    _ ≤ 20 * (9 / (n : ℝ)) :=
      mul_le_mul_of_nonneg_left hmesh (by norm_num)
    _ = ((10 + 10 : ℝ) * 9) / (n : ℝ) := by
      ring

/-- Exercise 803, gap 4; remove the irrelevant oscillation premise. -/
theorem gap4 (n : ℕ) : ((10 + 10 : ℝ) * 9) / (n : ℝ) = 180 / (n : ℝ) := by
  ring

/-- Exercise 803, gap 5; add the omitted interval and mesh hypotheses. -/
theorem gap5 (x₁ x₂ : ℝ) (n : ℕ)
    (hx₁ : x₁ ∈ Set.Icc (1 : ℝ) 10) (hx₂ : x₂ ∈ Set.Icc (1 : ℝ) 10)
    (hmesh : |x₁ - x₂| ≤ 9 / (n : ℝ)) :
    |x₁ ^ 2 - x₂ ^ 2| ≤ 180 / (n : ℝ) := by
  calc
    |x₁ ^ 2 - x₂ ^ 2| = |x₁ + x₂| * |x₁ - x₂| := gap2 x₁ x₂
    _ ≤ ((10 + 10 : ℝ) * 9) / (n : ℝ) := gap3 x₁ x₂ n hx₁ hx₂ hmesh
    _ = 180 / (n : ℝ) := gap4 n

/-- Exercise 803, gap 6; bind the previously free natural `n`. -/
theorem gap6 (n : ℕ) (hn : 1800000 < n) :
    180 / (n : ℝ) < 0.0001 := by
  have hnR : (1800000 : ℝ) < (n : ℝ) := Nat.cast_lt.mpr hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    linarith
  rw [div_lt_iff₀ hnpos]
  norm_num at ⊢
  linarith

/-- Exercise 803, gap 7; state the numeric implication directly. -/
theorem gap7 (n : ℕ) (hn : 0 < n) (hsmall : 180 / (n : ℝ) < 0.0001) :
    1800000 < n := by
  have hnR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  rw [div_lt_iff₀ hnR] at hsmall
  norm_num at hsmall
  have hcast : (1800000 : ℝ) < (n : ℝ) := by
    linarith
  exact Nat.cast_lt.mp hcast

/-- Exercise 803, gap 8; correct `n≥1800000` to strict `n>1800000` and expose the grid. -/
theorem gap8 (n : ℕ) (hn : 1800000 < n) : GridOscillationSmall n := by
  unfold GridOscillationSmall
  intro k hk x₁ hx₁ x₂ hx₂
  have hnpos : 0 < n := lt_trans (by norm_num) hn
  have hnR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hnpos
  have hmesh : |x₁ - x₂| ≤ 9 / (n : ℝ) :=
    gap1 n k hnpos hk x₁ hx₁ x₂ hx₂
  have hkR : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hterm_nonneg :
      0 ≤ 9 * (k : ℝ) / (n : ℝ) := by
    exact div_nonneg (mul_nonneg (by norm_num) hkR) hnR.le
  have hlower :
      (1 : ℝ) ≤ 1 + 9 * (k : ℝ) / (n : ℝ) := by
    linarith
  have hkn : k + 1 ≤ n := Nat.succ_le_iff.mpr hk
  have hknR : ((k + 1 : ℕ) : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hkn
  have hterm_le :
      9 * ((k + 1 : ℕ) : ℝ) / (n : ℝ) ≤ 9 := by
    apply (div_le_iff₀ hnR).2
    nlinarith [hknR]
  have hupper :
      1 + 9 * ((k + 1 : ℕ) : ℝ) / (n : ℝ) ≤ (10 : ℝ) := by
    linarith
  simp only [cell, Set.mem_Icc] at hx₁ hx₂
  have hx₁I : x₁ ∈ Set.Icc (1 : ℝ) 10 :=
    ⟨le_trans hlower hx₁.1, le_trans hx₁.2 hupper⟩
  have hx₂I : x₂ ∈ Set.Icc (1 : ℝ) 10 :=
    ⟨le_trans hlower hx₂.1, le_trans hx₂.2 hupper⟩
  change |x₁ ^ 2 - x₂ ^ 2| < 0.0001
  exact lt_of_le_of_lt (gap5 x₁ x₂ n hx₁I hx₂I hmesh) (gap6 n hn)

end

end ProofGap.Exercise803
