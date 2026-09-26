import Mathlib

noncomputable section

namespace ProofGapBatch5

abbrev SeqR := ℕ → ℝ

def partialSum (a : SeqR) (n : ℕ) : ℝ :=
  Finset.sum (Finset.range (n + 1)) a

def powerSeriesSum (a : SeqR) (x : ℝ) : ℝ :=
  ∑' n : ℕ, a n * x ^ n

def geomPowerSeriesSum (x : ℝ) : ℝ :=
  ∑' n : ℕ, x ^ n

namespace exercise_2896

theorem proof_gap_exercise_2896_1
    (f F : ℝ → ℝ) (a : SeqR) (s : Set ℝ)
    (hf : ∀ x ∈ s, f x = powerSeriesSum a x)
    (hF : ∀ x : ℝ, x ≠ 1 → F x = f x / (1 - x)) :
    ∀ x : ℝ, x ∈ s ∧ x ≠ 1 →
      F x = powerSeriesSum a x * geomPowerSeriesSum x := by
  sorry

theorem proof_gap_exercise_2896_2
    (f F : ℝ → ℝ) (a : SeqR) (s : Set ℝ)
    (hf : ∀ x ∈ s, f x = powerSeriesSum a x)
    (hF : ∀ x : ℝ, x ≠ 1 → F x = f x / (1 - x))
    (hproduct : ∀ x : ℝ, x ∈ s ∧ x ≠ 1 →
      F x = powerSeriesSum a x * geomPowerSeriesSum x) :
    ∀ x : ℝ, x ∈ s ∧ x ≠ 1 →
      F x = powerSeriesSum (fun n => partialSum a n) x := by
  sorry

end exercise_2896

end ProofGapBatch5
