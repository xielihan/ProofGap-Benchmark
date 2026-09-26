import Mathlib

noncomputable section

namespace ProofGapBatch5

abbrev SeqC := ℕ → ℂ

def complexSeqLimit (u : ℕ → ℝ) (L : ℝ) : Prop :=
  Tendsto u Filter.atTop (𝓝 L)

def HasComplexPowerSeriesRadius (c : SeqC) (R : ℝ) : Prop :=
  0 ≤ R ∧
    (∀ r : ℝ, 0 ≤ r → r < R → Summable (fun n : ℕ => ‖c n‖ * r ^ n)) ∧
    (∀ r : ℝ, R < r → ¬ Summable (fun n : ℕ => ‖c n‖ * r ^ n))

def complexSeriesFromOne (c : SeqC) (z : ℂ) : Prop :=
  Summable (fun n : ℕ => c (n + 1) * (z - 1 - Complex.I) ^ (n + 1))

namespace exercise_2916

variable (z : ℂ) (c : SeqC)

theorem proof_gap_exercise_2916_1
    (hc : ∀ n : ℕ, 0 < n → c n = (1 : ℂ) / ((n : ℂ) * (2 : ℂ) ^ n)) :
    complexSeqLimit (fun n : ℕ => ‖c n / c (n + 1)‖) 2 := by
  sorry

theorem proof_gap_exercise_2916_2
    (hc : ∀ n : ℕ, 0 < n → c n = (1 : ℂ) / ((n : ℂ) * (2 : ℂ) ^ n))
    (hratio : complexSeqLimit (fun n : ℕ => ‖c n / c (n + 1)‖) 2) :
    HasComplexPowerSeriesRadius c 2 := by
  sorry

theorem proof_gap_exercise_2916_3
    (hc : ∀ n : ℕ, 0 < n → c n = (1 : ℂ) / ((n : ℂ) * (2 : ℂ) ^ n))
    (hradius : HasComplexPowerSeriesRadius c 2) :
    complexSeriesFromOne c z ↔ ‖z - 1 - Complex.I‖ < 2 := by
  sorry

theorem proof_gap_exercise_2916_4
    (hconv : complexSeriesFromOne c z ↔ ‖z - 1 - Complex.I‖ < 2) :
    ∀ x y : ℝ, z = x + y * Complex.I →
      (‖z - 1 - Complex.I‖ < 2 ↔ (x - 1) ^ 2 + (y - 1) ^ 2 < 2 ^ 2) := by
  sorry

theorem proof_gap_exercise_2916_5
    (hdisc : ∀ x y : ℝ, z = x + y * Complex.I →
      (‖z - 1 - Complex.I‖ < 2 ↔ (x - 1) ^ 2 + (y - 1) ^ 2 < 2 ^ 2))
    (hconv : complexSeriesFromOne c z ↔ ‖z - 1 - Complex.I‖ < 2) :
    ({w : ℂ | ‖w - 1 - Complex.I‖ < 2} =
        {w : ℂ | ∃ x y : ℝ, w = x + y * Complex.I ∧
          (x - 1) ^ 2 + (y - 1) ^ 2 < 2 ^ 2}) ↔
      complexSeriesFromOne c z := by
  sorry

end exercise_2916

end ProofGapBatch5
