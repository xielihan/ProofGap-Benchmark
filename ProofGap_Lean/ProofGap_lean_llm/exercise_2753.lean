import Mathlib

noncomputable section

open Filter Real
open scoped Topology

namespace Exercise2753

def f2753 (n : ℕ) (x : ℝ) : ℝ := Real.sqrt (x^2 + 1 / (n : ℝ)^2)
def g2753 (x : ℝ) : ℝ := |x|
def UniformOn (u : ℕ → ℝ → ℝ) (s : Set ℝ) (g : ℝ → ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ x ∈ s, |u n x - g x| < ε

-- GAP 1
theorem proof_gap_exercise_2753_1 :
    ∀ x : ℝ, Tendsto (fun n : ℕ => f2753 (n + 1) x) atTop (𝓝 (g2753 x)) := by
  sorry

-- GAP 2
theorem proof_gap_exercise_2753_2 :
    ∀ n : ℕ, 0 < n → ∀ x : ℝ,
      |f2753 n x - g2753 x| =
        (x^2 + 1 / (n : ℝ)^2 - x^2) / (Real.sqrt (x^2 + 1 / (n : ℝ)^2) + |x|) := by
  sorry

-- GAP 3
theorem proof_gap_exercise_2753_3 :
    ∀ x : ℝ, ∀ n : ℕ, 0 < n →
      (x^2 + 1 / (n : ℝ)^2 - x^2) / (Real.sqrt (x^2 + 1 / (n : ℝ)^2) + |x|)
        < (1 / (n : ℝ)^2) / (1 / (n : ℝ)) := by
  sorry

-- GAP 4
theorem proof_gap_exercise_2753_4 :
    ∀ n : ℕ, 0 < n → (1 / (n : ℝ)^2) / (1 / (n : ℝ)) = 1 / (n : ℝ) := by
  sorry

-- GAP 5
theorem proof_gap_exercise_2753_5 :
    ∀ n : ℕ, 0 < n → ∀ x : ℝ, |f2753 n x - g2753 x| < 1 / (n : ℝ) := by
  sorry

-- GAP 6
theorem proof_gap_exercise_2753_6 :
    ∀ n : ℕ, 0 < n → ∀ x : ℝ, ∀ ε : ℝ, 0 < ε → 1 / (n : ℝ) < ε →
      |f2753 n x - g2753 x| < ε := by
  sorry

-- GAP 7
theorem proof_gap_exercise_2753_7 :
    ∀ n : ℕ, 0 < n → ∀ ε : ℝ, 0 < ε → (n : ℝ) > 1 / ε → 1 / (n : ℝ) < ε := by
  sorry

-- GAP 8
theorem proof_gap_exercise_2753_8 :
    ∀ n : ℕ, 0 < n → ∀ x ε : ℝ, 0 < ε → (n : ℝ) > 1 / ε →
      |f2753 n x - g2753 x| < ε := by
  sorry

-- GAP 9
theorem proof_gap_exercise_2753_9 :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, (N : ℝ) = Nat.floor (1 / ε) := by
  sorry

-- GAP 10
theorem proof_gap_exercise_2753_10 :
    ∀ n N : ℕ, ∀ x ε : ℝ, 0 < ε → n > N → 0 < n → (N : ℝ) = Nat.floor (1 / ε) →
      |f2753 n x - g2753 x| < ε := by
  sorry

-- GAP 11
theorem proof_gap_exercise_2753_11 :
    UniformOn f2753 Set.univ g2753 := by
  sorry

-- GAP 12
theorem proof_gap_exercise_2753_12 (C : ℝ) :
    C = 1 → C = 1 := by
  sorry

end Exercise2753

