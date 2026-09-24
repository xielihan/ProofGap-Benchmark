import Mathlib

noncomputable section

open Filter Real
open scoped Topology

namespace Exercise2757

def f2757 (n : ℕ) (x : ℝ) : ℝ := Real.exp ((n : ℝ) * (x - 1))
def g2757 (x : ℝ) : ℝ := 0
def UniformOn (u : ℕ → ℝ → ℝ) (s : Set ℝ) (g : ℝ → ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ x ∈ s, |u n x - g x| < ε
def ConvergentSeqOn (u : ℕ → ℝ → ℝ) (s : Set ℝ) (g : ℝ → ℝ) : Prop :=
  ∀ x ∈ s, Tendsto (fun n : ℕ => u (n + 1) x) atTop (𝓝 (g x))

-- GAP 1
theorem proof_gap_exercise_2757_1 :
    ∀ x : ℝ, x ∈ Set.Ioo (0 : ℝ) 1 → Tendsto (fun n : ℕ => f2757 (n + 1) x) atTop (𝓝 0) := by
  sorry

-- GAP 2
theorem proof_gap_exercise_2757_2 :
    ∀ x : ℝ, x ∈ Set.Ioo (0 : ℝ) 1 → 0 = g2757 x := by
  sorry

-- GAP 3
theorem proof_gap_exercise_2757_3 :
    ∀ x : ℝ, x ∈ Set.Ioo (0 : ℝ) 1 → Tendsto (fun n : ℕ => f2757 (n + 1) x) atTop (𝓝 (g2757 x)) := by
  sorry

-- GAP 4
theorem proof_gap_exercise_2757_4 :
    ConvergentSeqOn f2757 (Set.Ioo (0 : ℝ) 1) g2757 := by
  sorry

-- GAP 5
theorem proof_gap_exercise_2757_5 (ε₀ : ℝ) (hε : ε₀ = 1 / (2 * Real.exp 1)) : 0 < ε₀ := by
  sorry

-- GAP 6
theorem proof_gap_exercise_2757_6 (ε₀ : ℝ) (hε : ε₀ = 1 / (2 * Real.exp 1)) :
    ε₀ < Real.exp (-1) := by
  sorry

-- GAP 7
theorem proof_gap_exercise_2757_7 : (0 : ℝ) < Real.exp (-1) := by
  sorry

-- GAP 8
theorem proof_gap_exercise_2757_8 :
    ∀ x : ℝ, ∀ n : ℕ, 0 < n → (1 : ℝ) < n → x = 1 - 1 / (n : ℝ) →
      x ∈ Set.Ioo (0 : ℝ) 1 := by
  sorry

-- GAP 9
theorem proof_gap_exercise_2757_9 :
    ∀ x : ℝ, ∀ n : ℕ, 0 < n → (1 : ℝ) < n → x = 1 - 1 / (n : ℝ) →
      |f2757 n x - g2757 x| = |f2757 n (1 - 1 / (n : ℝ)) - g2757 (1 - 1 / (n : ℝ))| := by
  sorry

-- GAP 10
theorem proof_gap_exercise_2757_10 :
    ∀ x : ℝ, ∀ n : ℕ, 0 < n → (1 : ℝ) < n → x = 1 - 1 / (n : ℝ) →
      |f2757 n (1 - 1 / (n : ℝ)) - g2757 (1 - 1 / (n : ℝ))| =
        Real.exp ((n : ℝ) * (1 - 1 / (n : ℝ) - 1)) := by
  sorry

-- GAP 11
theorem proof_gap_exercise_2757_11 :
    ∀ x : ℝ, ∀ n : ℕ, 0 < n → (1 : ℝ) < n → x = 1 - 1 / (n : ℝ) →
      Real.exp ((n : ℝ) * (1 - 1 / (n : ℝ) - 1)) = Real.exp (-1) := by
  sorry

-- GAP 12
theorem proof_gap_exercise_2757_12 (ε₀ : ℝ) (hε : ε₀ = 1 / (2 * Real.exp 1)) :
    ∀ x : ℝ, ∀ n : ℕ, 0 < n → (1 : ℝ) < n → x = 1 - 1 / (n : ℝ) →
      Real.exp (-1) > ε₀ := by
  sorry

-- GAP 13
theorem proof_gap_exercise_2757_13 (ε₀ : ℝ) (hε : ε₀ = 1 / (2 * Real.exp 1)) :
    ∀ x : ℝ, ∀ n : ℕ, 0 < n → (1 : ℝ) < n → x = 1 - 1 / (n : ℝ) →
      |f2757 n x - g2757 x| > ε₀ := by
  sorry

-- GAP 14
theorem proof_gap_exercise_2757_14 :
    ¬ UniformOn f2757 (Set.Ioo (0 : ℝ) 1) g2757 := by
  sorry

-- GAP 15
theorem proof_gap_exercise_2757_15 :
    ¬ (ConvergentSeqOn f2757 (Set.Ioo (0 : ℝ) 1) g2757 ∧
       UniformOn f2757 (Set.Ioo (0 : ℝ) 1) g2757) := by
  sorry

end Exercise2757

