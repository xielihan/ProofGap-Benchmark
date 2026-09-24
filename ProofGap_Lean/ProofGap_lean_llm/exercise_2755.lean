import Mathlib

noncomputable section

open Filter Real
open scoped Topology

namespace Exercise2755

def f2755 (n : ℕ) (x : ℝ) : ℝ := Real.sin ((n : ℝ) * x) / (n : ℝ)
def h2755 (n : ℕ) (x : ℝ) : ℝ := Real.sin (x / (n : ℝ))
def g2755 (x : ℝ) : ℝ := 0
def UniformOn (u : ℕ → ℝ → ℝ) (s : Set ℝ) (g : ℝ → ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ x ∈ s, |u n x - g x| < ε
def NonUniformWitness (u : ℕ → ℝ → ℝ) (s : Set ℝ) (g : ℝ → ℝ) (ε₀ : ℝ) : Prop :=
  0 < ε₀ ∧ ∀ N : ℕ, ∃ n > N, ∃ x ∈ s, |u n x - g x| > ε₀

-- GAP 1
theorem proof_gap_exercise_2755_1 :
    ∀ x : ℝ, Tendsto (fun n : ℕ => f2755 (n + 1) x) atTop (𝓝 (g2755 x)) := by
  sorry

-- GAP 2
theorem proof_gap_exercise_2755_2 :
    ∀ n : ℕ, 0 < n → ∀ x : ℝ, |f2755 n x - g2755 x| = |Real.sin ((n : ℝ) * x)| / (n : ℝ) := by
  sorry

-- GAP 3
theorem proof_gap_exercise_2755_3 :
    ∀ n : ℕ, 0 < n → ∀ x : ℝ, |Real.sin ((n : ℝ) * x)| / (n : ℝ) ≤ 1 / (n : ℝ) := by
  sorry

-- GAP 4
theorem proof_gap_exercise_2755_4 :
    ∀ n : ℕ, 0 < n → ∀ x : ℝ, |f2755 n x - g2755 x| ≤ 1 / (n : ℝ) := by
  sorry

-- GAP 5
theorem proof_gap_exercise_2755_5 :
    ∀ n : ℕ, 0 < n → ∀ x ε : ℝ, 0 < ε → 1 / (n : ℝ) < ε →
      |f2755 n x - g2755 x| < ε := by
  sorry

-- GAP 6
theorem proof_gap_exercise_2755_6 :
    ∀ n : ℕ, 0 < n → ∀ ε : ℝ, 0 < ε → (n : ℝ) > 1 / ε → 1 / (n : ℝ) < ε := by
  sorry

-- GAP 7
theorem proof_gap_exercise_2755_7 :
    ∀ n : ℕ, 0 < n → ∀ x ε : ℝ, 0 < ε → (n : ℝ) > 1 / ε →
      |f2755 n x - g2755 x| < ε := by
  sorry

-- GAP 8
theorem proof_gap_exercise_2755_8 :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, (N : ℝ) = Nat.floor (1 / ε) := by
  sorry

-- GAP 9
theorem proof_gap_exercise_2755_9 :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, 0 < n → n > N → ∀ x : ℝ,
      |f2755 n x - g2755 x| < ε := by
  sorry

-- GAP 10
theorem proof_gap_exercise_2755_10 :
    UniformOn f2755 Set.univ g2755 := by
  sorry

-- GAP 11
theorem proof_gap_exercise_2755_11 :
    ∀ x : ℝ, Tendsto (fun n : ℕ => h2755 (n + 1) x) atTop (𝓝 (g2755 x)) := by
  sorry

-- GAP 12
theorem proof_gap_exercise_2755_12 (ε₀ : ℝ) (hε : ε₀ = (1 / 2 : ℝ)) : 0 < ε₀ := by
  sorry

-- GAP 13
theorem proof_gap_exercise_2755_13 (ε₀ : ℝ) (hε : ε₀ = (1 / 2 : ℝ)) : ε₀ < 1 := by
  sorry

-- GAP 14
theorem proof_gap_exercise_2755_14 : (0 : ℝ) < 1 := by
  sorry

-- GAP 15
theorem proof_gap_exercise_2755_15 (ε₀ : ℝ) (hε : ε₀ = (1 / 2 : ℝ)) :
    ∀ n : ℕ, 0 < n →
      ((n : ℝ) * Real.pi / 2) ∈ (Set.univ : Set ℝ) ∧
      |h2755 n ((n : ℝ) * Real.pi / 2) - g2755 ((n : ℝ) * Real.pi / 2)| = 1 ∧
      1 > ε₀ := by
  sorry

-- GAP 16
theorem proof_gap_exercise_2755_16 :
    ∃ ε₀ : ℝ, NonUniformWitness h2755 Set.univ g2755 ε₀ := by
  sorry

-- GAP 17
theorem proof_gap_exercise_2755_17 :
    ¬ UniformOn h2755 Set.univ g2755 := by
  sorry

end Exercise2755

