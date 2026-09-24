import Mathlib

noncomputable section

open Filter Real
open scoped Topology

namespace Exercise2752

def f2752 (n : ℕ) (x : ℝ) : ℝ := (2 * (n : ℝ) * x) / (1 + (n : ℝ)^2 * x^2)
def g2752 (x : ℝ) : ℝ := 0
def UniformOn (u : ℕ → ℝ → ℝ) (s : Set ℝ) (g : ℝ → ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ x ∈ s, |u n x - g x| < ε
def NonUniformWitness (u : ℕ → ℝ → ℝ) (s : Set ℝ) (g : ℝ → ℝ) (ε₀ : ℝ) : Prop :=
  0 < ε₀ ∧ ∀ N : ℕ, ∃ n > N, ∃ x ∈ s, |u n x - g x| > ε₀

-- GAP 1: pointwise limit on [0,1].
theorem proof_gap_exercise_2752_1 :
    ∀ x : ℝ, x ∈ Set.Icc (0 : ℝ) 1 → Tendsto (fun n : ℕ => f2752 (n + 1) x) atTop (𝓝 0) := by
  sorry

-- GAP 2: ε₀ = 1/2 is positive.
theorem proof_gap_exercise_2752_2 (ε₀ : ℝ) (hε : ε₀ = (1 / 2 : ℝ)) : 0 < ε₀ := by
  sorry

-- GAP 3: ε₀ = 1/2 is less than 1.
theorem proof_gap_exercise_2752_3 (ε₀ : ℝ) (hε : ε₀ = (1 / 2 : ℝ)) : ε₀ < 1 := by
  sorry

-- GAP 4: positivity of 1.
theorem proof_gap_exercise_2752_4 : (0 : ℝ) < 1 := by
  sorry

-- GAP 5: counterexample value x = 1/n gives error 1.
theorem proof_gap_exercise_2752_5 (ε₀ : ℝ) (hε : ε₀ = (1 / 2 : ℝ)) :
    ∀ n : ℕ, 0 < n →
      (1 / (n : ℝ)) ∈ Set.Icc (0 : ℝ) 1 ∧
      |f2752 n (1 / (n : ℝ)) - g2752 (1 / (n : ℝ))| = 1 ∧
      1 > ε₀ := by
  sorry

-- GAP 6: non-uniform convergence witness on [0,1].
theorem proof_gap_exercise_2752_6 :
    ∃ ε₀ : ℝ, NonUniformWitness f2752 (Set.Icc (0 : ℝ) 1) g2752 ε₀ := by
  sorry

-- GAP 7: pointwise limit on (1,+∞).
theorem proof_gap_exercise_2752_7 :
    ∀ x : ℝ, x ∈ Set.Ioi (1 : ℝ) → Tendsto (fun n : ℕ => f2752 (n + 1) x) atTop (𝓝 0) := by
  sorry

-- GAP 8: exact formula implies ε-bound.
theorem proof_gap_exercise_2752_8 :
    ∀ n : ℕ, 0 < n → ∀ x : ℝ, x ∈ Set.Ioi (1 : ℝ) →
      ∀ ε : ℝ, 0 < ε → (2 * (n : ℝ) * x) / (1 + (n : ℝ)^2 * x^2) < ε →
        |f2752 n x - g2752 x| < ε := by
  sorry

-- GAP 9: comparison with 2/n on x>1.
theorem proof_gap_exercise_2752_9 :
    ∀ n : ℕ, 0 < n → ∀ x : ℝ, x ∈ Set.Ioi (1 : ℝ) →
      ∀ ε : ℝ, 0 < ε → (2 : ℝ) / n < ε →
        (2 * (n : ℝ) * x) / (1 + (n : ℝ)^2 * x^2) < ε := by
  sorry

-- GAP 10: n > 2/ε implies 2/n < ε.
theorem proof_gap_exercise_2752_10 :
    ∀ n : ℕ, 0 < n → ∀ ε : ℝ, 0 < ε → (n : ℝ) > 2 / ε → (2 : ℝ) / n < ε := by
  sorry

-- GAP 11: uniform ε-bound from n > 2/ε.
theorem proof_gap_exercise_2752_11 :
    ∀ n : ℕ, 0 < n → ∀ x : ℝ, x ∈ Set.Ioi (1 : ℝ) →
      ∀ ε : ℝ, 0 < ε → (n : ℝ) > 2 / ε → |f2752 n x - g2752 x| < ε := by
  sorry

-- GAP 12: floor choice for 2/ε.
theorem proof_gap_exercise_2752_12 :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, (N : ℝ) = Nat.floor (2 / ε) := by
  sorry

-- GAP 13: absolute difference equals the displayed formula for x>1.
theorem proof_gap_exercise_2752_13 :
    ∀ n N : ℕ, ∀ x : ℝ, 0 < n → x ∈ Set.Ioi (1 : ℝ) →
      |f2752 n x - g2752 x| = (2 * (n : ℝ) * x) / (1 + (n : ℝ)^2 * x^2) := by
  sorry

-- GAP 14: displayed formula is bounded by 2/n.
theorem proof_gap_exercise_2752_14 :
    ∀ n N : ℕ, ∀ x : ℝ, 0 < n → x ∈ Set.Ioi (1 : ℝ) →
      (2 * (n : ℝ) * x) / (1 + (n : ℝ)^2 * x^2) < (2 : ℝ) / n := by
  sorry

-- GAP 15: n>N with N=floor(2/ε) yields 2/n<ε.
theorem proof_gap_exercise_2752_15 :
    ∀ n N : ℕ, ∀ ε : ℝ, 0 < ε → (N : ℝ) = Nat.floor (2 / ε) → n > N → 0 < n →
      (2 : ℝ) / n < ε := by
  sorry

-- GAP 16: combine the previous estimates.
theorem proof_gap_exercise_2752_16 :
    ∀ n N : ℕ, ∀ x ε : ℝ, 0 < ε → n > N → 0 < n → x ∈ Set.Ioi (1 : ℝ) →
      (N : ℝ) = Nat.floor (2 / ε) → |f2752 n x - g2752 x| < ε := by
  sorry

-- GAP 17: uniform convergence on (1,+∞).
theorem proof_gap_exercise_2752_17 :
    UniformOn f2752 (Set.Ioi (1 : ℝ)) g2752 := by
  sorry

-- GAP 18: source terminal statement C=(0,1)=>C=0 is type-inconsistent; preserved as impossible real equality schema.
theorem proof_gap_exercise_2752_18 (C : ℝ) :
    C = 0 → C = 0 := by
  sorry

end Exercise2752

