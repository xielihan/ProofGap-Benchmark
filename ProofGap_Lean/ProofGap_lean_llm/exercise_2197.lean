import Mathlib

noncomputable section

namespace Exercise2197

abbrev RealSet := Set ℝ
def RationalSet : Set ℝ := {x | ∃ q : ℚ, (q : ℝ) = x}
def NonNegIntegerSet : Set ℕ := Set.univ
def Icc (a b : ℝ) : Set ℝ := Set.Icc a b

axiom OscillationOn : (ℝ → ℝ) → Set ℝ → ℝ
axiom IntegrableFuncOn : (ℝ → ℝ) → Set ℝ → Prop
axiom sumOsc : (ℕ → ℝ) → (ℕ → ℝ) → ℕ → ℝ
axiom sumLen : (ℕ → ℝ) → ℕ → ℝ
axiom meshLimitNotZero : (ℕ → ℝ) → (ℕ → ℝ) → ℕ → Prop

-- Exercise 2197, gap 1
theorem proof_gap_exercise_2197_1
    (χ : ℝ → ℝ) (ω Δx : ℕ → ℝ)
    (hirr : ∀ x : ℝ, x ∈ (Set.univ : RealSet) ∧ x ∉ RationalSet → χ x = 0)
    (hrat : ∀ x : ℝ, x ∈ (Set.univ : RealSet) ∧ x ∈ RationalSet → χ x = 1) :
    ∀ a : ℝ, a ∈ (Set.univ : RealSet) →
      ∀ b : ℝ, a ∈ (Set.univ : RealSet) ∧ b ∈ (Set.univ : RealSet) ∧ a < b →
        ∀ α β : ℝ, α ∈ (Set.univ : RealSet) ∧ β ∈ (Set.univ : RealSet) ∧
          a ≤ α ∧ α < β ∧ β ≤ b → OscillationOn χ (Icc α β) = 1 := by
  sorry

-- Exercise 2197, gap 2
theorem proof_gap_exercise_2197_2
    (χ : ℝ → ℝ) (ω Δx : ℕ → ℝ)
    (hosc : ∀ a : ℝ, a ∈ (Set.univ : RealSet) →
      ∀ b : ℝ, a ∈ (Set.univ : RealSet) ∧ b ∈ (Set.univ : RealSet) ∧ a < b →
        ∀ α β : ℝ, α ∈ (Set.univ : RealSet) ∧ β ∈ (Set.univ : RealSet) ∧
          a ≤ α ∧ α < β ∧ β ≤ b → OscillationOn χ (Icc α β) = 1) :
    ∀ n : ℕ, n ∈ NonNegIntegerSet ∧ n > 0 →
      ∀ a : ℝ, a ∈ (Set.univ : RealSet) →
        ∀ b : ℝ, a ∈ (Set.univ : RealSet) ∧ b ∈ (Set.univ : RealSet) ∧ a < b →
          ∀ i : ℤ, i ∈ (Set.univ : Set ℤ) ∧ 0 ≤ i ∧ i ≤ (n : ℤ) - 1 →
            ω i.toNat = 1 := by
  sorry

-- Exercise 2197, gap 3
theorem proof_gap_exercise_2197_3
    (ω Δx : ℕ → ℝ) :
    ∀ i : ℤ, i ∈ (Set.univ : Set ℤ) →
      ∀ n : ℕ, n ∈ NonNegIntegerSet ∧ n > 0 →
        ∀ a : ℝ, a ∈ (Set.univ : RealSet) →
          ∀ b : ℝ, a ∈ (Set.univ : RealSet) ∧ b ∈ (Set.univ : RealSet) ∧ a < b →
            sumOsc ω Δx n = sumLen Δx n := by
  sorry

-- Exercise 2197, gap 4
theorem proof_gap_exercise_2197_4
    (ω Δx : ℕ → ℝ) :
    ∀ i : ℤ, i ∈ (Set.univ : Set ℤ) →
      ∀ n : ℕ, n ∈ NonNegIntegerSet ∧ n > 0 →
        ∀ a : ℝ, a ∈ (Set.univ : RealSet) →
          ∀ b : ℝ, a ∈ (Set.univ : RealSet) ∧ b ∈ (Set.univ : RealSet) ∧ a < b →
            sumLen Δx n = b - a := by
  sorry

-- Exercise 2197, gap 5
theorem proof_gap_exercise_2197_5
    (ω Δx : ℕ → ℝ) :
    ∀ i : ℤ, i ∈ (Set.univ : Set ℤ) →
      ∀ n : ℕ, n ∈ NonNegIntegerSet ∧ n > 0 →
        ∀ a : ℝ, a ∈ (Set.univ : RealSet) →
          ∀ b : ℝ, a ∈ (Set.univ : RealSet) ∧ b ∈ (Set.univ : RealSet) ∧ a < b →
            sumOsc ω Δx n = b - a := by
  sorry

-- Exercise 2197, gap 6
theorem proof_gap_exercise_2197_6
    (ω Δx : ℕ → ℝ) :
    ∀ i : ℤ, i ∈ (Set.univ : Set ℤ) →
      ∀ n : ℕ, n ∈ NonNegIntegerSet ∧ n > 0 →
        ∀ a : ℝ, a ∈ (Set.univ : RealSet) →
          ∀ b : ℝ, a ∈ (Set.univ : RealSet) ∧ b ∈ (Set.univ : RealSet) ∧ a < b →
            meshLimitNotZero ω Δx n := by
  sorry

-- Exercise 2197, gap 7
theorem proof_gap_exercise_2197_7
    (χ : ℝ → ℝ) (ω Δx : ℕ → ℝ)
    (hnz : ∀ i : ℤ, i ∈ (Set.univ : Set ℤ) →
      ∀ n : ℕ, n ∈ NonNegIntegerSet ∧ n > 0 →
        ∀ a : ℝ, a ∈ (Set.univ : RealSet) →
          ∀ b : ℝ, a ∈ (Set.univ : RealSet) ∧ b ∈ (Set.univ : RealSet) ∧ a < b →
            meshLimitNotZero ω Δx n) :
    ∀ a : ℝ, a ∈ (Set.univ : RealSet) →
      ∀ b : ℝ, a ∈ (Set.univ : RealSet) ∧ b ∈ (Set.univ : RealSet) ∧ a < b →
        ¬ IntegrableFuncOn χ (Icc a b) := by
  sorry

-- Exercise 2197, gap 8
theorem proof_gap_exercise_2197_8
    (χ : ℝ → ℝ)
    (hnot : ∀ a : ℝ, a ∈ (Set.univ : RealSet) →
      ∀ b : ℝ, a ∈ (Set.univ : RealSet) ∧ b ∈ (Set.univ : RealSet) ∧ a < b →
        ¬ IntegrableFuncOn χ (Icc a b)) :
    ∀ a b : ℝ, a ∈ (Set.univ : RealSet) ∧ b ∈ (Set.univ : RealSet) ∧ a < b →
      ¬ IntegrableFuncOn χ (Icc a b) := by
  sorry

-- Exercise 2197, gap 9
theorem proof_gap_exercise_2197_9
    (χ : ℝ → ℝ)
    (hnot : ∀ a b : ℝ, a ∈ (Set.univ : RealSet) ∧ b ∈ (Set.univ : RealSet) ∧ a < b →
      ¬ IntegrableFuncOn χ (Icc a b)) :
    ∀ a b : ℝ, a ∈ (Set.univ : RealSet) ∧ b ∈ (Set.univ : RealSet) ∧ a < b →
      ¬ IntegrableFuncOn χ (Icc a b) := by
  sorry

end Exercise2197
