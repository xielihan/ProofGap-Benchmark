import Mathlib

open Filter
open scoped Topology

noncomputable section

namespace Exercise2197

abbrev RealSet := Set ℝ
def RationalSet : Set ℝ := {x | ∃ q : ℚ, (q : ℝ) = x}
def NonNegIntegerSet : Set ℕ := Set.univ
def Icc (a b : ℝ) : Set ℝ := Set.Icc a b

noncomputable def OscillationOn (f : ℝ → ℝ) (s : Set ℝ) : ℝ := sSup ((fun p : ℝ × ℝ => |f p.1 - f p.2|) '' (s ×ˢ s))
def IntegrableFuncOn (f : ℝ → ℝ) (s : Set ℝ) : Prop := MeasureTheory.IntegrableOn f s
noncomputable def sumOsc (ω Δx : ℕ → ℝ) (n : ℕ) : ℝ := ∑ i ∈ Finset.range n, ω i * Δx i
noncomputable def sumLen (Δx : ℕ → ℝ) (n : ℕ) : ℝ := ∑ i ∈ Finset.range n, Δx i
def meshLimitNotZero (ω Δx : ℕ → ℝ) (_n : ℕ) : Prop := ¬ Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n, ω i * Δx i) atTop (𝓝 0)

theorem proof_gap_exercise_2197_1
    (χ : ℝ → ℝ) (ω Δx : ℕ → ℝ)
    (hirr : ∀ x : ℝ, x ∈ (Set.univ : RealSet) ∧ x ∉ RationalSet → χ x = 0)
    (hrat : ∀ x : ℝ, x ∈ (Set.univ : RealSet) ∧ x ∈ RationalSet → χ x = 1) :
    ∀ a : ℝ, a ∈ (Set.univ : RealSet) →
      ∀ b : ℝ, a ∈ (Set.univ : RealSet) ∧ b ∈ (Set.univ : RealSet) ∧ a < b →
        ∀ α β : ℝ, α ∈ (Set.univ : RealSet) ∧ β ∈ (Set.univ : RealSet) ∧
          a ≤ α ∧ α < β ∧ β ≤ b → OscillationOn χ (Icc α β) = 1 := by
  sorry

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

theorem proof_gap_exercise_2197_3
    (ω Δx : ℕ → ℝ) :
    ∀ i : ℤ, i ∈ (Set.univ : Set ℤ) →
      ∀ n : ℕ, n ∈ NonNegIntegerSet ∧ n > 0 →
        ∀ a : ℝ, a ∈ (Set.univ : RealSet) →
          ∀ b : ℝ, a ∈ (Set.univ : RealSet) ∧ b ∈ (Set.univ : RealSet) ∧ a < b →
            sumOsc ω Δx n = sumLen Δx n := by
  sorry

theorem proof_gap_exercise_2197_4
    (ω Δx : ℕ → ℝ) :
    ∀ i : ℤ, i ∈ (Set.univ : Set ℤ) →
      ∀ n : ℕ, n ∈ NonNegIntegerSet ∧ n > 0 →
        ∀ a : ℝ, a ∈ (Set.univ : RealSet) →
          ∀ b : ℝ, a ∈ (Set.univ : RealSet) ∧ b ∈ (Set.univ : RealSet) ∧ a < b →
            sumLen Δx n = b - a := by
  sorry

theorem proof_gap_exercise_2197_5
    (ω Δx : ℕ → ℝ) :
    ∀ i : ℤ, i ∈ (Set.univ : Set ℤ) →
      ∀ n : ℕ, n ∈ NonNegIntegerSet ∧ n > 0 →
        ∀ a : ℝ, a ∈ (Set.univ : RealSet) →
          ∀ b : ℝ, a ∈ (Set.univ : RealSet) ∧ b ∈ (Set.univ : RealSet) ∧ a < b →
            sumOsc ω Δx n = b - a := by
  sorry

theorem proof_gap_exercise_2197_6
    (ω Δx : ℕ → ℝ) :
    ∀ i : ℤ, i ∈ (Set.univ : Set ℤ) →
      ∀ n : ℕ, n ∈ NonNegIntegerSet ∧ n > 0 →
        ∀ a : ℝ, a ∈ (Set.univ : RealSet) →
          ∀ b : ℝ, a ∈ (Set.univ : RealSet) ∧ b ∈ (Set.univ : RealSet) ∧ a < b →
            meshLimitNotZero ω Δx n := by
  sorry

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

theorem proof_gap_exercise_2197_8
    (χ : ℝ → ℝ)
    (hnot : ∀ a : ℝ, a ∈ (Set.univ : RealSet) →
      ∀ b : ℝ, a ∈ (Set.univ : RealSet) ∧ b ∈ (Set.univ : RealSet) ∧ a < b →
        ¬ IntegrableFuncOn χ (Icc a b)) :
    ∀ a b : ℝ, a ∈ (Set.univ : RealSet) ∧ b ∈ (Set.univ : RealSet) ∧ a < b →
      ¬ IntegrableFuncOn χ (Icc a b) := by
  sorry

theorem proof_gap_exercise_2197_9
    (χ : ℝ → ℝ)
    (hnot : ∀ a b : ℝ, a ∈ (Set.univ : RealSet) ∧ b ∈ (Set.univ : RealSet) ∧ a < b →
      ¬ IntegrableFuncOn χ (Icc a b)) :
    ∀ a b : ℝ, a ∈ (Set.univ : RealSet) ∧ b ∈ (Set.univ : RealSet) ∧ a < b →
      ¬ IntegrableFuncOn χ (Icc a b) := by
  sorry

end Exercise2197
