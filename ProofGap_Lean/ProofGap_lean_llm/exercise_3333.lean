import Mathlib

/- exercise_3333, gaps 1-4. -/

noncomputable section

axiom DiffableFuncOn : (ℝ → ℝ) → Set ℝ → Prop
axiom partialDeriv : (ℝ → ℝ → ℝ) → Nat → Nat → ℝ → ℝ → ℝ
axiom compDeriv3333 : (ℝ → ℝ) → (ℝ → ℝ → ℝ) → Nat → ℝ → ℝ

abbrev posInterval3333 : Set ℝ := Set.Ioi 0
abbrev r3333 (x y : ℝ) : ℝ := Real.sqrt (x ^ (2 : Nat) + y ^ (2 : Nat))
abbrev radialDeriv3333 (φ : ℝ → ℝ) (x y : ℝ) : ℝ :=
  compDeriv3333 φ (fun x y => r3333 x y) 1 (r3333 x y)

theorem proof_gap_exercise_3333_1
    (z : ℝ → ℝ → ℝ) (φ : ℝ → ℝ)
    (hz : ∀ x y : ℝ, (x, y) ≠ (0, 0) → z x y = φ (r3333 x y))
    (hφ : DiffableFuncOn φ posInterval3333) :
    ∀ x y : ℝ, (x, y) ≠ (0, 0) →
      partialDeriv z 1 1 x y = x * radialDeriv3333 φ x y / r3333 x y := by
  sorry

theorem proof_gap_exercise_3333_2
    (z : ℝ → ℝ → ℝ) (φ : ℝ → ℝ)
    (hz : ∀ x y : ℝ, (x, y) ≠ (0, 0) → z x y = φ (r3333 x y))
    (hφ : DiffableFuncOn φ posInterval3333)
    (h1 : ∀ x y : ℝ, (x, y) ≠ (0, 0) →
      partialDeriv z 1 1 x y = x * radialDeriv3333 φ x y / r3333 x y) :
    ∀ x y : ℝ, (x, y) ≠ (0, 0) →
      partialDeriv z 2 1 x y = y * radialDeriv3333 φ x y / r3333 x y := by
  sorry

theorem proof_gap_exercise_3333_3
    (z : ℝ → ℝ → ℝ) (φ : ℝ → ℝ)
    (hz : ∀ x y : ℝ, (x, y) ≠ (0, 0) → z x y = φ (r3333 x y))
    (hφ : DiffableFuncOn φ posInterval3333)
    (h1 : ∀ x y : ℝ, (x, y) ≠ (0, 0) →
      partialDeriv z 1 1 x y = x * radialDeriv3333 φ x y / r3333 x y)
    (h2 : ∀ x y : ℝ, (x, y) ≠ (0, 0) →
      partialDeriv z 2 1 x y = y * radialDeriv3333 φ x y / r3333 x y) :
    ∀ y x : ℝ, (x, y) ≠ (0, 0) →
      y * partialDeriv z 1 1 x y - x * partialDeriv z 2 1 x y = 0 := by
  sorry

theorem proof_gap_exercise_3333_4
    (z : ℝ → ℝ → ℝ) (φ : ℝ → ℝ)
    (hz : ∀ x y : ℝ, (x, y) ≠ (0, 0) → z x y = φ (r3333 x y))
    (hφ : DiffableFuncOn φ posInterval3333)
    (h1 : ∀ x y : ℝ, (x, y) ≠ (0, 0) →
      partialDeriv z 1 1 x y = x * radialDeriv3333 φ x y / r3333 x y)
    (h2 : ∀ x y : ℝ, (x, y) ≠ (0, 0) →
      partialDeriv z 2 1 x y = y * radialDeriv3333 φ x y / r3333 x y)
    (h3 : ∀ y x : ℝ, (x, y) ≠ (0, 0) →
      y * partialDeriv z 1 1 x y - x * partialDeriv z 2 1 x y = 0) :
    ∀ y x : ℝ, (x, y) ≠ (0, 0) →
      y * partialDeriv z 1 1 x y - x * partialDeriv z 2 1 x y = 0 := by
  sorry
