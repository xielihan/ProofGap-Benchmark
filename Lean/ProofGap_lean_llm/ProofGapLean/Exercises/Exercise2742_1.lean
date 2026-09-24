import ProofGapLean.Prelude.Analysis

namespace ProofGap.Exercise2742_1

noncomputable section

def cutoffSet
    (f : ℕ → ℝ → ℝ) (F : ℝ → ℝ) (x ε : ℝ) : Set ℕ :=
  {N : ℕ | 0 < N ∧ ∀ n : ℕ, N < n → |f n x - F x| < ε}

def PointwiseConvergesOn
    (f : ℕ → ℝ → ℝ) (F : ℝ → ℝ) (X : Set ℝ) : Prop :=
  ∀ x ∈ X, ∀ ε : ℝ, 0 < ε → (cutoffSet f F x ε).Nonempty

theorem gap1 (f : ℕ → ℝ → ℝ) (F : ℝ → ℝ) (x₀ x ε : ℝ)
    (hconv : PointwiseConvergesOn f F (Set.Ioi x₀))
    (hx : x₀ < x) (hε : 0 < ε) :
    ∃ N : ℕ, N ∈ cutoffSet f F x ε := by
  exact hconv x hx ε hε

theorem gap2 (f : ℕ → ℝ → ℝ) (F : ℝ → ℝ) (x ε : ℝ) (N n : ℕ)
    (hN : N ∈ cutoffSet f F x ε) (hn : N < n) :
    |f n x - F x| < ε := by
  exact hN.2 n hn

theorem gap3 (f : ℕ → ℝ → ℝ) (F : ℝ → ℝ) (x₀ : ℝ) :
    PointwiseConvergesOn f F (Set.Ioi x₀) ↔
      ∀ x : ℝ, x₀ < x → ∀ ε : ℝ, 0 < ε →
        ∃ N : ℕ, N ∈ cutoffSet f F x ε := by
  constructor
  · intro hconv x hx ε hε
    exact hconv x hx ε hε
  · intro h x hx ε hε
    exact h x hx ε hε

theorem gap4 (f : ℕ → ℝ → ℝ) (F : ℝ → ℝ) (x ε : ℝ) (N : ℕ)
    (hN : N ∈ cutoffSet f F x ε) :
    0 < N ∧ ∀ n : ℕ, N < n → |f n x - F x| < ε := by
  exact hN

theorem gap5 (f : ℕ → ℝ → ℝ) (F : ℝ → ℝ) (x ε : ℝ) (N : ℕ) :
    N ∈ cutoffSet f F x ε ↔
      0 < N ∧ ∀ n : ℕ, N < n → |f n x - F x| < ε := by
  rfl

end

end ProofGap.Exercise2742_1
