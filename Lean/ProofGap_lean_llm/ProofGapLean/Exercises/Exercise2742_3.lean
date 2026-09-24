import ProofGapLean.Prelude.Analysis

namespace ProofGap.Exercise2742_3

noncomputable section

def UniformlyConvergesOn
    (f : ℕ → ℝ → ℝ) (F : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ n : ℕ, N < n → ∀ x ∈ s, |f n x - F x| < ε

theorem gap1 :
    ∀ (f : ℕ → ℝ → ℝ) (F : ℝ → ℝ) (x₀ : ℝ),
      UniformlyConvergesOn f F (Set.Ioi x₀) ↔
        ∀ ε : ℝ, 0 < ε →
          ∃ N : ℕ, ∀ n : ℕ, N < n →
            ∀ x : ℝ, x ∈ Set.Ioi x₀ → |f n x - F x| < ε := by
  intro f F x₀
  rfl

theorem gap2 :
    ∀ (f : ℕ → ℝ → ℝ) (F : ℝ → ℝ) (x₀ : ℝ),
      UniformlyConvergesOn f F (Set.Ioi x₀) ↔
        ∀ ε : ℝ, 0 < ε →
          ∃ N : ℕ, ∀ n : ℕ, N < n →
            ∀ x : ℝ, x ∈ Set.Ioi x₀ → |f n x - F x| < ε := by
  intro f F x₀
  exact gap1 f F x₀

end

end ProofGap.Exercise2742_3
