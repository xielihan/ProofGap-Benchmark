import ProofGapLean.Prelude.Analysis

namespace ProofGap.Exercise2742_2

noncomputable section

def UniformlyConvergesOn
    (f : ℕ → ℝ → ℝ) (F : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ n : ℕ, N < n → ∀ x ∈ s, |f n x - F x| < ε

theorem gap1 :
    ∀ (f : ℕ → ℝ → ℝ) (F : ℝ → ℝ) (a b : ℝ),
      UniformlyConvergesOn f F (Set.Ioo a b) ↔
        ∀ ε : ℝ, 0 < ε →
          ∃ N : ℕ, ∀ n : ℕ, N < n →
            ∀ x : ℝ, x ∈ Set.Ioo a b → |f n x - F x| < ε := by
  intro f F a b
  rfl

theorem gap2 :
    ∀ (f : ℕ → ℝ → ℝ) (F : ℝ → ℝ) (a b : ℝ),
      UniformlyConvergesOn f F (Set.Ioo a b) ↔
        ∀ ε : ℝ, 0 < ε →
          ∃ N : ℕ, ∀ n : ℕ, N < n →
            ∀ x : ℝ, x ∈ Set.Ioo a b → |f n x - F x| < ε := by
  intro f F a b
  exact gap1 f F a b

end

end ProofGap.Exercise2742_2
