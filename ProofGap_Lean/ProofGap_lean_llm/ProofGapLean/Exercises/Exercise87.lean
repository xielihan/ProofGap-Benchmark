import ProofGapLean.Prelude.Core

namespace ProofGap.Exercise87

def IsCauchy (x : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ m n : ℕ, N < n → N < m → |x n - x m| < ε

def FailsCauchy (x : ℕ → ℝ) : Prop :=
  ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ N : ℕ, ∃ n₀ m₀ : ℕ,
      N < n₀ ∧ N < m₀ ∧ ε₀ ≤ |x n₀ - x m₀|

/-- Exercise 87, gap 1; remove the rebound N witness. -/
theorem gap1 (x : ℕ → ℝ) :
    ¬ IsCauchy x ↔ FailsCauchy x := by
  unfold IsCauchy FailsCauchy
  push_neg
  constructor
  · rintro ⟨ε, hε, h⟩
    refine ⟨ε, hε, ?_⟩
    intro N
    rcases h N with ⟨m, n, hn, hm, hdist⟩
    exact ⟨n, m, hn, hm, hdist⟩
  · rintro ⟨ε, hε, h⟩
    refine ⟨ε, hε, ?_⟩
    intro N
    rcases h N with ⟨n, m, hn, hm, hdist⟩
    exact ⟨m, n, hn, hm, hdist⟩

/-- Exercise 87, gap 2. -/
theorem gap2 (x : ℕ → ℝ) :
    ¬ IsCauchy x ↔ FailsCauchy x := by
  exact gap1 x

end ProofGap.Exercise87
