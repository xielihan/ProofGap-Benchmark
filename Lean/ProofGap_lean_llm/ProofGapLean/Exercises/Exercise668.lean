import ProofGapLean.Prelude.Sequences
import Mathlib.Tactic

namespace ProofGap.Exercise668

/-- Source: `proof_gap/exercise_668/1.txt`; epsilon-delta witness for failure of continuity. -/
theorem gap1 (f : ℝ → ℝ) (x₀ : ℝ) (h : ¬ ContinuousAt f x₀) :
    ∃ ε₀ > 0, ∀ δ > 0, ∃ x,
      |x - x₀| < δ ∧ ε₀ ≤ |f x - f x₀| := by
  rw [Metric.continuousAt_iff] at h
  push_neg at h
  simpa only [Real.dist_eq] using h

/-- Source: `proof_gap/exercise_668/2.txt`. -/
theorem gap2 (f : ℝ → ℝ) (x₀ : ℝ) :
    ¬ ContinuousAt f x₀ ↔
      ∃ ε₀ > 0, ∀ δ > 0, ∃ x,
        |x - x₀| < δ ∧ ε₀ ≤ |f x - f x₀| := by
  constructor
  · exact gap1 f x₀
  · rintro ⟨ε₀, hε₀, hbad⟩ hcont
    rw [Metric.continuousAt_iff] at hcont
    obtain ⟨δ, hδ, hclose⟩ := hcont ε₀ hε₀
    obtain ⟨x, hx, hfar⟩ := hbad δ hδ
    have hx' : dist x x₀ < δ := by
      simpa only [Real.dist_eq] using hx
    have hnear : |f x - f x₀| < ε₀ := by
      simpa only [Real.dist_eq] using (@hclose x hx')
    exact (not_lt_of_ge hfar) hnear

end ProofGap.Exercise668
