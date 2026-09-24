import ProofGapLean.Prelude.Sequences

namespace ProofGap.Exercise746

/-- Source: `proof_gap/exercise_746/1.txt`. -/
theorem gap1 (f : ℝ → ℝ) :
    ∀ x₀, ContinuousAt f x₀ →
      ∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| < δ →
        |f x - f x₀| < ε := by
  intro x₀ hf
  simpa only [Metric.continuousAt_iff, Real.dist_eq] using hf

/-- Source: `proof_gap/exercise_746/2.txt`; remove the unused `ε` quantifier. -/
theorem gap2 (f : ℝ → ℝ) :
    ∀ x x₀, abs (abs (f x) - abs (f x₀)) ≤ |f x - f x₀| := by
  intro x x₀
  exact abs_abs_sub_abs_le_abs_sub (f x) (f x₀)

/-- Source: `proof_gap/exercise_746/3.txt`; restore the missing
`|x-x₀|<δ` premise. -/
theorem gap3 (f : ℝ → ℝ) :
    ∀ x₀, ContinuousAt f x₀ → ∀ ε > 0, ∃ δ > 0, ∀ x,
      |x - x₀| < δ → abs (abs (f x) - abs (f x₀)) < ε := by
  intro x₀ hf ε hε
  obtain ⟨δ, hδ, hd⟩ := gap1 f x₀ hf ε hε
  refine ⟨δ, hδ, ?_⟩
  intro x hx
  exact lt_of_le_of_lt (gap2 f x x₀) (hd x hx)

/-- Source: `proof_gap/exercise_746/4.txt`. -/
theorem gap4 (f F : ℝ → ℝ) (hF : ∀ x, F x = |f x|) :
    ∀ x₀, ContinuousAt f x₀ → ContinuousAt F x₀ := by
  intro x₀ hf
  rw [Metric.continuousAt_iff]
  intro ε hε
  obtain ⟨δ, hδ, hd⟩ := gap3 f x₀ hf ε hε
  refine ⟨δ, hδ, ?_⟩
  intro x hx
  have hx' : |x - x₀| < δ := by
    simpa only [Real.dist_eq] using hx
  have h := hd x hx'
  simpa only [Real.dist_eq, hF x, hF x₀] using h

/-- Source: `proof_gap/exercise_746/5.txt`. -/
theorem gap5 (f F : ℝ → ℝ) (hf : Continuous f)
    (hF : ∀ x, F x = |f x|) : Continuous F := by
  rw [continuous_iff_continuousAt]
  intro x₀
  exact gap4 f F hF x₀ hf.continuousAt

/-- Source: `proof_gap/exercise_746/6.txt`. -/
theorem gap6 (f F : ℝ → ℝ) (hf : Continuous f)
    (hF : ∀ x, F x = |f x|) : Continuous F := by
  exact gap5 f F hf hF

end ProofGap.Exercise746
