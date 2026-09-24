import ProofGapLean.Prelude.Sequences

namespace ProofGap.Exercise787

noncomputable section

/-- Exercise 787, gap 1; identify the nested ε-δ formula with pointwise continuity. -/
theorem gap1 (f : ℝ → ℝ) (E : Set ℝ) (hcont : ContinuousOn f E) :
    ∀ x₀ ∈ E, ∀ ε > 0, ∃ δ > 0,
      ∀ x ∈ E, |x - x₀| < δ → |f x - f x₀| < ε := by
  intro x₀ hx₀
  have hc := hcont x₀ hx₀
  simpa only [Metric.continuousWithinAt_iff, Real.dist_eq] using hc

/-- Exercise 787, gap 2; bind the set once instead of existentially shadowing it. -/
theorem gap2 (f : ℝ → ℝ) (E : Set ℝ) (hnot : ¬ UniformContinuousOn f E) :
    ∃ ε₀ > 0, ∀ δ > 0, ∃ x₁ ∈ E, ∃ x₂ ∈ E,
      |x₁ - x₂| < δ ∧ |f x₁ - f x₂| ≥ ε₀ := by
  rw [Metric.uniformContinuousOn_iff] at hnot
  push_neg at hnot
  simpa only [Real.dist_eq] using hnot

/-- Exercise 787, gap 3. -/
theorem gap3 (f : ℝ → ℝ) (E : Set ℝ) (hcont : ContinuousOn f E) :
    ContinuousOn f E := by
  exact hcont

/-- Exercise 787, gap 4. -/
theorem gap4 (f : ℝ → ℝ) (E : Set ℝ)
    (hwitness : ∃ ε₀ > 0, ∀ δ > 0, ∃ x₁ ∈ E, ∃ x₂ ∈ E,
      |x₁ - x₂| < δ ∧ |f x₁ - f x₂| ≥ ε₀) :
    ¬ UniformContinuousOn f E := by
  intro huniform
  rw [Metric.uniformContinuousOn_iff] at huniform
  rcases hwitness with ⟨ε₀, hε₀, hwitness⟩
  rcases huniform ε₀ hε₀ with ⟨δ, hδ, hbound⟩
  rcases hwitness δ hδ with ⟨x₁, hx₁, x₂, hx₂, hnear, hfar⟩
  have hin : dist x₁ x₂ < δ := by
    simpa only [Real.dist_eq] using hnear
  have hout : |f x₁ - f x₂| < ε₀ := by
    simpa only [Real.dist_eq] using hbound x₁ hx₁ x₂ hx₂ hin
  exact (not_lt_of_ge hfar) hout

/-- Exercise 787, gap 5. -/
theorem gap5 (f : ℝ → ℝ) (E : Set ℝ)
    (hcont : ContinuousOn f E) (hnot : ¬ UniformContinuousOn f E) :
    ContinuousOn f E ∧ ¬ UniformContinuousOn f E := by
  exact ⟨hcont, hnot⟩

end

end ProofGap.Exercise787
