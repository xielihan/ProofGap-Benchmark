import Mathlib

set_option linter.style.longLine false

open scoped BigOperators Topology Nat
open Filter

local notation:70 x " /. " y => ((x : ℝ) / (y : ℝ))

def leftRay (a : ℝ) : Set ℝ := Set.Iic a
def rightRay (a : ℝ) : Set ℝ := Set.Ici a
def wholeRealInterval : Set ℝ := Set.univ

-- exercise: exercise_798

theorem proof_gap_exercise_798_1
  (f : ℝ → ℝ)
  (hf : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → f x = Real.arctan x)
  : ContinuousOn f (leftRay 1) := by
  sorry

theorem proof_gap_exercise_798_2
  (f : ℝ → ℝ)
  (hf : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → f x = Real.arctan x)
  (h3 : ContinuousOn f (leftRay 1))
  : ContinuousOn f (rightRay 0) := by
  sorry

theorem proof_gap_exercise_798_3
  (f : ℝ → ℝ)
  (hf : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → f x = Real.arctan x)
  (h3 : ContinuousOn f (leftRay 1))
  (h4 : ContinuousOn f (rightRay 0))
  : Tendsto (fun x : ℝ => Real.arctan x) atTop (𝓝 (Real.pi /. 2)) := by
  sorry

theorem proof_gap_exercise_798_4
  (f : ℝ → ℝ)
  (hf : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → f x = Real.arctan x)
  (h3 : ContinuousOn f (leftRay 1))
  (h4 : ContinuousOn f (rightRay 0))
  (h5 : Tendsto (fun x : ℝ => Real.arctan x) atTop (𝓝 (Real.pi /. 2)))
  : Tendsto (fun x : ℝ => Real.arctan x) atBot (𝓝 (-(Real.pi /. 2))) := by
  sorry

theorem proof_gap_exercise_798_5
  (f : ℝ → ℝ)
  (hf : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → f x = Real.arctan x)
  (h3 : ContinuousOn f (leftRay 1))
  (h4 : ContinuousOn f (rightRay 0))
  (h5 : Tendsto (fun x : ℝ => Real.arctan x) atTop (𝓝 (Real.pi /. 2)))
  (h6 : Tendsto (fun x : ℝ => Real.arctan x) atBot (𝓝 (-(Real.pi /. 2))))
  : UniformContinuousOn f (rightRay 0) := by
  sorry

theorem proof_gap_exercise_798_6
  (f : ℝ → ℝ)
  (hf : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → f x = Real.arctan x)
  (h3 : ContinuousOn f (leftRay 1))
  (h4 : ContinuousOn f (rightRay 0))
  (h5 : Tendsto (fun x : ℝ => Real.arctan x) atTop (𝓝 (Real.pi /. 2)))
  (h6 : Tendsto (fun x : ℝ => Real.arctan x) atBot (𝓝 (-(Real.pi /. 2))))
  (h7 : UniformContinuousOn f (rightRay 0))
  : UniformContinuousOn f (leftRay 1) := by
  sorry

theorem proof_gap_exercise_798_7
  (f : ℝ → ℝ)
  (hf : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → f x = Real.arctan x)
  (h3 : ContinuousOn f (leftRay 1))
  (h4 : ContinuousOn f (rightRay 0))
  (h5 : Tendsto (fun x : ℝ => Real.arctan x) atTop (𝓝 (Real.pi /. 2)))
  (h6 : Tendsto (fun x : ℝ => Real.arctan x) atBot (𝓝 (-(Real.pi /. 2))))
  (h7 : UniformContinuousOn f (rightRay 0))
  (h8 : UniformContinuousOn f (leftRay 1))
  : ∀ ε : ℝ, ε ∈ (Set.univ : Set ℝ) ∧ ε > 0 →
      ∃ δ : ℝ × ℝ → ℝ, δ (1, ε) > 0 ∧
        ∀ x₁ x₂ : ℝ, x₁ ∈ (Set.univ : Set ℝ) ∧ x₂ ∈ (Set.univ : Set ℝ) ∧
          x₁ ∈ leftRay 1 ∧ x₂ ∈ leftRay 1 ∧ |x₁ - x₂| < δ (1, ε) →
          |f x₁ - f x₂| < ε := by
  sorry

theorem proof_gap_exercise_798_8
  (f : ℝ → ℝ)
  (hf : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → f x = Real.arctan x)
  (h3 : ContinuousOn f (leftRay 1))
  (h4 : ContinuousOn f (rightRay 0))
  (h5 : Tendsto (fun x : ℝ => Real.arctan x) atTop (𝓝 (Real.pi /. 2)))
  (h6 : Tendsto (fun x : ℝ => Real.arctan x) atBot (𝓝 (-(Real.pi /. 2))))
  (h7 : UniformContinuousOn f (rightRay 0))
  (h8 : UniformContinuousOn f (leftRay 1))
  (h9 : ∀ ε : ℝ, ε ∈ (Set.univ : Set ℝ) ∧ ε > 0 →
      ∃ δ : ℝ × ℝ → ℝ, δ (1, ε) > 0 ∧
        ∀ x₁ x₂ : ℝ, x₁ ∈ (Set.univ : Set ℝ) ∧ x₂ ∈ (Set.univ : Set ℝ) ∧
          x₁ ∈ leftRay 1 ∧ x₂ ∈ leftRay 1 ∧ |x₁ - x₂| < δ (1, ε) →
          |f x₁ - f x₂| < ε)
  : ∀ ε : ℝ, ε ∈ (Set.univ : Set ℝ) ∧ ε > 0 →
      ∃ δ : ℝ × ℝ → ℝ, δ (2, ε) > 0 ∧
        ∀ x₁ x₂ : ℝ, x₁ ∈ (Set.univ : Set ℝ) ∧ x₂ ∈ (Set.univ : Set ℝ) ∧
          x₁ ∈ rightRay 0 ∧ x₂ ∈ rightRay 0 ∧ |x₁ - x₂| < δ (2, ε) →
          |f x₁ - f x₂| < ε := by
  sorry

theorem proof_gap_exercise_798_9
  (f : ℝ → ℝ)
  (hf : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → f x = Real.arctan x)
  (h3 : ContinuousOn f (leftRay 1))
  (h4 : ContinuousOn f (rightRay 0))
  (h5 : Tendsto (fun x : ℝ => Real.arctan x) atTop (𝓝 (Real.pi /. 2)))
  (h6 : Tendsto (fun x : ℝ => Real.arctan x) atBot (𝓝 (-(Real.pi /. 2))))
  (h7 : UniformContinuousOn f (rightRay 0))
  (h8 : UniformContinuousOn f (leftRay 1))
  (h9 : ∀ ε : ℝ, ε ∈ (Set.univ : Set ℝ) ∧ ε > 0 →
      ∃ δ : ℝ × ℝ → ℝ, δ (1, ε) > 0 ∧
        ∀ x₁ x₂ : ℝ, x₁ ∈ (Set.univ : Set ℝ) ∧ x₂ ∈ (Set.univ : Set ℝ) ∧
          x₁ ∈ leftRay 1 ∧ x₂ ∈ leftRay 1 ∧ |x₁ - x₂| < δ (1, ε) →
          |f x₁ - f x₂| < ε)
  (h10 : ∀ ε : ℝ, ε ∈ (Set.univ : Set ℝ) ∧ ε > 0 →
      ∃ δ : ℝ × ℝ → ℝ, δ (2, ε) > 0 ∧
        ∀ x₁ x₂ : ℝ, x₁ ∈ (Set.univ : Set ℝ) ∧ x₂ ∈ (Set.univ : Set ℝ) ∧
          x₁ ∈ rightRay 0 ∧ x₂ ∈ rightRay 0 ∧ |x₁ - x₂| < δ (2, ε) →
          |f x₁ - f x₂| < ε)
  : ∃ δ : ℝ × ℝ → ℝ, ∃ d : ℝ → ℝ,
      ∀ ε : ℝ, ε ∈ (Set.univ : Set ℝ) ∧ ε > 0 ∧ d ε = min 1 (min (δ (1, ε)) (δ (2, ε))) →
        ∀ x₁ x₂ : ℝ, x₁ ∈ (Set.univ : Set ℝ) ∧ x₂ ∈ (Set.univ : Set ℝ) ∧
          x₁ ∈ wholeRealInterval ∧ x₂ ∈ wholeRealInterval ∧ |x₁ - x₂| < d ε →
          (x₁ ∈ leftRay 1 ∧ x₂ ∈ leftRay 1) ∨ (x₁ ∈ rightRay 0 ∧ x₂ ∈ rightRay 0) := by
  sorry

theorem proof_gap_exercise_798_10
  (f : ℝ → ℝ)
  (hf : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → f x = Real.arctan x)
  (h3 : ContinuousOn f (leftRay 1))
  (h4 : ContinuousOn f (rightRay 0))
  (h5 : Tendsto (fun x : ℝ => Real.arctan x) atTop (𝓝 (Real.pi /. 2)))
  (h6 : Tendsto (fun x : ℝ => Real.arctan x) atBot (𝓝 (-(Real.pi /. 2))))
  (h7 : UniformContinuousOn f (rightRay 0))
  (h8 : UniformContinuousOn f (leftRay 1))
  (h11 : ∃ δ : ℝ × ℝ → ℝ, ∃ d : ℝ → ℝ,
      ∀ ε : ℝ, ε ∈ (Set.univ : Set ℝ) ∧ ε > 0 ∧ d ε = min 1 (min (δ (1, ε)) (δ (2, ε))) →
        ∀ x₁ x₂ : ℝ, x₁ ∈ (Set.univ : Set ℝ) ∧ x₂ ∈ (Set.univ : Set ℝ) ∧
          x₁ ∈ wholeRealInterval ∧ x₂ ∈ wholeRealInterval ∧ |x₁ - x₂| < d ε →
          (x₁ ∈ leftRay 1 ∧ x₂ ∈ leftRay 1) ∨ (x₁ ∈ rightRay 0 ∧ x₂ ∈ rightRay 0))
  : ∃ δ : ℝ × ℝ → ℝ, ∃ d : ℝ → ℝ,
      ∀ ε : ℝ, ε ∈ (Set.univ : Set ℝ) ∧ ε > 0 ∧ d ε = min 1 (min (δ (1, ε)) (δ (2, ε))) →
        ∀ x₁ x₂ : ℝ, x₁ ∈ (Set.univ : Set ℝ) ∧ x₂ ∈ (Set.univ : Set ℝ) ∧
          x₁ ∈ wholeRealInterval ∧ x₂ ∈ wholeRealInterval ∧ |x₁ - x₂| < d ε →
          |f x₁ - f x₂| < ε := by
  sorry

theorem proof_gap_exercise_798_11
  (f : ℝ → ℝ)
  (hf : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → f x = Real.arctan x)
  (h3 : ContinuousOn f (leftRay 1))
  (h4 : ContinuousOn f (rightRay 0))
  (h5 : Tendsto (fun x : ℝ => Real.arctan x) atTop (𝓝 (Real.pi /. 2)))
  (h6 : Tendsto (fun x : ℝ => Real.arctan x) atBot (𝓝 (-(Real.pi /. 2))))
  (h7 : UniformContinuousOn f (rightRay 0))
  (h8 : UniformContinuousOn f (leftRay 1))
  (h11 : ∃ δ : ℝ × ℝ → ℝ, ∃ d : ℝ → ℝ,
      ∀ ε : ℝ, ε ∈ (Set.univ : Set ℝ) ∧ ε > 0 ∧ d ε = min 1 (min (δ (1, ε)) (δ (2, ε))) →
        ∀ x₁ x₂ : ℝ, x₁ ∈ (Set.univ : Set ℝ) ∧ x₂ ∈ (Set.univ : Set ℝ) ∧
          x₁ ∈ wholeRealInterval ∧ x₂ ∈ wholeRealInterval ∧ |x₁ - x₂| < d ε →
          (x₁ ∈ leftRay 1 ∧ x₂ ∈ leftRay 1) ∨ (x₁ ∈ rightRay 0 ∧ x₂ ∈ rightRay 0))
  (h12 : ∃ δ : ℝ × ℝ → ℝ, ∃ d : ℝ → ℝ,
      ∀ ε : ℝ, ε ∈ (Set.univ : Set ℝ) ∧ ε > 0 ∧ d ε = min 1 (min (δ (1, ε)) (δ (2, ε))) →
        ∀ x₁ x₂ : ℝ, x₁ ∈ (Set.univ : Set ℝ) ∧ x₂ ∈ (Set.univ : Set ℝ) ∧
          x₁ ∈ wholeRealInterval ∧ x₂ ∈ wholeRealInterval ∧ |x₁ - x₂| < d ε →
          |f x₁ - f x₂| < ε)
  : UniformContinuousOn f wholeRealInterval := by
  sorry

theorem proof_gap_exercise_798_12
  (f : ℝ → ℝ)
  (hf : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → f x = Real.arctan x)
  (h3 : ContinuousOn f (leftRay 1))
  (h4 : ContinuousOn f (rightRay 0))
  (h5 : Tendsto (fun x : ℝ => Real.arctan x) atTop (𝓝 (Real.pi /. 2)))
  (h6 : Tendsto (fun x : ℝ => Real.arctan x) atBot (𝓝 (-(Real.pi /. 2))))
  (h7 : UniformContinuousOn f (rightRay 0))
  (h8 : UniformContinuousOn f (leftRay 1))
  (h13 : UniformContinuousOn f wholeRealInterval)
  : UniformContinuousOn f wholeRealInterval := by
  sorry
