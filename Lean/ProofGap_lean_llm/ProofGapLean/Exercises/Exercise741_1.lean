import ProofGapLean.Prelude.Sequences

namespace ProofGap.Exercise741_1

/-- Source: `proof_gap/exercise_741_1/1.txt`; a limit equality is represented by
equality of the corresponding `Tendsto` propositions. -/
theorem gap1 (f g F : ℝ → ℝ) (x₀ : ℝ) (hF : ∀ x, F x = f x + g x) :
    ContinuousAt F x₀ →
      ∀ L, Filter.Tendsto g (nhds x₀) (nhds L) ↔
        Filter.Tendsto (fun x => F x - f x) (nhds x₀) (nhds L) := by
  intro _ L
  have hEq : (fun x => F x - f x) = g := by
    funext x
    simp [hF x]
  rw [hEq]

/-- Source: `proof_gap/exercise_741_1/2.txt`. -/
theorem gap2 (f F : ℝ → ℝ) (x₀ LF Lf : ℝ)
    (hF : Filter.Tendsto F (nhds x₀) (nhds LF))
    (hf : Filter.Tendsto f (nhds x₀) (nhds Lf)) :
    Filter.Tendsto (fun x => F x - f x) (nhds x₀) (nhds (LF - Lf)) := by
  exact hF.sub hf

/-- Source: `proof_gap/exercise_741_1/3.txt`. -/
theorem gap3 (f F : ℝ → ℝ) (x₀ : ℝ) (hf : ContinuousAt f x₀) :
    ContinuousAt F x₀ →
      Filter.Tendsto (fun x => F x - f x) (nhds x₀)
        (nhds (F x₀ - f x₀)) := by
  intro hF
  exact hF.sub hf

/-- Source: `proof_gap/exercise_741_1/4.txt`. -/
theorem gap4 (f g F : ℝ → ℝ) (x₀ : ℝ) (hF : ∀ x, F x = f x + g x) :
    ContinuousAt F x₀ → F x₀ - f x₀ = g x₀ := by
  intro _
  simp [hF x₀]

/-- Source: `proof_gap/exercise_741_1/5.txt`. -/
theorem gap5 (f g F : ℝ → ℝ) (x₀ : ℝ) (hf : ContinuousAt f x₀)
    (hF : ∀ x, F x = f x + g x) :
    ContinuousAt F x₀ →
      Filter.Tendsto g (nhds x₀) (nhds (g x₀)) := by
  intro hFc
  simpa [hF] using hFc.sub hf

/-- Source: `proof_gap/exercise_741_1/6.txt`. -/
theorem gap6 (f g F : ℝ → ℝ) (x₀ : ℝ) (hf : ContinuousAt f x₀)
    (hF : ∀ x, F x = f x + g x) :
    ContinuousAt F x₀ → ContinuousAt g x₀ := by
  intro hFc
  exact gap5 f g F x₀ hf hF hFc

/-- Source: `proof_gap/exercise_741_1/7.txt`. -/
theorem gap7 (f g F : ℝ → ℝ) (x₀ : ℝ) (hf : ContinuousAt f x₀)
    (hng : ¬ContinuousAt g x₀) (hF : ∀ x, F x = f x + g x) :
    ContinuousAt F x₀ → False := by
  intro hFc
  exact hng (gap6 f g F x₀ hf hF hFc)

/-- Source: `proof_gap/exercise_741_1/8.txt`. -/
theorem gap8 (f g F : ℝ → ℝ) (x₀ : ℝ) (hf : ContinuousAt f x₀)
    (hng : ¬ContinuousAt g x₀) (hF : ∀ x, F x = f x + g x) :
    ¬ContinuousAt F x₀ := by
  intro hFc
  exact gap7 f g F x₀ hf hng hF hFc

/-- Source: `proof_gap/exercise_741_1/9.txt`. -/
theorem gap9 (f g F : ℝ → ℝ) (x₀ : ℝ) (hf : ContinuousAt f x₀)
    (hng : ¬ContinuousAt g x₀) (hF : ∀ x, F x = f x + g x) :
    ¬ContinuousAt F x₀ := by
  exact gap8 f g F x₀ hf hng hF

end ProofGap.Exercise741_1
