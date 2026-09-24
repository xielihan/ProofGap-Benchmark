import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise799

/-- Source: `proof_gap/exercise_799/1.txt`. -/
theorem gap1 (x₁ x₂ : ℝ) (hx₁ : x₁ ∈ Set.Ici (1 : ℝ))
    (hx₂ : x₂ ∈ Set.Ici (1 : ℝ)) :
    |Real.sqrt x₁ - Real.sqrt x₂| =
      |(x₁ - x₂) / (Real.sqrt x₁ + Real.sqrt x₂)| := by
  have hx₁' : (1 : ℝ) ≤ x₁ := hx₁
  have hx₂' : (1 : ℝ) ≤ x₂ := hx₂
  have hx₁0 : 0 ≤ x₁ := by linarith
  have hx₂0 : 0 ≤ x₂ := by linarith
  have hs₁pos : 0 < Real.sqrt x₁ :=
    Real.sqrt_pos.2 (by linarith)
  have hs₂pos : 0 < Real.sqrt x₂ :=
    Real.sqrt_pos.2 (by linarith)
  have hden : 0 < Real.sqrt x₁ + Real.sqrt x₂ := by linarith
  have hquot :
      Real.sqrt x₁ - Real.sqrt x₂ =
        (x₁ - x₂) / (Real.sqrt x₁ + Real.sqrt x₂) := by
    apply (eq_div_iff (ne_of_gt hden)).2
    nlinarith [Real.sq_sqrt hx₁0, Real.sq_sqrt hx₂0]
  exact congrArg (fun x : ℝ => |x|) hquot

/-- Source: `proof_gap/exercise_799/2.txt`. -/
theorem gap2 (x₁ x₂ : ℝ) (hx₁ : x₁ ∈ Set.Ici (1 : ℝ))
    (hx₂ : x₂ ∈ Set.Ici (1 : ℝ)) :
    |(x₁ - x₂) / (Real.sqrt x₁ + Real.sqrt x₂)| ≤
      |x₁ - x₂| / 2 := by
  have hx₁' : (1 : ℝ) ≤ x₁ := hx₁
  have hx₂' : (1 : ℝ) ≤ x₂ := hx₂
  have hs₁ : (1 : ℝ) ≤ Real.sqrt x₁ := by
    simpa only [Real.sqrt_one] using (Real.sqrt_le_sqrt hx₁')
  have hs₂ : (1 : ℝ) ≤ Real.sqrt x₂ := by
    simpa only [Real.sqrt_one] using (Real.sqrt_le_sqrt hx₂')
  have hden : (2 : ℝ) ≤ Real.sqrt x₁ + Real.sqrt x₂ := by linarith
  have hdenpos : 0 < Real.sqrt x₁ + Real.sqrt x₂ := by linarith
  rw [abs_div, abs_of_pos hdenpos]
  exact div_le_div_of_nonneg_left (abs_nonneg _) (by norm_num) hden

/-- Source: `proof_gap/exercise_799/3.txt`. -/
theorem gap3 (x₁ x₂ : ℝ) (hx₁ : x₁ ∈ Set.Ici (1 : ℝ))
    (hx₂ : x₂ ∈ Set.Ici (1 : ℝ)) :
    |Real.sqrt x₁ - Real.sqrt x₂| ≤ |x₁ - x₂| / 2 := by
  calc
    |Real.sqrt x₁ - Real.sqrt x₂| =
        |(x₁ - x₂) / (Real.sqrt x₁ + Real.sqrt x₂)| :=
      gap1 x₁ x₂ hx₁ hx₂
    _ ≤ |x₁ - x₂| / 2 := gap2 x₁ x₂ hx₁ hx₂

/-- Source: `proof_gap/exercise_799/4.txt`; move `ε` outside the existential
so that the modulus may depend on it. -/
theorem gap4 :
    ∀ ε > 0, ∃ δ > 0, ∀ x₁ ∈ Set.Ici (1 : ℝ), ∀ x₂ ∈ Set.Ici (1 : ℝ),
      |x₁ - x₂| < δ →
        |Real.sqrt x₁ - Real.sqrt x₂| < (1 / 2 : ℝ) * (2 * ε) := by
  intro ε hε
  refine ⟨2 * ε, by nlinarith, ?_⟩
  intro x₁ hx₁ x₂ hx₂ hdist
  have hhalf : |x₁ - x₂| / 2 < ε := by nlinarith
  calc
    |Real.sqrt x₁ - Real.sqrt x₂| ≤ |x₁ - x₂| / 2 :=
      gap3 x₁ x₂ hx₁ hx₂
    _ < ε := hhalf
    _ = (1 / 2 : ℝ) * (2 * ε) := by ring

/-- Source: `proof_gap/exercise_799/5`; move `ε` outside the existential. -/
theorem gap5 :
    ∀ ε > 0, ∃ δ > 0, ∀ x₁ ∈ Set.Ici (1 : ℝ), ∀ x₂ ∈ Set.Ici (1 : ℝ),
      |x₁ - x₂| < δ → (1 / 2 : ℝ) * (2 * ε) = ε := by
  intro ε hε
  refine ⟨1, zero_lt_one, ?_⟩
  intro x₁ hx₁ x₂ hx₂ hdist
  ring

/-- Source: `proof_gap/exercise_799/6`; repair the modulus quantifier order. -/
theorem gap6 :
    ∀ ε > 0, ∃ δ > 0, ∀ x₁ ∈ Set.Ici (1 : ℝ), ∀ x₂ ∈ Set.Ici (1 : ℝ),
      |x₁ - x₂| < δ → |Real.sqrt x₁ - Real.sqrt x₂| < ε := by
  intro ε hε
  obtain ⟨δ, hδ, hmod⟩ := gap4 ε hε
  refine ⟨δ, hδ, ?_⟩
  intro x₁ hx₁ x₂ hx₂ hdist
  calc
    |Real.sqrt x₁ - Real.sqrt x₂| < (1 / 2 : ℝ) * (2 * ε) :=
      hmod x₁ hx₁ x₂ hx₂ hdist
    _ = ε := by ring

/-- Source: `proof_gap/exercise_799/7.txt`; replace the unbound `f` by the
specified square-root function. -/
theorem gap7 : UniformContinuousOn Real.sqrt (Set.Ici (1 : ℝ)) := by
  rw [Metric.uniformContinuousOn_iff]
  intro ε hε
  obtain ⟨δ, hδ, hmod⟩ := gap6 ε hε
  refine ⟨δ, hδ, ?_⟩
  intro x₁ hx₁ x₂ hx₂ hdist
  have habs : |x₁ - x₂| < δ := by
    simpa only [Real.dist_eq] using hdist
  simpa only [Real.dist_eq] using hmod x₁ hx₁ x₂ hx₂ habs

/-- Source: `proof_gap/exercise_799/8.txt`. -/
theorem gap8 : UniformContinuousOn Real.sqrt (Set.Ici (1 : ℝ)) := by
  exact gap7

end ProofGap.Exercise799
