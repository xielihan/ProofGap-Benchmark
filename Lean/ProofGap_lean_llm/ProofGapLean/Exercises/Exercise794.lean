import ProofGapLean.Prelude.Sequences
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise794

noncomputable section

def f (x : ℝ) : ℝ := x / (4 - x ^ 2)

/-- Source: `proof_gap/exercise_794/1.txt`. -/
theorem gap1 (x₁ x₂ : ℝ) (hx₁ : x₁ ∈ Set.Icc (-1 : ℝ) 1)
    (hx₂ : x₂ ∈ Set.Icc (-1 : ℝ) 1) :
    |f x₁ - f x₂| = |x₁ / (4 - x₁ ^ 2) - x₂ / (4 - x₂ ^ 2)| := by
  rfl

/-- Source: `proof_gap/exercise_794/2.txt`. -/
theorem gap2 (x₁ x₂ : ℝ) (hx₁ : x₁ ∈ Set.Icc (-1 : ℝ) 1)
    (hx₂ : x₂ ∈ Set.Icc (-1 : ℝ) 1) :
    |x₁ / (4 - x₁ ^ 2) - x₂ / (4 - x₂ ^ 2)| =
      |(4 + x₁ * x₂) / ((4 - x₁ ^ 2) * (4 - x₂ ^ 2))| * |x₁ - x₂| := by
  have hp₁ : 0 ≤ (x₁ + 1) * (1 - x₁) := by
    exact mul_nonneg (by linarith [hx₁.1]) (by linarith [hx₁.2])
  have hp₂ : 0 ≤ (x₂ + 1) * (1 - x₂) := by
    exact mul_nonneg (by linarith [hx₂.1]) (by linarith [hx₂.2])
  have hd₁pos : 0 < 4 - x₁ ^ 2 := by
    nlinarith [hp₁]
  have hd₂pos : 0 < 4 - x₂ ^ 2 := by
    nlinarith [hp₂]
  have hd₁ : 4 - x₁ ^ 2 ≠ 0 := ne_of_gt hd₁pos
  have hd₂ : 4 - x₂ ^ 2 ≠ 0 := ne_of_gt hd₂pos
  have hident :
      x₁ / (4 - x₁ ^ 2) - x₂ / (4 - x₂ ^ 2) =
        ((4 + x₁ * x₂) / ((4 - x₁ ^ 2) * (4 - x₂ ^ 2))) * (x₁ - x₂) := by
    field_simp [hd₁, hd₂] <;> ring
  rw [hident, abs_mul]

/-- Source: `proof_gap/exercise_794/3.txt`. -/
theorem gap3 (x₁ x₂ : ℝ) (hx₁ : x₁ ∈ Set.Icc (-1 : ℝ) 1)
    (hx₂ : x₂ ∈ Set.Icc (-1 : ℝ) 1) :
    |f x₁ - f x₂| =
      |(4 + x₁ * x₂) / ((4 - x₁ ^ 2) * (4 - x₂ ^ 2))| * |x₁ - x₂| := by
  calc
    |f x₁ - f x₂| = |x₁ / (4 - x₁ ^ 2) - x₂ / (4 - x₂ ^ 2)| :=
      gap1 x₁ x₂ hx₁ hx₂
    _ = |(4 + x₁ * x₂) / ((4 - x₁ ^ 2) * (4 - x₂ ^ 2))| * |x₁ - x₂| :=
      gap2 x₁ x₂ hx₁ hx₂

/-- Source: `proof_gap/exercise_794/4.txt`; correct strict `<5/9` to `≤5/9` at the endpoints. -/
theorem gap4 (x₁ x₂ : ℝ) (hx₁ : x₁ ∈ Set.Icc (-1 : ℝ) 1)
    (hx₂ : x₂ ∈ Set.Icc (-1 : ℝ) 1) :
    |(4 + x₁ * x₂) / ((4 - x₁ ^ 2) * (4 - x₂ ^ 2))| ≤ (4 + 1 : ℝ) / (3 * 3) := by
  have hx₁abs : |x₁| ≤ 1 := (abs_le).2 hx₁
  have hx₂abs : |x₂| ≤ 1 := (abs_le).2 hx₂
  have hxyabs : |x₁ * x₂| ≤ 1 := by
    calc
      |x₁ * x₂| = |x₁| * |x₂| := abs_mul x₁ x₂
      _ ≤ 1 * 1 := mul_le_mul hx₁abs hx₂abs (abs_nonneg x₂) (by norm_num)
      _ = 1 := by norm_num
  have hxy : -1 ≤ x₁ * x₂ ∧ x₁ * x₂ ≤ 1 := (abs_le).1 hxyabs
  have hp₁ : 0 ≤ (x₁ + 1) * (1 - x₁) := by
    exact mul_nonneg (by linarith [hx₁.1]) (by linarith [hx₁.2])
  have hp₂ : 0 ≤ (x₂ + 1) * (1 - x₂) := by
    exact mul_nonneg (by linarith [hx₂.1]) (by linarith [hx₂.2])
  have hd₁ : 3 ≤ 4 - x₁ ^ 2 := by
    nlinarith [hp₁]
  have hd₂ : 3 ≤ 4 - x₂ ^ 2 := by
    nlinarith [hp₂]
  have hden :
      (3 : ℝ) * 3 ≤ (4 - x₁ ^ 2) * (4 - x₂ ^ 2) :=
    mul_le_mul hd₁ hd₂ (by norm_num) (by nlinarith [hd₁])
  have hden_pos : 0 < (4 - x₁ ^ 2) * (4 - x₂ ^ 2) := by
    nlinarith [hden]
  have hnum_nonneg : 0 ≤ 4 + x₁ * x₂ := by
    nlinarith [hxy.1]
  have hnum_le : 4 + x₁ * x₂ ≤ 5 := by
    nlinarith [hxy.2]
  rw [abs_of_nonneg (div_nonneg hnum_nonneg (le_of_lt hden_pos))]
  apply (div_le_iff₀ hden_pos).2
  norm_num
  nlinarith [hnum_le, hden]

/-- Source: `proof_gap/exercise_794/5.txt`; remove irrelevant quantified points. -/
theorem gap5 : (4 + 1 : ℝ) / (3 * 3) = 5 / 9 := by
  norm_num

/-- Source: `proof_gap/exercise_794/6.txt`; remove irrelevant quantified points. -/
theorem gap6 : (5 / 9 : ℝ) < 1 := by
  norm_num

/-- Source: `proof_gap/exercise_794/7.txt`. -/
theorem gap7 (x₁ x₂ : ℝ) (hx₁ : x₁ ∈ Set.Icc (-1 : ℝ) 1)
    (hx₂ : x₂ ∈ Set.Icc (-1 : ℝ) 1) :
    |(4 + x₁ * x₂) / ((4 - x₁ ^ 2) * (4 - x₂ ^ 2))| < 1 := by
  calc
    |(4 + x₁ * x₂) / ((4 - x₁ ^ 2) * (4 - x₂ ^ 2))| ≤ (4 + 1 : ℝ) / (3 * 3) :=
      gap4 x₁ x₂ hx₁ hx₂
    _ = 5 / 9 := gap5
    _ < 1 := gap6

/-- Source: `proof_gap/exercise_794/8.txt`; move `δ` under `ε`. -/
theorem gap8 :
    ∀ ε > 0, ∃ δ > 0, ∀ x₁ ∈ Set.Icc (-1 : ℝ) 1,
      ∀ x₂ ∈ Set.Icc (-1 : ℝ) 1,
        |x₁ - x₂| < δ → |f x₁ - f x₂| < ε := by
  intro ε hε
  refine ⟨ε, hε, ?_⟩
  intro x₁ hx₁ x₂ hx₂ hdist
  have hcoeff :
      |(4 + x₁ * x₂) / ((4 - x₁ ^ 2) * (4 - x₂ ^ 2))| < 1 :=
    gap7 x₁ x₂ hx₁ hx₂
  have hprod :
      |(4 + x₁ * x₂) / ((4 - x₁ ^ 2) * (4 - x₂ ^ 2))| * |x₁ - x₂| ≤
        |x₁ - x₂| := by
    nlinarith [mul_nonneg
      (sub_nonneg.mpr (le_of_lt hcoeff)) (abs_nonneg (x₁ - x₂))]
  calc
    |f x₁ - f x₂| =
        |(4 + x₁ * x₂) / ((4 - x₁ ^ 2) * (4 - x₂ ^ 2))| * |x₁ - x₂| :=
      gap3 x₁ x₂ hx₁ hx₂
    _ ≤ |x₁ - x₂| := hprod
    _ < ε := hdist

/-- Source: `proof_gap/exercise_794/9.txt`. -/
theorem gap9 : UniformContinuousOn f (Set.Icc (-1 : ℝ) 1) := by
  apply Metric.uniformContinuousOn_iff.mpr
  simpa only [Real.dist_eq] using gap8

/-- Source: `proof_gap/exercise_794/10.txt`. -/
theorem gap10 : UniformContinuousOn f (Set.Icc (-1 : ℝ) 1) := by
  exact gap9

end

end ProofGap.Exercise794
