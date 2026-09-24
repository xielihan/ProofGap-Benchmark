import ProofGapLean.Prelude.Elementary
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

namespace ProofGap.Exercise214

noncomputable section

def f (x : ℝ) : ℝ := Real.sin x
def domain : Set ℝ := Set.Icc (-Real.pi / 2) (Real.pi / 2)

/-- Source: `proof_gap/exercise_214/1.txt`. -/
theorem gap1 : ∀ x₁ x₂ : ℝ, -Real.pi / 2 < x₁ → x₁ < x₂ → x₂ < Real.pi / 2 →
    -Real.pi / 2 < (x₁ + x₂) / 2 := by
  intro x₁ x₂ hx₁ hx₁₂ hx₂
  linarith

/-- Source: `proof_gap/exercise_214/2.txt`. -/
theorem gap2 : ∀ x₁ x₂ : ℝ, -Real.pi / 2 < x₁ → x₁ < x₂ → x₂ < Real.pi / 2 →
    (x₁ + x₂) / 2 < Real.pi / 2 := by
  intro x₁ x₂ hx₁ hx₁₂ hx₂
  linarith

/-- Source: `proof_gap/exercise_214/3.txt`. -/
theorem gap3 : ∀ x₁ x₂ : ℝ, -Real.pi / 2 < x₁ → x₁ < x₂ → x₂ < Real.pi / 2 →
    0 < (x₂ - x₁) / 2 := by
  intro x₁ x₂ hx₁ hx₁₂ hx₂
  linarith

/-- Source: `proof_gap/exercise_214/4.txt`. -/
theorem gap4 : ∀ x₁ x₂ : ℝ, -Real.pi / 2 < x₁ → x₁ < x₂ → x₂ < Real.pi / 2 →
    (x₂ - x₁) / 2 < Real.pi / 2 := by
  intro x₁ x₂ hx₁ hx₁₂ hx₂
  have hpi : 0 < Real.pi := Real.pi_pos
  linarith

/-- Source: `proof_gap/exercise_214/5.txt`. -/
theorem gap5 : ∀ x₁ x₂ : ℝ, -Real.pi / 2 < x₁ → x₁ < x₂ → x₂ < Real.pi / 2 →
    0 < Real.cos ((x₁ + x₂) / 2) := by
  intro x₁ x₂ hx₁ hx₁₂ hx₂
  apply Real.cos_pos_of_mem_Ioo
  constructor
  · have h := gap1 x₁ x₂ hx₁ hx₁₂ hx₂
    linarith
  · exact gap2 x₁ x₂ hx₁ hx₁₂ hx₂

/-- Source: `proof_gap/exercise_214/6.txt`. -/
theorem gap6 : ∀ x₁ x₂ : ℝ, -Real.pi / 2 < x₁ → x₁ < x₂ → x₂ < Real.pi / 2 →
    0 < Real.sin ((x₂ - x₁) / 2) := by
  intro x₁ x₂ hx₁ hx₁₂ hx₂
  apply Real.sin_pos_of_pos_of_lt_pi
  · exact gap3 x₁ x₂ hx₁ hx₁₂ hx₂
  · have h := gap4 x₁ x₂ hx₁ hx₁₂ hx₂
    have hpi : 0 < Real.pi := Real.pi_pos
    linarith

/-- Source: `proof_gap/exercise_214/7.txt`. -/
theorem gap7 : ∀ x₁ x₂ : ℝ, f x₂ - f x₁ = Real.sin x₂ - Real.sin x₁ := by
  intro x₁ x₂
  rfl

/-- Source: `proof_gap/exercise_214/8.txt`. -/
theorem gap8 : ∀ x₁ x₂ : ℝ,
    Real.sin x₂ - Real.sin x₁ =
      2 * Real.cos ((x₂ + x₁) / 2) * Real.sin ((x₂ - x₁) / 2) := by
  intro x₁ x₂
  let a : ℝ := (x₂ + x₁) / 2
  let b : ℝ := (x₂ - x₁) / 2
  have hx₂ : x₂ = a + b := by
    dsimp [a, b]
    ring
  have hx₁ : x₁ = a - b := by
    dsimp [a, b]
    ring
  rw [hx₂, hx₁, Real.sin_add, Real.sin_sub]
  dsimp [a, b]
  ring

/-- Source: `proof_gap/exercise_214/9.txt`. -/
theorem gap9 : ∀ x₁ x₂ : ℝ, -Real.pi / 2 < x₁ → x₁ < x₂ → x₂ < Real.pi / 2 →
    0 < 2 * Real.cos ((x₂ + x₁) / 2) * Real.sin ((x₂ - x₁) / 2) := by
  intro x₁ x₂ hx₁ hx₁₂ hx₂
  have hcos : 0 < Real.cos ((x₂ + x₁) / 2) := by
    simpa [add_comm] using gap5 x₁ x₂ hx₁ hx₁₂ hx₂
  have hsin : 0 < Real.sin ((x₂ - x₁) / 2) :=
    gap6 x₁ x₂ hx₁ hx₁₂ hx₂
  positivity

/-- Source: `proof_gap/exercise_214/10.txt`. -/
theorem gap10 : ∀ x₁ x₂ : ℝ, -Real.pi / 2 < x₁ → x₁ < x₂ → x₂ < Real.pi / 2 →
    0 < f x₂ - f x₁ := by
  intro x₁ x₂ hx₁ hx₁₂ hx₂
  rw [gap7 x₁ x₂, gap8 x₁ x₂]
  exact gap9 x₁ x₂ hx₁ hx₁₂ hx₂

/-- Source: `proof_gap/exercise_214/11.txt`. -/
theorem gap11 : StrictMonoOn f domain := by
  intro x₁ hx₁ x₂ hx₂ hx₁₂
  rcases hx₁ with ⟨hx₁low, hx₁high⟩
  rcases hx₂ with ⟨hx₂low, hx₂high⟩
  have havg_lower : -(Real.pi / 2) < (x₂ + x₁) / 2 := by
    linarith
  have havg_upper : (x₂ + x₁) / 2 < Real.pi / 2 := by
    linarith
  have hcos : 0 < Real.cos ((x₂ + x₁) / 2) := by
    apply Real.cos_pos_of_mem_Ioo
    exact ⟨havg_lower, havg_upper⟩
  have hhalf_pos : 0 < (x₂ - x₁) / 2 := by
    linarith
  have hhalf_lt_pi : (x₂ - x₁) / 2 < Real.pi := by
    have hpi : 0 < Real.pi := Real.pi_pos
    linarith
  have hsin : 0 < Real.sin ((x₂ - x₁) / 2) := by
    exact Real.sin_pos_of_pos_of_lt_pi hhalf_pos hhalf_lt_pi
  have hdiff : 0 < f x₂ - f x₁ := by
    rw [gap7 x₁ x₂, gap8 x₁ x₂]
    positivity
  linarith

/-- Source: `proof_gap/exercise_214/12.txt`. -/
theorem gap12 : StrictMonoOn f domain := by
  exact gap11

end

end ProofGap.Exercise214
