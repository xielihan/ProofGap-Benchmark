import ProofGapLean.Prelude.Elementary
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise218

noncomputable section

def f (x : ℝ) : ℝ := Real.cos x
def domain : Set ℝ := Set.Icc 0 Real.pi

/-- Source: `proof_gap/exercise_218/1.txt`. -/
theorem gap1 : ∀ x₁ x₂, f x₂ - f x₁ = Real.cos x₂ - Real.cos x₁ := by
  intro x₁ x₂
  rfl

/-- Source: `proof_gap/exercise_218/2.txt`. -/
theorem gap2 : ∀ x₁ x₂ : ℝ,
    Real.cos x₂ - Real.cos x₁ =
      -2 * Real.sin ((x₂ + x₁) / 2) * Real.sin ((x₂ - x₁) / 2) := by
  intro x₁ x₂
  let u : ℝ := (x₂ + x₁) / 2
  let v : ℝ := (x₂ - x₁) / 2
  have h₂ : x₂ = u + v := by
    dsimp [u, v]
    ring
  have h₁ : x₁ = u - v := by
    dsimp [u, v]
    ring
  calc
    Real.cos x₂ - Real.cos x₁ =
        Real.cos (u + v) - Real.cos (u - v) := by rw [h₂, h₁]
    _ = -2 * Real.sin ((x₂ + x₁) / 2) *
          Real.sin ((x₂ - x₁) / 2) := by
      rw [Real.cos_add, Real.cos_sub]
      dsimp [u, v]
      ring

/-- Source: `proof_gap/exercise_218/3.txt`. -/
theorem gap3 : ∀ x₁ x₂,
    f x₂ - f x₁ =
      -2 * Real.sin ((x₂ + x₁) / 2) * Real.sin ((x₂ - x₁) / 2) := by
  intro x₁ x₂
  simpa [f] using (gap2 x₁ x₂)

/-- Source: `proof_gap/exercise_218/4.txt`. -/
theorem gap4 : ∀ x₁ x₂ : ℝ, 0 < x₁ → x₁ < x₂ → x₂ < Real.pi →
    0 < (x₁ + x₂) / 2 := by
  intro x₁ x₂ hx₁ hx₁₂ hx₂
  linarith

/-- Source: `proof_gap/exercise_218/5.txt`. -/
theorem gap5 : ∀ x₁ x₂ : ℝ, 0 < x₁ → x₁ < x₂ → x₂ < Real.pi →
    (x₁ + x₂) / 2 < Real.pi := by
  intro x₁ x₂ hx₁ hx₁₂ hx₂
  linarith

/-- Source: `proof_gap/exercise_218/6.txt`. -/
theorem gap6 : ∀ x₁ x₂ : ℝ, 0 < x₁ → x₁ < x₂ → x₂ < Real.pi →
    0 < (x₂ - x₁) / 2 := by
  intro x₁ x₂ hx₁ hx₁₂ hx₂
  linarith

/-- Source: `proof_gap/exercise_218/7.txt`. -/
theorem gap7 : ∀ x₁ x₂ : ℝ, 0 < x₁ → x₁ < x₂ → x₂ < Real.pi →
    (x₂ - x₁) / 2 < Real.pi / 2 := by
  intro x₁ x₂ hx₁ hx₁₂ hx₂
  linarith

/-- Source: `proof_gap/exercise_218/8.txt`. -/
theorem gap8 : ∀ x₁ x₂ : ℝ, 0 < x₁ → x₁ < x₂ → x₂ < Real.pi →
    0 < Real.sin ((x₁ + x₂) / 2) := by
  intro x₁ x₂ hx₁ hx₁₂ hx₂
  exact Real.sin_pos_of_pos_of_lt_pi
    (gap4 x₁ x₂ hx₁ hx₁₂ hx₂)
    (gap5 x₁ x₂ hx₁ hx₁₂ hx₂)

/-- Source: `proof_gap/exercise_218/9.txt`. -/
theorem gap9 : ∀ x₁ x₂ : ℝ, 0 < x₁ → x₁ < x₂ → x₂ < Real.pi →
    0 < Real.sin ((x₂ - x₁) / 2) := by
  intro x₁ x₂ hx₁ hx₁₂ hx₂
  apply Real.sin_pos_of_pos_of_lt_pi
  · exact gap6 x₁ x₂ hx₁ hx₁₂ hx₂
  · have hhalf := gap7 x₁ x₂ hx₁ hx₁₂ hx₂
    have hpi := Real.pi_pos
    linarith

/-- Source: `proof_gap/exercise_218/10.txt`. -/
theorem gap10 : ∀ x₁ x₂ : ℝ, 0 < x₁ → x₁ < x₂ → x₂ < Real.pi →
    f x₂ - f x₁ < 0 := by
  intro x₁ x₂ hx₁ hx₁₂ hx₂
  rw [gap3 x₁ x₂]
  have hs₁ : 0 < Real.sin ((x₂ + x₁) / 2) := by
    simpa [add_comm] using (gap8 x₁ x₂ hx₁ hx₁₂ hx₂)
  have hs₂ : 0 < Real.sin ((x₂ - x₁) / 2) :=
    gap9 x₁ x₂ hx₁ hx₁₂ hx₂
  have hneg : (-2 : ℝ) < 0 := by
    linarith
  exact mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hneg hs₁) hs₂

/-- Source: `proof_gap/exercise_218/11.txt`. -/
theorem gap11 : StrictAntiOn f domain := by
  intro x hx y hy hxy
  change x ∈ Set.Icc 0 Real.pi at hx
  change y ∈ Set.Icc 0 Real.pi at hy
  rcases hx with ⟨hx0, hxpi⟩
  rcases hy with ⟨hy0, hypi⟩
  have hpi : 0 < Real.pi := Real.pi_pos
  have havg0 : 0 < (x + y) / 2 := by
    linarith
  have havgpi : (x + y) / 2 < Real.pi := by
    linarith
  have hdiff0 : 0 < (y - x) / 2 := by
    linarith
  have hdiffpi : (y - x) / 2 < Real.pi := by
    linarith
  have hs₁ : 0 < Real.sin ((y + x) / 2) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · simpa [add_comm] using havg0
    · simpa [add_comm] using havgpi
  have hs₂ : 0 < Real.sin ((y - x) / 2) :=
    Real.sin_pos_of_pos_of_lt_pi hdiff0 hdiffpi
  have hdiff : f y - f x < 0 := by
    rw [gap3 x y]
    have hneg : (-2 : ℝ) < 0 := by
      linarith
    exact mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hneg hs₁) hs₂
  exact sub_neg.mp hdiff

/-- Source: `proof_gap/exercise_218/12.txt`. -/
theorem gap12 : StrictAntiOn f domain := by
  exact gap11

end

end ProofGap.Exercise218
