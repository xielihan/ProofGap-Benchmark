import ProofGapLean.Prelude.Elementary
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise155

noncomputable section

def phaseCondition (x : ℝ) : Prop :=
  ∃ k : ℕ, 2 * (k : ℝ) * Real.pi ≤ Real.sqrt x ∧
    Real.sqrt x ≤ (2 * (k : ℝ) + 1) * Real.pi

def domain : Set ℝ := {x | 0 ≤ x ∧ phaseCondition x}

/-- Source: `proof_gap/exercise_155/1.txt`; nonnegativity is conditional, not universal. -/
theorem gap1 : ∀ x : ℝ, x ∈ domain → 0 ≤ Real.sin (Real.sqrt x) := by
  intro x hx
  rcases hx.2 with ⟨k, hklo, hkhi⟩
  let t := Real.sqrt x - (k : ℝ) * (2 * Real.pi)
  have ht0 : 0 ≤ t := by
    dsimp [t]
    linarith
  have htpi : t ≤ Real.pi := by
    dsimp [t]
    linarith
  have hsin : 0 ≤ Real.sin t :=
    Real.sin_nonneg_of_nonneg_of_le_pi ht0 htpi
  have harg : t + (k : ℝ) * (2 * Real.pi) = Real.sqrt x := by
    dsimp [t]
    ring
  rw [← harg]
  simpa only using hsin.trans_eq (Real.sin_add_nat_mul_two_pi t k).symm

/-- Source: `proof_gap/exercise_155/2.txt`; k is existentially chosen for each domain point. -/
theorem gap2 : ∀ x : ℝ, x ∈ domain ↔
    0 ≤ x ∧ ∃ k : ℕ, 2 * (k : ℝ) * Real.pi ≤ Real.sqrt x ∧
      Real.sqrt x ≤ (2 * (k : ℝ) + 1) * Real.pi := by
  intro x
  rfl

/-- Source: `proof_gap/exercise_155/3.txt`; squaring the nonnegative endpoints. -/
theorem gap3 : ∀ x : ℝ, x ∈ domain ↔
    ∃ k : ℕ, 4 * (k : ℝ) ^ 2 * Real.pi ^ 2 ≤ x ∧
      x ≤ (2 * (k : ℝ) + 1) ^ 2 * Real.pi ^ 2 := by
  intro x
  constructor
  · rintro ⟨hx0, k, hklo, hkhi⟩
    have hleft0 : 0 ≤ 2 * (k : ℝ) * Real.pi := by positivity
    have hright0 : 0 ≤ (2 * (k : ℝ) + 1) * Real.pi := by positivity
    have hl_sq :
        (2 * (k : ℝ) * Real.pi) ^ 2 ≤ (Real.sqrt x) ^ 2 :=
      (sq_le_sq₀ hleft0 (Real.sqrt_nonneg x)).2 hklo
    have hu_sq :
        (Real.sqrt x) ^ 2 ≤ ((2 * (k : ℝ) + 1) * Real.pi) ^ 2 :=
      (sq_le_sq₀ (Real.sqrt_nonneg x) hright0).2 hkhi
    rw [Real.sq_sqrt hx0] at hl_sq hu_sq
    refine ⟨k, ?_, ?_⟩
    · nlinarith
    · nlinarith
  · rintro ⟨k, hklo, hkhi⟩
    have hx0 : 0 ≤ x := le_trans (by positivity) hklo
    have hleft0 : 0 ≤ 2 * (k : ℝ) * Real.pi := by positivity
    have hright0 : 0 ≤ (2 * (k : ℝ) + 1) * Real.pi := by positivity
    have hsqrt_sq : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt hx0
    have hlow_sq :
        (2 * (k : ℝ) * Real.pi) ^ 2 ≤ (Real.sqrt x) ^ 2 := by
      rw [hsqrt_sq]
      nlinarith
    have hupp_sq :
        (Real.sqrt x) ^ 2 ≤ ((2 * (k : ℝ) + 1) * Real.pi) ^ 2 := by
      rw [hsqrt_sq]
      nlinarith
    refine ⟨hx0, k, ?_, ?_⟩
    · exact (sq_le_sq₀ hleft0 (Real.sqrt_nonneg x)).1 hlow_sq
    · exact (sq_le_sq₀ (Real.sqrt_nonneg x) hright0).1 hupp_sq

/-- Source: `proof_gap/exercise_155/4.txt`. -/
theorem gap4 :
    domain =
      {x : ℝ | ∃ k : ℕ, 4 * (k : ℝ) ^ 2 * Real.pi ^ 2 ≤ x ∧
        x ≤ (2 * (k : ℝ) + 1) ^ 2 * Real.pi ^ 2} := by
  ext x
  exact gap3 x

end

end ProofGap.Exercise155
