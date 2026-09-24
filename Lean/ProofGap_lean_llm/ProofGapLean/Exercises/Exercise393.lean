import ProofGapLean.Prelude.Elementary
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise393

noncomputable section

def f (x : ℝ) : ℝ := Real.sin x + Real.cos x
def rangeOnPeriod : Set ℝ :=
  {y | ∃ x ∈ Set.Icc (0 : ℝ) (2 * Real.pi), y = f x}

/-- Source: `proof_gap/exercise_393/1.txt`. -/
theorem gap1 : ∀ x,
    f x = Real.sqrt 2 * Real.sin (x + Real.pi / 4) := by
  intro x
  unfold f
  rw [Real.sin_add, Real.sin_pi_div_four, Real.cos_pi_div_four]
  have hsq : Real.sqrt (2 : ℝ) ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num)
  calc
    Real.sin x + Real.cos x =
        Real.sqrt 2 ^ 2 / 2 * (Real.sin x + Real.cos x) := by
          rw [hsq]
          ring
    _ = Real.sqrt 2 *
        (Real.sin x * (Real.sqrt 2 / 2) +
          Real.cos x * (Real.sqrt 2 / 2)) := by ring

/-- Source: `proof_gap/exercise_393/2.txt`. -/
theorem gap2 : sInf rangeOnPeriod = -Real.sqrt 2 := by
  have hsqrt : 0 ≤ Real.sqrt (2 : ℝ) := Real.sqrt_nonneg _
  have hlower : ∀ y ∈ rangeOnPeriod, -Real.sqrt 2 ≤ y := by
    intro y hy
    change ∃ x ∈ Set.Icc (0 : ℝ) (2 * Real.pi), y = f x at hy
    rcases hy with ⟨x, hx, rfl⟩
    rw [gap1]
    have h := mul_le_mul_of_nonneg_left
      (Real.neg_one_le_sin (x + Real.pi / 4)) hsqrt
    simpa using h
  have hbdd : BddBelow rangeOnPeriod := by
    refine ⟨-Real.sqrt 2, ?_⟩
    intro y hy
    exact hlower y hy
  have hmin : -Real.sqrt 2 ∈ rangeOnPeriod := by
    change ∃ x ∈ Set.Icc (0 : ℝ) (2 * Real.pi), -Real.sqrt 2 = f x
    refine ⟨5 * Real.pi / 4, ?_, ?_⟩
    · constructor <;> nlinarith [Real.pi_pos]
    · rw [gap1]
      have harg :
          5 * Real.pi / 4 + Real.pi / 4 = Real.pi + Real.pi / 2 := by
        ring
      rw [harg, Real.sin_add, Real.sin_pi, Real.cos_pi,
        Real.sin_pi_div_two, Real.cos_pi_div_two]
      ring
  apply le_antisymm
  · exact csInf_le hbdd hmin
  · apply le_csInf
    · exact ⟨_, hmin⟩
    · intro y hy
      exact hlower y hy

/-- Source: `proof_gap/exercise_393/3.txt`. -/
theorem gap3 : sSup rangeOnPeriod = Real.sqrt 2 := by
  have hsqrt : 0 ≤ Real.sqrt (2 : ℝ) := Real.sqrt_nonneg _
  have hupper : ∀ y ∈ rangeOnPeriod, y ≤ Real.sqrt 2 := by
    intro y hy
    change ∃ x ∈ Set.Icc (0 : ℝ) (2 * Real.pi), y = f x at hy
    rcases hy with ⟨x, hx, rfl⟩
    rw [gap1]
    have h := mul_le_mul_of_nonneg_left
      (Real.sin_le_one (x + Real.pi / 4)) hsqrt
    simpa using h
  have hbdd : BddAbove rangeOnPeriod := by
    refine ⟨Real.sqrt 2, ?_⟩
    intro y hy
    exact hupper y hy
  have hmax : Real.sqrt 2 ∈ rangeOnPeriod := by
    change ∃ x ∈ Set.Icc (0 : ℝ) (2 * Real.pi), Real.sqrt 2 = f x
    refine ⟨Real.pi / 4, ?_, ?_⟩
    · constructor <;> nlinarith [Real.pi_pos]
    · rw [gap1]
      have harg : Real.pi / 4 + Real.pi / 4 = Real.pi / 2 := by
        ring
      rw [harg, Real.sin_pi_div_two]
      ring
  apply le_antisymm
  · apply csSup_le
    · exact ⟨_, hmax⟩
    · intro y hy
      exact hupper y hy
  · exact le_csSup hbdd hmax

end

end ProofGap.Exercise393
