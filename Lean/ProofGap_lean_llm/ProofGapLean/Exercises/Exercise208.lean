import ProofGapLean.Prelude.Core
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

namespace ProofGap.Exercise208

noncomputable section

def f (x : ℝ) : ℝ := 1 / (1 - x)

/-- Source: `proof_gap/exercise_208/1.txt`; exclude poles of both iterates. -/
theorem gap1 : ∀ x : ℝ, x ≠ 0 → x ≠ 1 →
    f (f x) = 1 / (1 - 1 / (1 - x)) := by
  intro x hx0 hx1
  rfl

/-- Source: `proof_gap/exercise_208/2.txt`. -/
theorem gap2 : ∀ x : ℝ, x ≠ 0 → x ≠ 1 →
    1 / (1 - 1 / (1 - x)) = 1 - 1 / x := by
  intro x hx0 hx1
  have hden : 1 - x ≠ 0 := by
    intro h
    apply hx1
    linarith
  field_simp [hx0, hden]
  ring

/-- Source: `proof_gap/exercise_208/3.txt`. -/
theorem gap3 : ∀ x : ℝ, x ≠ 0 → x ≠ 1 → f (f x) = 1 - 1 / x := by
  intro x hx0 hx1
  rw [gap1 x hx0 hx1, gap2 x hx0 hx1]

/-- Source: `proof_gap/exercise_208/4.txt`. -/
theorem gap4 : ∀ x : ℝ, x ≠ 0 → x ≠ 1 →
    f (f (f x)) = 1 / (1 - (1 - 1 / x)) := by
  intro x hx0 hx1
  rw [show f (f (f x)) = f (1 - 1 / x) by rw [gap3 x hx0 hx1]]
  rfl

/-- Source: `proof_gap/exercise_208/5.txt`. -/
theorem gap5 : ∀ x : ℝ, x ≠ 0 → 1 / (1 - (1 - 1 / x)) = x := by
  intro x hx0
  field_simp [hx0]
  ring

/-- Source: `proof_gap/exercise_208/6.txt`; the Möbius map has order three off its poles. -/
theorem gap6 : ∀ x : ℝ, x ≠ 0 → x ≠ 1 → f (f (f x)) = x := by
  intro x hx0 hx1
  rw [gap4 x hx0 hx1, gap5 x hx0]

end

end ProofGap.Exercise208
