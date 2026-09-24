import ProofGapLean.Prelude.Elementary

namespace ProofGap.Exercise231_3

noncomputable section

def f (a x : ℝ) : ℝ := Real.rpow a x + Real.rpow a (-x)

/-- Source: `proof_gap/exercise_231_3/1.txt`. -/
theorem gap1 (a : ℝ) (ha : 0 < a) : ∀ x,
    f a (-x) = Real.rpow a (-x) + Real.rpow a x := by
  intro x
  simp [f]

/-- Source: `proof_gap/exercise_231_3/2.txt`. -/
theorem gap2 (a : ℝ) (ha : 0 < a) : ∀ x,
    Real.rpow a (-x) + Real.rpow a x = f a x := by
  intro x
  simp [f, add_comm]

/-- Source: `proof_gap/exercise_231_3/3.txt`. -/
theorem gap3 (a : ℝ) (ha : 0 < a) : ∀ x, f a (-x) = f a x := by
  intro x
  rw [gap1 a ha x, gap2 a ha x]

/-- Source: `proof_gap/exercise_231_3/4.txt`. -/
theorem gap4 (a : ℝ) (ha : 0 < a) : Function.Even (f a) := by
  intro x
  exact gap3 a ha x

end

end ProofGap.Exercise231_3
