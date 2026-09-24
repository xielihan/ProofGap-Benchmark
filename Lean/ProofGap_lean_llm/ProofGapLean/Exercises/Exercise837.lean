import ProofGapLean.Prelude.Sequences
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise837

noncomputable section

def y (a b : ℝ) (x : ℝ) : ℝ := (a * x + b) / (a + b)

/-- Exercise 837, gap 1; state the derivative formula before solving its zero set. -/
theorem gap1 (a b x : ℝ) (hab : a + b ≠ 0) :
    deriv (y a b) x = a / (a + b) := by
  unfold y
  have hfun :
      (fun t : ℝ => (a * t + b) / (a + b)) =
        (fun t : ℝ => (a / (a + b)) * t + b / (a + b)) := by
    funext t
    ring
  rw [hfun]
  convert
    ((((hasDerivAt_const x (a / (a + b))).mul (hasDerivAt_id x)).add
      (hasDerivAt_const x (b / (a + b)))).deriv) using 1 <;> ring

/-- Exercise 837, gap 2; retain the parameter-degenerate critical set explicitly. -/
theorem gap2 (a b x : ℝ) (hab : a + b ≠ 0) :
    x ∈ {z : ℝ | a / (a + b) = 0} ↔ deriv (y a b) x = 0 := by
  change a / (a + b) = 0 ↔ deriv (y a b) x = 0
  rw [gap1 a b x hab]

end

end ProofGap.Exercise837
