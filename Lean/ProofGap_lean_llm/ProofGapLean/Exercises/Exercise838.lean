import ProofGapLean.Prelude.Sequences
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace ProofGap.Exercise838

noncomputable section

def y (a b : ℝ) (x : ℝ) : ℝ := (x - a) * (x - b)

/-- Exercise 838, gap 1; correct the source's illogical `0↔derivative` chain to a derivative identity. -/
theorem gap1 (a b x : ℝ) :
    deriv (y a b) x = (x - a) + (x - b) := by
  change deriv (fun z : ℝ => (z - a) * (z - b)) x = (x - a) + (x - b)
  have hderiv :
      deriv (fun z : ℝ => (z - a) * (z - b)) x =
        1 * (x - b) + (x - a) * 1 :=
    (((hasDerivAt_id x).sub_const a).mul
      ((hasDerivAt_id x).sub_const b)).deriv
  calc
    deriv (fun z : ℝ => (z - a) * (z - b)) x =
        1 * (x - b) + (x - a) * 1 := hderiv
    _ = (x - a) + (x - b) := by ring

/-- Exercise 838, gap 2; state the algebraic identity directly. -/
theorem gap2 (a b x : ℝ) :
    (x - a) + (x - b) = 2 * x - a - b := by
  ring

/-- Exercise 838, gap 3; state the derivative identity directly. -/
theorem gap3 (a b x : ℝ) :
    deriv (y a b) x = 2 * x - a - b := by
  rw [gap1, gap2]

/-- Exercise 838, gap 4. -/
theorem gap4 (a b x : ℝ) :
    deriv (y a b) x = 0 ↔ 2 * x - a - b = 0 := by
  rw [gap3]

/-- Exercise 838, gap 5. -/
theorem gap5 (a b x : ℝ) :
    x ∈ ({(a + b) / 2} : Set ℝ) ↔ deriv (y a b) x = 0 := by
  rw [gap3]
  simp only [Set.mem_singleton_iff]
  constructor <;> intro h <;> linarith

end

end ProofGap.Exercise838
