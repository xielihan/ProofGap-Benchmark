import ProofGapLean.Prelude.Sequences
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Ext

open Filter

namespace ProofGap.Exercise127_1

/-- Exercise 127_1, gap 1. -/
theorem gap1
    (x y : ℕ → ℝ) :
    ∀ n : ℕ, y n = (x n + y n) - x n := by
  intro n
  ring

/-- Exercise 127_1, gap 2. -/
theorem gap2
    (x y : ℕ → ℝ)
    (hx : ProofGap.ConvergentSeq x)
    (hsum : ProofGap.ConvergentSeq (fun n => x n + y n)) :
    ProofGap.ConvergentSeq y := by
  rcases hx with ⟨a, ha⟩
  rcases hsum with ⟨b, hb⟩
  refine ⟨b - a, ?_⟩
  have hdiff := hb.sub ha
  convert hdiff using 1
  ext n
  ring

/-- Exercise 127_1, gap 3. -/
theorem gap3
    (x y : ℕ → ℝ)
    (hx : ProofGap.ConvergentSeq x)
    (hy : ¬ ProofGap.ConvergentSeq y)
    (hsum : ProofGap.ConvergentSeq (fun n => x n + y n)) :
    False := by
  exact hy (gap2 x y hx hsum)

/-- Exercise 127_1, gap 4. -/
theorem gap4
    (x y : ℕ → ℝ)
    (hx : ProofGap.ConvergentSeq x)
    (hy : ¬ ProofGap.ConvergentSeq y) :
    ¬ ProofGap.ConvergentSeq (fun n => x n + y n) := by
  intro hsum
  exact gap3 x y hx hy hsum

/-- Exercise 127_1, gap 5. -/
theorem gap5
    (x y : ℕ → ℝ)
    (h : ¬ ProofGap.ConvergentSeq (fun n => x n + y n)) :
    ¬ ProofGap.ConvergentSeq (fun n => x n + y n) := by
  exact h

end ProofGap.Exercise127_1
