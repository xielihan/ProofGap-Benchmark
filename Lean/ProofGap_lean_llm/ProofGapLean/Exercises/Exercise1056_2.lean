import ProofGapLean.Prelude.Core
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Linarith

namespace ProofGap.Exercise1056_2

def y (x : ℝ) : ℝ := 2 + x - x ^ 2

theorem gap1 (x : ℝ) :
    deriv y x = 1 - 2 * x := by
  have hraw :=
    (((hasDerivAt_const x (2 : ℝ)).add (hasDerivAt_id x)).sub
      ((hasDerivAt_id x).mul (hasDerivAt_id x)))
  have hfun :
      ((fun _ : ℝ => (2 : ℝ)) + id - id * id) = y := by
    funext z
    simp [y, pow_two]
  rw [hfun] at hraw
  simpa [two_mul] using hraw.deriv

theorem gap2 (x : ℝ) :
    deriv y x = 1 ↔ x = 0 := by
  rw [gap1]
  constructor
  · intro h
    linarith
  · intro h
    linarith

theorem gap3 (x : ℝ) :
    x ∈ ({0} : Set ℝ) ↔ deriv y x = 1 := by
  simpa only [Set.mem_singleton_iff] using (gap2 x).symm

theorem gap4 (x : ℝ) (hx : x = 0) :
    y x = 2 := by
  subst x
  simp [y]

theorem gap5 (x : ℝ)
    (hx : (x, y x) ∈ ({((0 : ℝ), (2 : ℝ))} : Set (ℝ × ℝ))) :
    y x = 2 + x - x ^ 2 ∧ deriv y x = 1 := by
  have hpair : (x, y x) = ((0 : ℝ), (2 : ℝ)) :=
    Set.mem_singleton_iff.mp hx
  have hx0 : x = 0 := by
    simpa using congrArg Prod.fst hpair
  constructor
  · rfl
  · exact (gap2 x).2 hx0

end ProofGap.Exercise1056_2
