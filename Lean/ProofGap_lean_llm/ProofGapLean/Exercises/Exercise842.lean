import ProofGapLean.Prelude.Core
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise842

def y (x : ℝ) : ℝ :=
  (1 - x) * (1 - x ^ 2) ^ 2 * (1 - x ^ 3) ^ 3

def expandedDerivative (x : ℝ) : ℝ :=
  -(1 - x ^ 2) ^ 2 * (1 - x ^ 3) ^ 3 -
    4 * x * (1 - x) * (1 - x ^ 2) * (1 - x ^ 3) ^ 3 -
    9 * x ^ 2 * (1 - x) * (1 - x ^ 2) ^ 2 * (1 - x ^ 3) ^ 2

def partiallyFactoredDerivative (x : ℝ) : ℝ :=
  -(1 - x) ^ 2 * (1 - x ^ 2) * (1 - x ^ 3) ^ 2 *
    (1 + 6 * x + 15 * x ^ 2 + 14 * x ^ 3)

def factoredDerivative (x : ℝ) : ℝ :=
  -(1 - x) ^ 5 * (1 + x) * (1 + 2 * x) *
    (1 + 4 * x + 7 * x ^ 2) * (1 + x + x ^ 2) ^ 2

/-- Source: `proof_gap/exercise_842/1.txt`; replace the malformed critical-point
biconditional by the derivative identity supplied by the product rule. -/
theorem gap1 (x : ℝ) : deriv y x = expandedDerivative x := by
  have hx2 :=
    (hasDerivAt_id x).mul (hasDerivAt_id x)
  have hx3 :=
    hx2.mul (hasDerivAt_id x)
  have h1 :=
    (hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)
  have h2 :=
    (hasDerivAt_const x (1 : ℝ)).sub hx2
  have h3 :=
    (hasDerivAt_const x (1 : ℝ)).sub hx3
  have h2sq := h2.mul h2
  have h3sq := h3.mul h3
  have h3cube := h3sq.mul h3
  have hy := (h1.mul h2sq).mul h3cube
  have hfun :
      ((((fun _ : ℝ => (1 : ℝ)) - id) *
          (((fun _ : ℝ => (1 : ℝ)) - id * id) *
            ((fun _ : ℝ => (1 : ℝ)) - id * id))) *
        ((((fun _ : ℝ => (1 : ℝ)) - id * id * id) *
            ((fun _ : ℝ => (1 : ℝ)) - id * id * id)) *
          ((fun _ : ℝ => (1 : ℝ)) - id * id * id))) = y := by
    funext t
    change
      (1 - t) * ((1 - t * t) * (1 - t * t)) *
          (((1 - (t * t) * t) * (1 - (t * t) * t)) *
            (1 - (t * t) * t)) =
        (1 - t) * (1 - t ^ 2) ^ 2 * (1 - t ^ 3) ^ 3
    ring
  rw [hfun] at hy
  calc
    deriv y x = _ := hy.deriv
    _ = expandedDerivative x := by
      unfold expandedDerivative
      simp only [Pi.mul_apply, Pi.sub_apply, id_eq]
      ring

/-- Source: `proof_gap/exercise_842/2.txt`; isolate the intended algebraic
factorization step. -/
theorem gap2 (x : ℝ) :
    expandedDerivative x = partiallyFactoredDerivative x := by
  unfold expandedDerivative partiallyFactoredDerivative
  ring

/-- Source: `proof_gap/exercise_842/3.txt`; isolate the final factorization
step. -/
theorem gap3 (x : ℝ) :
    partiallyFactoredDerivative x = factoredDerivative x := by
  unfold partiallyFactoredDerivative factoredDerivative
  ring

theorem gap4 (x : ℝ) :
    deriv y x = 0 ↔
      x = 1 ∨ x = -1 ∨ x = -(1 / 2) ∨
        1 + 4 * x + 7 * x ^ 2 = 0 ∨ 1 + x + x ^ 2 = 0 := by
  rw [gap1, gap2, gap3]
  unfold factoredDerivative
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h | hR
    · rcases mul_eq_zero.mp h with h | hQ
      · rcases mul_eq_zero.mp h with h | hC
        · rcases mul_eq_zero.mp h with hA | hB
          · have hA0 : (1 - x) ^ 5 = 0 := by
              linarith
            have hA' : 1 - x = 0 :=
              eq_zero_of_pow_eq_zero hA0
            left
            linarith
          · right
            left
            linarith
        · right
          right
          left
          linarith
      · right
        right
        right
        left
        exact hQ
    · have hR' : 1 + x + x ^ 2 = 0 :=
        eq_zero_of_pow_eq_zero hR
      right
      right
      right
      right
      exact hR'
  · rintro (hx | hx | hx | hQ | hR)
    · subst x
      ring
    · subst x
      ring
    · subst x
      ring
    · simp [hQ]
    · simp [hR]

/-- Source: `proof_gap/exercise_842/5.txt`; the intended step is that the
first residual quadratic has no real root. -/
theorem gap5 : ¬∃ z : ℝ, 1 + 4 * z + 7 * z ^ 2 = 0 := by
  rintro ⟨z, hz⟩
  nlinarith [sq_nonneg (7 * z + 2)]

/-- Source: `proof_gap/exercise_842/6.txt`; the intended step is that the
second residual quadratic has no real root. -/
theorem gap6 : ¬∃ z : ℝ, 1 + z + z ^ 2 = 0 := by
  rintro ⟨z, hz⟩
  nlinarith [sq_nonneg (2 * z + 1)]

theorem gap7 (x : ℝ) :
    x ∈ ({(1 : ℝ), -1, -(1 / 2)} : Set ℝ) ↔ deriv y x = 0 := by
  have h5 : 1 + 4 * x + 7 * x ^ 2 ≠ 0 := by
    intro h
    exact gap5 ⟨x, h⟩
  have h6 : 1 + x + x ^ 2 ≠ 0 := by
    intro h
    exact gap6 ⟨x, h⟩
  rw [gap4]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, h5, h6, or_false]

end ProofGap.Exercise842
