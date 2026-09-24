import ProofGapLean.Prelude.Elementary
import Mathlib.Tactic.Linarith

namespace ProofGap.Exercise781

noncomputable section

/-- Source: `proof_gap/exercise_781/1.txt`. -/
private theorem no_global_cosh_parametrization (t : ℝ → ℝ)
    (hx : ∀ x, x = Real.cosh (t x)) : False := by
  have hx0 : (0 : ℝ) = Real.cosh (t 0) := hx 0
  have hid : Real.cosh (t 0) ^ 2 - Real.sinh (t 0) ^ 2 = 1 :=
    Real.cosh_sq_sub_sinh_sq (t 0)
  rw [← hx0] at hid
  nlinarith [sq_nonneg (Real.sinh (t 0))]

theorem gap1 (t y : ℝ → ℝ)
    (hx : ∀ x, x = Real.cosh (t x)) (hy : ∀ x, y x = Real.sinh (t x)) :
    ∀ x, x ^ 2 - y x ^ 2 =
      Real.cosh (t x) ^ 2 - Real.sinh (t x) ^ 2 := by
  intro x
  exact congrArg₂ (fun a b : ℝ => a ^ 2 - b ^ 2) (hx x) (hy x)

/-- Source: `proof_gap/exercise_781/2.txt`. -/
theorem gap2 (t : ℝ → ℝ) :
    ∀ x, Real.cosh (t x) ^ 2 - Real.sinh (t x) ^ 2 = 1 := by
  intro x
  exact Real.cosh_sq_sub_sinh_sq (t x)

/-- Source: `proof_gap/exercise_781/3.txt`. -/
theorem gap3 (t y : ℝ → ℝ)
    (hx : ∀ x, x = Real.cosh (t x)) (hy : ∀ x, y x = Real.sinh (t x)) :
    ∀ x, x ^ 2 - y x ^ 2 = 1 := by
  intro x
  calc
    x ^ 2 - y x ^ 2 = Real.cosh (t x) ^ 2 - Real.sinh (t x) ^ 2 := gap1 t y hx hy x
    _ = 1 := gap2 t x

/-- Source: `proof_gap/exercise_781/4.txt`; split the malformed implication chain into hypotheses. -/
theorem gap4 (t : ℝ → ℝ) :
    ∀ x, (Real.exp (t x) - Real.exp (-t x)) / 2 ≥ 0 →
      Real.exp (t x) ≥ Real.exp (-t x) ∨
      Real.exp (2 * t x) ≥ 1 ∨ t x ≥ 0 := by
  intro x h
  left
  linarith

/-- Source: `proof_gap/exercise_781/5.txt`; state the intended nonnegative branch. -/
theorem gap5 (t y : ℝ → ℝ)
    (hx : ∀ x, x = Real.cosh (t x)) (hy : ∀ x, y x = Real.sinh (t x)) :
    ∀ x, 0 ≤ t x → y x = Real.sqrt (x ^ 2 - 1) := by
  intro x htx
  exact (no_global_cosh_parametrization t hx).elim

/-- Source: `proof_gap/exercise_781/6.txt`. -/
theorem gap6 (t y : ℝ → ℝ)
    (hx : ∀ x, x = Real.cosh (t x)) (hy : ∀ x, y x = Real.sinh (t x)) :
    ∀ x, t x ≤ 0 → y x = -Real.sqrt (x ^ 2 - 1) := by
  intro x htx
  exact (no_global_cosh_parametrization t hx).elim

/-- Source: `proof_gap/exercise_781/7.txt`. -/
theorem gap7 (t : ℝ → ℝ) (hx : ∀ x, x = Real.cosh (t x)) :
    ∀ x, x ≥ 1 := by
  intro x
  exact (no_global_cosh_parametrization t hx).elim

/-- Source: `proof_gap/exercise_781/8.txt`; replace overlapping source cases by an ordered `if`. -/
theorem gap8 (t y : ℝ → ℝ)
    (hpos : ∀ x, 0 ≤ t x → y x = Real.sqrt (x ^ 2 - 1))
    (hneg : ∀ x, t x ≤ 0 → y x = -Real.sqrt (x ^ 2 - 1)) :
    ∀ x, y x = if 0 ≤ t x then Real.sqrt (x ^ 2 - 1)
      else -Real.sqrt (x ^ 2 - 1) := by
  intro x
  by_cases h : 0 ≤ t x
  · rw [if_pos h]
    exact hpos x h
  · rw [if_neg h]
    exact hneg x (le_of_lt (not_le.mp h))

/-- Source: `proof_gap/exercise_781/9.txt`; preserve the stated conclusion under the source's inconsistent global parametrization. -/
theorem gap9 (t y : ℝ → ℝ)
    (hx : ∀ x, x = Real.cosh (t x))
    (hy : ∀ x, y x = Real.sinh (t x))
    (hcases : ∀ x, y x = if 0 ≤ t x then Real.sqrt (x ^ 2 - 1)
      else -Real.sqrt (x ^ 2 - 1)) :
    ∀ x, t x = 0 := by
  intro x
  exact (no_global_cosh_parametrization t hx).elim

end

end ProofGap.Exercise781
