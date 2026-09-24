import ProofGapLean.Prelude.Elementary
import Mathlib.Tactic.FieldSimp

namespace ProofGap.Exercise195_3

noncomputable section

def f (a x : ℝ) : ℝ := Real.rpow a x
def φ (a h x : ℝ) : ℝ := (f a (x + h) - f a x) / h

/-- Exercise 195_3, gap 1; require a>0 and h≠0. -/
theorem gap1 (a h : ℝ) (ha : 0 < a) (hh : h ≠ 0) :
    ∀ x, φ a h x = (Real.rpow a (x + h) - Real.rpow a x) / h := by
  intro x
  rfl

/-- Exercise 195_3, gap 2. -/
theorem gap2 (a h : ℝ) (ha : 0 < a) (hh : h ≠ 0) :
    ∀ x, (Real.rpow a (x + h) - Real.rpow a x) / h =
      Real.rpow a x * ((Real.rpow a h - 1) / h) := by
  intro x
  have hr :
      Real.rpow a (x + h) = Real.rpow a x * Real.rpow a h :=
    Real.rpow_add ha x h
  rw [hr]
  field_simp

/-- Exercise 195_3, gap 3. -/
theorem gap3 (a h : ℝ) (ha : 0 < a) (hh : h ≠ 0) :
    ∀ x, φ a h x = Real.rpow a x * ((Real.rpow a h - 1) / h) := by
  intro x
  exact gap2 a h ha hh x

end

end ProofGap.Exercise195_3
