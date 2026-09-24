import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Lean.Elab.Tactic.Omega

namespace ProofGap.Exercise1593_1

noncomputable section

def y (x : ℝ) := 1 - Real.cos x
def axis (_x : ℝ) : ℝ := 0
def iterDeriv : ℕ → (ℝ → ℝ) → ℝ → ℝ
  | 0, f => f
  | n + 1, f => deriv (iterDeriv n f)
def ContactOrder (f g : ℝ → ℝ) (x₀ : ℝ) (m : ℕ) : Prop :=
  (∀ k ≤ m, iterDeriv k f x₀ = iterDeriv k g x₀) ∧
    iterDeriv (m + 1) f x₀ ≠ iterDeriv (m + 1) g x₀

theorem gap1 (x : ℝ) : deriv y x = Real.sin x := by
  have h : HasDerivAt y (Real.sin x) x := by
    simpa only [y, zero_sub, neg_neg] using
      ((Real.hasDerivAt_cos x).const_sub 1)
  exact h.deriv
theorem gap2 (x : ℝ) : deriv (deriv y) x = Real.cos x := by
  have hy : deriv y = Real.sin := funext gap1
  rw [hy]
  exact (Real.hasDerivAt_sin x).deriv
theorem gap3 : deriv y 0 = 0 := by
  rw [gap1, Real.sin_zero]
theorem gap4 : deriv (deriv y) 0 = 1 := by
  rw [gap2, Real.cos_zero]
theorem gap5 (x : ℝ) : axis x = 0 := by
  rfl
theorem gap6 (x : ℝ) : deriv axis x = 0 := by
  unfold axis
  exact (hasDerivAt_const (x : ℝ) (0 : ℝ)).deriv
theorem gap7 (x : ℝ) : deriv (deriv axis) x = 0 := by
  have haxis : deriv axis = axis := by
    funext z
    rw [gap6, gap5]
  rw [haxis]
  exact gap6 x
theorem gap8 : ContactOrder y axis 0 1 := by
  constructor
  · intro k hk
    have hk' : k = 0 ∨ k = 1 := by omega
    rcases hk' with rfl | rfl
    · simp [iterDeriv, y, axis]
    · change deriv y 0 = deriv axis 0
      rw [gap3, gap6]
  · change deriv (deriv y) 0 ≠ deriv (deriv axis) 0
    rw [gap4, gap7]
    exact one_ne_zero

end
end ProofGap.Exercise1593_1
