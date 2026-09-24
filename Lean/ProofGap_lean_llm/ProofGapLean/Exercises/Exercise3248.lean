import ProofGapLean.Prelude.Core
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3248

noncomputable section

def u (x y : ℝ) : ℝ := x * y

def partialX (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => f t y) x

def partialY (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => f x t) y

def differential (f : ℝ → ℝ → ℝ) (x y dx dy : ℝ) : ℝ :=
  partialX f x y * dx + partialY f x y * dy

theorem gap1 (x y dx dy : ℝ) :
    differential u x y dx dy = x * dy + y * dx := by
  have hdx : deriv (fun t : ℝ => u t y) x = y := by
    simpa [u] using ((hasDerivAt_id x).mul_const y).deriv
  have hdy : deriv (fun t : ℝ => u x t) y = x := by
    simpa [u] using ((hasDerivAt_id y).const_mul x).deriv
  simp [differential, partialX, partialY, hdx, hdy, add_comm]

theorem gap2 (x y dx dy : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) :
    differential u x y dx dy / u x y = dx / x + dy / y := by
  rw [gap1]
  simp only [u]
  field_simp [hx, hy]
  ring

theorem gap3 (x y dx dy : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) :
    |differential u x y dx dy / u x y| ≤
      |dx / x| + |dy / y| := by
  rw [gap2 x y dx dy hx hy]
  exact abs_add_le _ _

theorem gap4 :
    ∀ (v : ℝ → ℝ → ℝ) (x y dx dy : ℝ),
      (∀ a b, v a b = a * b) →
      x ≠ 0 → y ≠ 0 →
      |differential v x y dx dy / v x y| ≤
        |dx / x| + |dy / y| := by
  intro v x y dx dy hv hx hy
  have hvu : v = u := by
    funext a b
    simpa [u] using hv a b
  subst v
  exact gap3 x y dx dy hx hy

end

end ProofGap.Exercise3248
