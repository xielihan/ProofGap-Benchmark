import ProofGapLean.Prelude.Core
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3322

noncomputable section

def z (φ : ℝ → ℝ) (x y : ℝ) : ℝ :=
  y ^ 2 / (3 * x) + φ (x * y)

def partialX (g : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun s => g s y) x

def partialY (g : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun s => g x s) y

theorem gap1 (φ : ℝ → ℝ) (hφ : Differentiable ℝ φ) :
    ∀ x y, x ≠ 0 →
      x ^ 2 * partialX (z φ) x y - x * y * partialY (z φ) x y + y ^ 2 =
        x ^ 2 * (-y ^ 2 / (3 * x ^ 2) + y * deriv φ (x * y)) -
          x * y * (2 * y / (3 * x) + x * deriv φ (x * y)) + y ^ 2 := by
  intro x y hx
  have hx3 : (3 : ℝ) * x ≠ 0 := mul_ne_zero (by norm_num) hx
  have hden : HasDerivAt (fun s : ℝ => 3 * s) 3 x := by
    simpa using
      (hasDerivAt_const x (3 : ℝ)).mul (hasDerivAt_id x)
  have hratX :
      HasDerivAt (fun s : ℝ => y ^ 2 / (3 * s))
        (-y ^ 2 / (3 * x ^ 2)) x := by
    convert (hasDerivAt_const x (y ^ 2)).div hden hx3 using 1 <;>
      field_simp [hx] <;> ring
  have hcompX :
      HasDerivAt (fun s : ℝ => φ (s * y))
        (y * deriv φ (x * y)) x := by
    simpa [mul_comm] using
      (hφ (x * y)).hasDerivAt.comp x
        ((hasDerivAt_id x).mul_const y)
  have hratY :
      HasDerivAt (fun s : ℝ => s ^ 2 / (3 * x))
        (2 * y / (3 * x)) y := by
    simpa [pow_two] using
      ((hasDerivAt_id y).pow 2).div_const (3 * x)
  have hcompY :
      HasDerivAt (fun s : ℝ => φ (x * s))
        (x * deriv φ (x * y)) y := by
    simpa [mul_comm] using
      (hφ (x * y)).hasDerivAt.comp y
        ((hasDerivAt_const y x).mul (hasDerivAt_id y))
  have hpartialX :
      partialX (z φ) x y =
        -y ^ 2 / (3 * x ^ 2) + y * deriv φ (x * y) := by
    simpa [partialX, z] using (hratX.add hcompX).deriv
  have hpartialY :
      partialY (z φ) x y =
        2 * y / (3 * x) + x * deriv φ (x * y) := by
    simpa [partialY, z] using (hratY.add hcompY).deriv
  rw [hpartialX, hpartialY]

theorem gap2 (φ : ℝ → ℝ) :
    ∀ x y, x ≠ 0 →
      x ^ 2 * (-y ^ 2 / (3 * x ^ 2) + y * deriv φ (x * y)) -
          x * y * (2 * y / (3 * x) + x * deriv φ (x * y)) + y ^ 2 =
        0 := by
  intro x y hx
  field_simp [hx]
  ring

theorem gap3 (φ : ℝ → ℝ) (hφ : Differentiable ℝ φ) :
    ∀ x y, x ≠ 0 →
      x ^ 2 * partialX (z φ) x y - x * y * partialY (z φ) x y + y ^ 2 =
        0 := by
  intro x y hx
  exact (gap1 φ hφ x y hx).trans (gap2 φ x y hx)

theorem gap4 (φ : ℝ → ℝ) (hφ : Differentiable ℝ φ) :
    ∀ x y, x ≠ 0 →
      x ^ 2 * partialX (z φ) x y - x * y * partialY (z φ) x y + y ^ 2 =
        0 := by
  exact gap3 φ hφ

end

end ProofGap.Exercise3322
