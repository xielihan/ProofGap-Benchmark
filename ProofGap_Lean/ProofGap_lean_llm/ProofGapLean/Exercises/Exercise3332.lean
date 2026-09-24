import ProofGapLean.Prelude.Core
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3332

noncomputable section

def z (φ : ℝ → ℝ) (x y : ℝ) : ℝ :=
  x * φ (x / y ^ 2)

def partialX (g : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun s => g s y) x

def partialY (g : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun s => g x s) y

theorem gap1 (φ : ℝ → ℝ) (hφ : Differentiable ℝ φ) :
    ∀ x y, y ≠ 0 →
      partialX (z φ) x y =
        φ (x / y ^ 2) + x / y ^ 2 * deriv φ (x / y ^ 2) := by
  intro x y hy
  unfold partialX z
  have hinner : HasDerivAt (fun s : ℝ => s / y ^ 2) (1 / y ^ 2) x := by
    simpa [div_eq_mul_inv] using
      (hasDerivAt_id x).mul_const ((y ^ 2)⁻¹)
  have hout : HasDerivAt (fun s : ℝ => φ (s / y ^ 2))
      (deriv φ (x / y ^ 2) * (1 / y ^ 2)) x :=
    (hφ (x / y ^ 2)).hasDerivAt.comp x hinner
  have hprod : HasDerivAt (fun s : ℝ => s * φ (s / y ^ 2))
      (1 * φ (x / y ^ 2) +
        x * (deriv φ (x / y ^ 2) * (1 / y ^ 2))) x :=
    (hasDerivAt_id x).mul hout
  convert hprod.deriv using 1 <;> field_simp [hy] <;> ring

theorem gap2 (φ : ℝ → ℝ) (hφ : Differentiable ℝ φ) :
    ∀ x y, y ≠ 0 →
      partialY (z φ) x y =
        -(2 * x ^ 2 / y ^ 3) * deriv φ (x / y ^ 2) := by
  intro x y hy
  unfold partialY z
  have hden : HasDerivAt (fun s : ℝ => s ^ 2) (2 * y) y := by
    simpa [pow_two, two_mul] using
      (hasDerivAt_id y).mul (hasDerivAt_id y)
  have hinner : HasDerivAt (fun s : ℝ => x / s ^ 2)
      (-2 * x / y ^ 3) y := by
    convert (hasDerivAt_const y x).div hden (pow_ne_zero 2 hy) using 1 <;>
      field_simp [hy] <;> ring
  have hout : HasDerivAt (fun s : ℝ => φ (x / s ^ 2))
      (deriv φ (x / y ^ 2) * (-2 * x / y ^ 3)) y :=
    (hφ (x / y ^ 2)).hasDerivAt.comp y hinner
  have hfinal : HasDerivAt (fun s : ℝ => x * φ (x / s ^ 2))
      (x * (deriv φ (x / y ^ 2) * (-2 * x / y ^ 3))) y :=
    hout.const_mul x
  convert hfinal.deriv using 1 <;> field_simp [hy] <;> ring

theorem gap3 (φ : ℝ → ℝ) (hφ : Differentiable ℝ φ) :
    ∀ x y, y ≠ 0 →
      2 * x * partialX (z φ) x y + y * partialY (z φ) x y =
        2 * x * φ (x / y ^ 2) +
          2 * x ^ 2 / y ^ 2 * deriv φ (x / y ^ 2) -
          2 * x ^ 2 / y ^ 2 * deriv φ (x / y ^ 2) := by
  intro x y hy
  rw [gap1 φ hφ x y hy, gap2 φ hφ x y hy]
  field_simp [hy]
  ring

theorem gap4 (φ : ℝ → ℝ) :
    ∀ x y, y ≠ 0 →
      2 * x * φ (x / y ^ 2) +
          2 * x ^ 2 / y ^ 2 * deriv φ (x / y ^ 2) -
          2 * x ^ 2 / y ^ 2 * deriv φ (x / y ^ 2) =
        2 * x * φ (x / y ^ 2) := by
  intro x y hy
  ring

theorem gap5 (φ : ℝ → ℝ) :
    ∀ x y, y ≠ 0 → 2 * x * φ (x / y ^ 2) = 2 * z φ x y := by
  intro x y hy
  unfold z
  ring

theorem gap6 (φ : ℝ → ℝ) (hφ : Differentiable ℝ φ) :
    ∀ x y, y ≠ 0 →
      2 * x * partialX (z φ) x y + y * partialY (z φ) x y =
        2 * z φ x y := by
  intro x y hy
  calc
    2 * x * partialX (z φ) x y + y * partialY (z φ) x y =
        2 * x * φ (x / y ^ 2) +
          2 * x ^ 2 / y ^ 2 * deriv φ (x / y ^ 2) -
          2 * x ^ 2 / y ^ 2 * deriv φ (x / y ^ 2) :=
      gap3 φ hφ x y hy
    _ = 2 * x * φ (x / y ^ 2) := gap4 φ x y hy
    _ = 2 * z φ x y := gap5 φ x y hy

theorem gap7 (φ : ℝ → ℝ) (hφ : Differentiable ℝ φ) :
    ∀ x y, y ≠ 0 →
      2 * x * partialX (z φ) x y + y * partialY (z φ) x y =
        2 * z φ x y := by
  exact gap6 φ hφ

end

end ProofGap.Exercise3332
