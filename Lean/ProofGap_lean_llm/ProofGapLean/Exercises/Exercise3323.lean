import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3323

noncomputable section

def q (x y : ℝ) : ℝ :=
  y * Real.exp (x ^ 2 / (2 * y ^ 2))

def z (φ : ℝ → ℝ) (x y : ℝ) : ℝ :=
  Real.exp y * φ (q x y)

def partialX (g : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun s => g s y) x

def partialY (g : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun s => g x s) y

theorem gap1 (φ : ℝ → ℝ) (hφ : Differentiable ℝ φ) :
    ∀ x y, y ≠ 0 →
      (x ^ 2 - y ^ 2) * partialX (z φ) x y +
          x * y * partialY (z φ) x y =
        (x ^ 2 - y ^ 2) * Real.exp y *
            (x * deriv φ (q x y) / y ^ 2) *
            y * Real.exp (x ^ 2 / (2 * y ^ 2)) +
          x * y *
            (Real.exp y * φ (q x y) +
              Real.exp y * deriv φ (q x y) *
                (Real.exp (x ^ 2 / (2 * y ^ 2)) -
                  x ^ 2 / y ^ 3 * y *
                    Real.exp (x ^ 2 / (2 * y ^ 2)))) := by
  intro x y hy
  have hsqX : HasDerivAt (fun s : ℝ => s * s) (x + x) x := by
    simpa using (hasDerivAt_id x).mul (hasDerivAt_id x)
  have hinnerX :
      HasDerivAt (fun s : ℝ => s ^ 2 / (2 * y ^ 2)) (x / y ^ 2) x := by
    have hraw := hsqX.div_const (2 * y ^ 2)
    convert hraw using 1
    · funext s
      simp [pow_two]
    · field_simp [hy]
      ring
  have hqX :
      HasDerivAt (fun s : ℝ => q s y)
        (y * (Real.exp (x ^ 2 / (2 * y ^ 2)) * (x / y ^ 2))) x := by
    convert ((hasDerivAt_const x y).mul
      ((Real.hasDerivAt_exp (x ^ 2 / (2 * y ^ 2))).comp x hinnerX)) using 1 <;>
      simp [q, Function.comp_def] <;>
      ring
  have hsqY : HasDerivAt (fun s : ℝ => s * s) (y + y) y := by
    simpa using (hasDerivAt_id y).mul (hasDerivAt_id y)
  have hdenY :
      HasDerivAt (fun s : ℝ => 2 * (s * s)) (2 * (y + y)) y := by
    simpa using (hasDerivAt_const y (2 : ℝ)).mul hsqY
  have hden : (2 : ℝ) * (y * y) ≠ 0 :=
    mul_ne_zero (by norm_num) (mul_ne_zero hy hy)
  have hinnerY :
      HasDerivAt (fun s : ℝ => x ^ 2 / (2 * s ^ 2)) (-x ^ 2 / y ^ 3) y := by
    have hraw := (hasDerivAt_const y (x ^ 2)).div hdenY hden
    convert hraw using 1
    · funext s
      simp [pow_two]
    · field_simp [hy]
      ring
  have hqY :
      HasDerivAt (fun s : ℝ => q x s)
        (Real.exp (x ^ 2 / (2 * y ^ 2)) -
          x ^ 2 / y ^ 3 * y * Real.exp (x ^ 2 / (2 * y ^ 2))) y := by
    convert ((hasDerivAt_id y).mul
      ((Real.hasDerivAt_exp (x ^ 2 / (2 * y ^ 2))).comp y hinnerY)) using 1 <;>
      simp [q, Function.comp_def] <;>
      ring
  have hzX :
      HasDerivAt (fun s : ℝ => z φ s y)
        (Real.exp y *
          (deriv φ (q x y) *
            (y * (Real.exp (x ^ 2 / (2 * y ^ 2)) * (x / y ^ 2))))) x := by
    convert ((hasDerivAt_const x (Real.exp y)).mul
      (((hφ (q x y)).hasDerivAt).comp x hqX)) using 1 <;>
      simp [z, Function.comp_def] <;>
      ring
  have hzY :
      HasDerivAt (fun s : ℝ => z φ x s)
        (Real.exp y * φ (q x y) +
          Real.exp y * deriv φ (q x y) *
            (Real.exp (x ^ 2 / (2 * y ^ 2)) -
              x ^ 2 / y ^ 3 * y *
                Real.exp (x ^ 2 / (2 * y ^ 2)))) y := by
    convert ((Real.hasDerivAt_exp y).mul
      (((hφ (q x y)).hasDerivAt).comp y hqY)) using 1 <;>
      simp [z, Function.comp_def] <;>
      ring
  have hpx :
      partialX (z φ) x y =
        Real.exp y *
          (deriv φ (q x y) *
            (y * (Real.exp (x ^ 2 / (2 * y ^ 2)) * (x / y ^ 2)))) := by
    simpa [partialX] using hzX.deriv
  have hpy :
      partialY (z φ) x y =
        Real.exp y * φ (q x y) +
          Real.exp y * deriv φ (q x y) *
            (Real.exp (x ^ 2 / (2 * y ^ 2)) -
              x ^ 2 / y ^ 3 * y *
                Real.exp (x ^ 2 / (2 * y ^ 2))) := by
    simpa [partialY] using hzY.deriv
  rw [hpx, hpy]
  ring

theorem gap2 (φ : ℝ → ℝ) :
    ∀ x y, y ≠ 0 →
      (x ^ 2 - y ^ 2) * Real.exp y *
            (x * deriv φ (q x y) / y ^ 2) *
            y * Real.exp (x ^ 2 / (2 * y ^ 2)) +
          x * y *
            (Real.exp y * φ (q x y) +
              Real.exp y * deriv φ (q x y) *
                (Real.exp (x ^ 2 / (2 * y ^ 2)) -
                  x ^ 2 / y ^ 3 * y *
                    Real.exp (x ^ 2 / (2 * y ^ 2)))) =
        x * y * Real.exp y * φ (q x y) := by
  intro x y hy
  field_simp [hy] <;> ring

theorem gap3 (φ : ℝ → ℝ) :
    ∀ x y, y ≠ 0 →
      x * y * Real.exp y * φ (q x y) = x * y * z φ x y := by
  intro x y hy
  simp [z, mul_assoc]

theorem gap4 (φ : ℝ → ℝ) (hφ : Differentiable ℝ φ) :
    ∀ x y, y ≠ 0 →
      (x ^ 2 - y ^ 2) * partialX (z φ) x y +
        x * y * partialY (z φ) x y = x * y * z φ x y := by
  intro x y hy
  exact (gap1 φ hφ x y hy).trans
    ((gap2 φ x y hy).trans (gap3 φ x y hy))

theorem gap5 (φ : ℝ → ℝ) (hφ : Differentiable ℝ φ) :
    ∀ x y, y ≠ 0 →
      (x ^ 2 - y ^ 2) * partialX (z φ) x y +
        x * y * partialY (z φ) x y = x * y * z φ x y := by
  intro x y hy
  exact gap4 φ hφ x y hy

end

end ProofGap.Exercise3323
