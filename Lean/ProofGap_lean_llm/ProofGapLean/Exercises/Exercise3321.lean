import ProofGapLean.Prelude.Core
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3321

noncomputable section

def z (φ : ℝ → ℝ) (x y : ℝ) : ℝ :=
  φ (x ^ 2 + y ^ 2)

def partialX (g : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun s => g s y) x

def partialY (g : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun s => g x s) y

theorem gap1 (φ : ℝ → ℝ) (hφ : Differentiable ℝ φ) :
    ∀ y x,
      y * partialX (z φ) x y =
        y * 2 * x * deriv φ (x ^ 2 + y ^ 2) := by
  intro y x
  unfold partialX z
  have hsq : HasDerivAt (fun s : ℝ => s * s) (2 * x) x := by
    convert (hasDerivAt_id x).mul (hasDerivAt_id x) using 1 <;>
      simp [id_eq] <;> ring
  have hx : HasDerivAt (fun s : ℝ => s ^ 2 + y ^ 2) (2 * x) x := by
    have hfun :
        (fun s : ℝ => s ^ 2 + y ^ 2) =
          (fun s : ℝ => s * s) + (fun _ : ℝ => y ^ 2) := by
      funext s
      simp [pow_two]
    rw [hfun]
    simpa using hsq.add (hasDerivAt_const x (y ^ 2))
  have hcomp :
      HasDerivAt (fun s : ℝ => φ (s ^ 2 + y ^ 2))
        (deriv φ (x ^ 2 + y ^ 2) * (2 * x)) x := by
    simpa [Function.comp_def] using
      ((hφ (x ^ 2 + y ^ 2)).hasDerivAt.comp x hx)
  rw [hcomp.deriv]
  ring

theorem gap2 (φ : ℝ → ℝ) (hφ : Differentiable ℝ φ) :
    ∀ x y,
      x * partialY (z φ) x y =
        x * 2 * y * deriv φ (x ^ 2 + y ^ 2) := by
  intro x y
  unfold partialY z
  have hsq : HasDerivAt (fun s : ℝ => s * s) (2 * y) y := by
    convert (hasDerivAt_id y).mul (hasDerivAt_id y) using 1 <;>
      simp [id_eq] <;> ring
  have hy : HasDerivAt (fun s : ℝ => x ^ 2 + s ^ 2) (2 * y) y := by
    have hfun :
        (fun s : ℝ => x ^ 2 + s ^ 2) =
          (fun _ : ℝ => x ^ 2) + (fun s : ℝ => s * s) := by
      funext s
      simp [pow_two]
    rw [hfun]
    simpa using (hasDerivAt_const y (x ^ 2)).add hsq
  have hcomp :
      HasDerivAt (fun s : ℝ => φ (x ^ 2 + s ^ 2))
        (deriv φ (x ^ 2 + y ^ 2) * (2 * y)) y := by
    simpa [Function.comp_def] using
      ((hφ (x ^ 2 + y ^ 2)).hasDerivAt.comp y hy)
  rw [hcomp.deriv]
  ring

theorem gap3 (φ : ℝ → ℝ) (hφ : Differentiable ℝ φ) :
    ∀ y x,
      y * partialX (z φ) x y - x * partialY (z φ) x y = 0 := by
  intro y x
  rw [gap1 φ hφ y x, gap2 φ hφ x y]
  ring

theorem gap4 (φ : ℝ → ℝ) (hφ : Differentiable ℝ φ) :
    ∀ y x,
      y * partialX (z φ) x y - x * partialY (z φ) x y = 0 := by
  exact gap3 φ hφ

end

end ProofGap.Exercise3321
