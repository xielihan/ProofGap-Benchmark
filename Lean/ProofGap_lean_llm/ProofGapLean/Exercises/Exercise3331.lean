import ProofGapLean.Prelude.Core
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Comp

namespace ProofGap.Exercise3331

noncomputable section

def z (φ : ℝ → ℝ) (x y : ℝ) : ℝ :=
  x + φ (x * y)

def partialX (g : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun s => g s y) x

def partialY (g : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun s => g x s) y

theorem gap1 (φ : ℝ → ℝ) (hφ : Differentiable ℝ φ) :
    ∀ x y, partialX (z φ) x y = 1 + y * deriv φ (x * y) := by
  intro x y
  have hinner : HasDerivAt (fun s : ℝ => s * y) y x := by
    simpa using (hasDerivAt_id x).mul (hasDerivAt_const x y)
  have houter : HasDerivAt φ (deriv φ (x * y)) (x * y) :=
    (hφ (x * y)).hasDerivAt
  have hcomp :
      HasDerivAt (fun s : ℝ => φ (s * y)) (y * deriv φ (x * y)) x := by
    simpa [Function.comp_def, mul_comm] using houter.scomp x hinner
  have hsum :
      HasDerivAt (fun s : ℝ => s + φ (s * y))
        (1 + y * deriv φ (x * y)) x :=
    (hasDerivAt_id x).add hcomp
  simpa [partialX, z] using hsum.deriv

theorem gap2 (φ : ℝ → ℝ) (hφ : Differentiable ℝ φ) :
    ∀ x y, partialY (z φ) x y = x * deriv φ (x * y) := by
  intro x y
  have hinner : HasDerivAt (fun s : ℝ => x * s) x y := by
    simpa using (hasDerivAt_const y x).mul (hasDerivAt_id y)
  have houter : HasDerivAt φ (deriv φ (x * y)) (x * y) :=
    (hφ (x * y)).hasDerivAt
  have hcomp :
      HasDerivAt (fun s : ℝ => φ (x * s)) (x * deriv φ (x * y)) y := by
    simpa [Function.comp_def, mul_comm] using houter.scomp y hinner
  have hsum :
      HasDerivAt (fun s : ℝ => x + φ (x * s))
        (0 + x * deriv φ (x * y)) y :=
    (hasDerivAt_const y x).add hcomp
  change deriv (fun s : ℝ => x + φ (x * s)) y =
    x * deriv φ (x * y)
  simpa only [zero_add] using hsum.deriv

theorem gap3 (φ : ℝ → ℝ) (hφ : Differentiable ℝ φ) :
    ∀ x y, x * partialX (z φ) x y - y * partialY (z φ) x y = x := by
  intro x y
  rw [gap1 φ hφ x y, gap2 φ hφ x y]
  ring

theorem gap4 (φ : ℝ → ℝ) (hφ : Differentiable ℝ φ) :
    ∀ x y, x * partialX (z φ) x y - y * partialY (z φ) x y = x := by
  exact gap3 φ hφ

end

end ProofGap.Exercise3331
