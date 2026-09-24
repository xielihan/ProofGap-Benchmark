import ProofGapLean.Prelude.Core
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3318

noncomputable section

def z (f : ℝ → ℝ) (x y : ℝ) : ℝ :=
  y * f (x ^ 2 - y ^ 2)

def partialX (g : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun s => g s y) x

def partialY (g : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun s => g x s) y

theorem gap1 (f : ℝ → ℝ) (hf : Differentiable ℝ f) :
    ∀ y x,
      y ^ 2 * partialX (z f) x y + x * y * partialY (z f) x y =
        y ^ 2 * (2 * x * y * deriv f (x ^ 2 - y ^ 2)) +
          x * y * (f (x ^ 2 - y ^ 2) -
            2 * y ^ 2 * deriv f (x ^ 2 - y ^ 2)) := by
  intro y x
  have hf' :
      HasDerivAt f (deriv f (x ^ 2 - y ^ 2)) (x ^ 2 - y ^ 2) :=
    (hf (x ^ 2 - y ^ 2)).hasDerivAt
  have hxinner :
      HasDerivAt (fun s : ℝ => s ^ 2 - y ^ 2) (2 * x) x := by
    simpa [pow_two, two_mul] using
      (((hasDerivAt_id x).mul (hasDerivAt_id x)).sub_const (y ^ 2))
  have hyinner :
      HasDerivAt (fun s : ℝ => x ^ 2 - s ^ 2) (-2 * y) y := by
    have hfun :
        (fun s : ℝ => x ^ 2 - s ^ 2) =
          (fun s : ℝ => x ^ 2 - s * s) := by
      funext s
      simp only [pow_two]
    rw [hfun]
    convert
      (((hasDerivAt_id y).mul (hasDerivAt_id y)).const_sub (x ^ 2))
      using 1 <;> simp <;> ring_nf
  have hfxcomp :
      HasDerivAt (fun s : ℝ => f (s ^ 2 - y ^ 2))
        (deriv f (x ^ 2 - y ^ 2) * (2 * x)) x := by
    simpa [Function.comp_def] using hf'.comp x hxinner
  have hfycomp :
      HasDerivAt (fun s : ℝ => f (x ^ 2 - s ^ 2))
        (deriv f (x ^ 2 - y ^ 2) * (-2 * y)) y := by
    simpa [Function.comp_def] using hf'.comp y hyinner
  have hxz :
      HasDerivAt (fun s : ℝ => z f s y)
        (y * (deriv f (x ^ 2 - y ^ 2) * (2 * x))) x := by
    simpa [z] using (hasDerivAt_const x y).mul hfxcomp
  have hyz :
      HasDerivAt (fun s : ℝ => z f x s)
        (f (x ^ 2 - y ^ 2) +
          y * (deriv f (x ^ 2 - y ^ 2) * (-2 * y))) y := by
    simpa [z] using (hasDerivAt_id y).mul hfycomp
  change
    y ^ 2 * deriv (fun s : ℝ => z f s y) x +
        x * y * deriv (fun s : ℝ => z f x s) y = _
  rw [hxz.deriv, hyz.deriv]
  ring

theorem gap2 (f : ℝ → ℝ) :
    ∀ y x,
      y ^ 2 * (2 * x * y * deriv f (x ^ 2 - y ^ 2)) +
          x * y * (f (x ^ 2 - y ^ 2) -
            2 * y ^ 2 * deriv f (x ^ 2 - y ^ 2)) =
        x * y * f (x ^ 2 - y ^ 2) := by
  intro y x
  ring

theorem gap3 (f : ℝ → ℝ) :
    ∀ x y, x * y * f (x ^ 2 - y ^ 2) = x * z f x y := by
  intro x y
  unfold z
  ring

theorem gap4 (f : ℝ → ℝ) (hf : Differentiable ℝ f) :
    ∀ y x,
      y ^ 2 * partialX (z f) x y + x * y * partialY (z f) x y =
        x * z f x y := by
  intro y x
  rw [gap1 f hf y x, gap2 f y x, gap3 f x y]

theorem gap5 (f : ℝ → ℝ) (hf : Differentiable ℝ f) :
    ∀ y x,
      y ^ 2 * partialX (z f) x y + x * y * partialY (z f) x y =
        x * z f x y := by
  exact gap4 f hf

end

end ProofGap.Exercise3318
