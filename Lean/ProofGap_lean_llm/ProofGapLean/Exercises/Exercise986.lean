import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise986

noncomputable section

def y1 (f : ℝ → ℝ) (x : ℝ) : ℝ := f (x ^ 2)
def y2 (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  f (Real.sin x ^ 2) + f (Real.cos x ^ 2)
def y3 (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  f (Real.exp x) * Real.exp (f x)
def y4 (f : ℝ → ℝ) (x : ℝ) : ℝ := f (f (f x))

def expandedY2 (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  2 * Real.sin x * Real.cos x * deriv f (Real.sin x ^ 2) -
    2 * Real.sin x * Real.cos x * deriv f (Real.cos x ^ 2)

def finalY2 (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  Real.sin (2 * x) *
    (deriv f (Real.sin x ^ 2) - deriv f (Real.cos x ^ 2))

theorem gap1 (f : ℝ → ℝ) (hf : Differentiable ℝ f) (x : ℝ) :
    HasDerivAt (y1 f) (2 * x * deriv f (x ^ 2)) x := by
  have hsq : HasDerivAt (fun t : ℝ => t ^ 2) (2 * x) x := by
    simpa only [id_eq, pow_two, mul_one, one_mul, two_mul] using
      (hasDerivAt_id x).mul (hasDerivAt_id x)
  have hcomp : HasDerivAt (fun t : ℝ => f (t ^ 2))
      (deriv f (x ^ 2) * (2 * x)) x :=
    (hf (x ^ 2)).hasDerivAt.comp x hsq
  unfold y1
  convert hcomp using 1 <;> ring

theorem gap2 (f : ℝ → ℝ) (hf : Differentiable ℝ f) (x : ℝ) :
    HasDerivAt (y2 f) (expandedY2 f x) x := by
  have hs : HasDerivAt (fun t : ℝ => Real.sin t ^ 2)
      (2 * Real.sin x * Real.cos x) x := by
    convert (Real.hasDerivAt_sin x).mul (Real.hasDerivAt_sin x) using 1 <;> try ring
    funext t
    rfl
  have hc : HasDerivAt (fun t : ℝ => Real.cos t ^ 2)
      (-2 * Real.sin x * Real.cos x) x := by
    convert (Real.hasDerivAt_cos x).mul (Real.hasDerivAt_cos x) using 1 <;> try ring
    funext t
    rfl
  have hfs : HasDerivAt (fun t : ℝ => f (Real.sin t ^ 2))
      (deriv f (Real.sin x ^ 2) * (2 * Real.sin x * Real.cos x)) x :=
    (hf (Real.sin x ^ 2)).hasDerivAt.comp x hs
  have hfc : HasDerivAt (fun t : ℝ => f (Real.cos t ^ 2))
      (deriv f (Real.cos x ^ 2) * (-2 * Real.sin x * Real.cos x)) x :=
    (hf (Real.cos x ^ 2)).hasDerivAt.comp x hc
  unfold y2 expandedY2
  convert hfs.add hfc using 1 <;> ring

theorem gap3 (f : ℝ → ℝ) (x : ℝ) :
    expandedY2 f x = finalY2 f x := by
  unfold expandedY2 finalY2
  rw [Real.sin_two_mul]
  ring

theorem gap4 (f : ℝ → ℝ) (hf : Differentiable ℝ f) (x : ℝ) :
    HasDerivAt (y2 f) (finalY2 f x) x := by
  rw [← gap3 f x]
  exact gap2 f hf x

theorem gap5 (f : ℝ → ℝ) (hf : Differentiable ℝ f) (x : ℝ) :
    HasDerivAt (y3 f)
      (Real.exp (f x) *
        (deriv f x * f (Real.exp x) + Real.exp x * deriv f (Real.exp x))) x := by
  have hleft : HasDerivAt (fun t : ℝ => f (Real.exp t))
      (deriv f (Real.exp x) * Real.exp x) x :=
    (hf (Real.exp x)).hasDerivAt.comp x (Real.hasDerivAt_exp x)
  have hright : HasDerivAt (fun t : ℝ => Real.exp (f t))
      (Real.exp (f x) * deriv f x) x :=
    (Real.hasDerivAt_exp (f x)).comp x (hf x).hasDerivAt
  unfold y3
  convert hleft.mul hright using 1 <;> ring

theorem gap6 (f : ℝ → ℝ) (hf : Differentiable ℝ f) (x : ℝ) :
    HasDerivAt (y4 f)
      (deriv f x * deriv f (f x) * deriv f (f (f x))) x := by
  have hinner : HasDerivAt (fun t : ℝ => f (f t))
      (deriv f (f x) * deriv f x) x :=
    (hf (f x)).hasDerivAt.comp x (hf x).hasDerivAt
  have hall : HasDerivAt (fun t : ℝ => f (f (f t)))
      (deriv f (f (f x)) * (deriv f (f x) * deriv f x)) x :=
    (hf (f (f x))).hasDerivAt.comp x hinner
  unfold y4
  convert hall using 1 <;> ring

end

end ProofGap.Exercise986
