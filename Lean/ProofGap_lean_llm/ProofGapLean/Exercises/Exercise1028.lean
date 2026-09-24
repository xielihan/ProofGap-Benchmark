import ProofGapLean.Prelude.Core
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp

namespace ProofGap.Exercise1028

noncomputable section

theorem gap1 (f : ℝ → ℝ) (T x : ℝ)
    (hper : Function.Periodic f T) :
    f (x + T) = f x := by
  exact hper x

theorem gap2 (f : ℝ → ℝ) (T x : ℝ)
    (hfd : Differentiable ℝ f) (hper : Function.Periodic f T) :
    deriv f (x + T) = deriv f x := by
  have hf : HasDerivAt f (deriv f (x + T)) (x + T) :=
    (hfd (x + T)).hasDerivAt
  have hg : HasDerivAt (fun y : ℝ => y + T) 1 x := by
    simpa using (hasDerivAt_id x).add_const T
  have hshift :
      HasDerivAt (fun y : ℝ => f (y + T)) (deriv f (x + T)) x := by
    simpa using hf.comp x hg
  have heq : (fun y : ℝ => f (y + T)) = f := funext hper
  rw [heq] at hshift
  exact hshift.deriv.symm

theorem gap3 (f : ℝ → ℝ) (T : ℝ)
    (hfd : Differentiable ℝ f) (hper : Function.Periodic f T) :
    Function.Periodic (deriv f) T := by
  intro x
  exact gap2 f T x hfd hper

theorem gap4 (f : ℝ → ℝ) (T : ℝ)
    (hfd : Differentiable ℝ f) (hper : Function.Periodic f T) :
    Function.Periodic (deriv f) T := by
  exact gap3 f T hfd hper

end

end ProofGap.Exercise1028
