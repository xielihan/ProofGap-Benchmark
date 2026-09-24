import ProofGapLean.Prelude.Core
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp

namespace ProofGap.Exercise1027

noncomputable section

theorem gap1 (f : ℝ → ℝ) (hf : Function.Even f) (x : ℝ) :
    f x = f (-x) := by
  exact (hf x).symm

theorem gap2 (f : ℝ → ℝ) (hfd : Differentiable ℝ f)
    (hf : Function.Even f) (x : ℝ) :
    deriv f x = -deriv f (-x) := by
  have hcomp : HasDerivAt (fun y : ℝ => f (-y)) (-deriv f (-x)) x := by
    simpa using ((hfd (-x)).hasDerivAt.comp x (hasDerivAt_id x).neg)
  have heq : (fun y : ℝ => f (-y)) = f := funext hf
  rw [heq] at hcomp
  exact (hfd x).hasDerivAt.unique hcomp

theorem gap3 (f : ℝ → ℝ) (hfd : Differentiable ℝ f)
    (hf : Function.Even f) (x : ℝ) :
    deriv f (-x) = -deriv f x := by
  simpa using gap2 f hfd hf (-x)

theorem gap4 (f : ℝ → ℝ) (hfd : Differentiable ℝ f)
    (hf : Function.Even f) :
    Function.Odd (deriv f) := by
  intro x
  exact gap3 f hfd hf x

theorem gap5 (f : ℝ → ℝ) (hfd : Differentiable ℝ f)
    (hf : Function.Odd f) :
    Function.Even (deriv f) := by
  intro x
  have hcomp : HasDerivAt (fun y : ℝ => f (-y)) (-deriv f (-x)) x := by
    simpa using ((hfd (-x)).hasDerivAt.comp x (hasDerivAt_id x).neg)
  have heq : (fun y : ℝ => f (-y)) = (fun y : ℝ => -f y) := funext hf
  rw [heq] at hcomp
  have hneg : -deriv f (-x) = -deriv f x :=
    hcomp.unique ((hfd x).hasDerivAt.neg)
  exact neg_inj.mp hneg

theorem gap6 (f : ℝ → ℝ) (hfd : Differentiable ℝ f)
    (hf : Function.Even f) :
    Function.Odd (deriv f) := by
  exact gap4 f hfd hf

theorem gap7 (f : ℝ → ℝ) (hfd : Differentiable ℝ f)
    (hf : Function.Odd f) :
    Function.Even (deriv f) := by
  exact gap5 f hfd hf

theorem gap8 (f : ℝ → ℝ) (hfd : Differentiable ℝ f) :
    (Function.Even f → Function.Odd (deriv f)) ∧
      (Function.Odd f → Function.Even (deriv f)) := by
  constructor
  · intro hf
    exact gap6 f hfd hf
  · intro hf
    exact gap7 f hfd hf

end

end ProofGap.Exercise1027
