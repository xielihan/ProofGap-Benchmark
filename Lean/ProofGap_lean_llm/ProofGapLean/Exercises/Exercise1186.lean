import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1186

noncomputable section

def iterDeriv (n : ℕ) (f : ℝ → ℝ) : ℝ → ℝ :=
  (deriv^[n]) f

private theorem iterDeriv_const_mul
    (n : ℕ) (c : ℝ) (f : ℝ → ℝ) (x : ℝ)
    (hf : ContDiff ℝ n f) :
    iterDeriv n (fun z => c * f z) x = c * iterDeriv n f x := by
  induction n generalizing f x with
  | zero =>
      simp [iterDeriv]
  | succ n ih =>
      have hfDiff : Differentiable ℝ f :=
        hf.differentiable (by norm_num)
      have hder :
          deriv (fun z => c * f z) = fun z => c * deriv f z := by
        funext z
        convert ((hfDiff z).hasDerivAt.const_mul c).deriv using 1 <;> ring
      have hfd : ContDiff ℝ n (deriv f) := by
        simpa using hf.deriv'
      simp only [iterDeriv, Function.iterate_succ_apply, hder]
      exact ih (deriv f) x hfd

theorem gap1 (a b x : ℝ) :
    iterDeriv 1 (fun z : ℝ => a * z + b) x = a := by
  change deriv (fun z : ℝ => a * z + b) x = a
  convert ((hasDerivAt_id x).const_mul a).add_const b |>.deriv using 1 <;>
    ring

theorem gap2 (f : ℝ → ℝ) (n : ℕ) (a b x : ℝ)
    (hf : ContDiff ℝ n f) :
    iterDeriv n (fun z : ℝ => f (a * z + b)) x =
      a ^ n * iterDeriv n f (a * x + b) := by
  induction n generalizing f x with
  | zero =>
      simp [iterDeriv]
  | succ n ih =>
      have hfDiff : Differentiable ℝ f :=
        hf.differentiable (by norm_num)
      have hlin : ∀ z, HasDerivAt (fun w : ℝ => a * w + b) a z := by
        intro z
        convert ((hasDerivAt_id z).const_mul a).add_const b using 1 <;>
          ring
      have hchain :
          deriv (fun z : ℝ => f (a * z + b)) =
            fun z => a * deriv f (a * z + b) := by
        funext z
        have hcomp :=
          (hfDiff (a * z + b)).hasDerivAt.comp z (hlin z)
        calc
          deriv (fun w : ℝ => f (a * w + b)) z =
              deriv f (a * z + b) * a := hcomp.deriv
          _ = a * deriv f (a * z + b) := by ring
      have hfd : ContDiff ℝ n (deriv f) := by
        simpa using hf.deriv'
      have hinner :
          ContDiff ℝ n (fun z : ℝ => deriv f (a * z + b)) := by
        have haffine : ContDiff ℝ n (fun z : ℝ => a * z + b) := by
          exact (contDiff_const.mul contDiff_id).add contDiff_const
        exact hfd.comp haffine
      simp only [iterDeriv, Function.iterate_succ_apply, hchain]
      calc
        (deriv^[n]) (fun z => a * deriv f (a * z + b)) x =
            a * (deriv^[n]) (fun z => deriv f (a * z + b)) x := by
          exact iterDeriv_const_mul n a
            (fun z => deriv f (a * z + b)) x hinner
        _ = a * (a ^ n * iterDeriv n (deriv f) (a * x + b)) := by
          have hi := ih (deriv f) x hfd
          change (deriv^[n]) (fun z => deriv f (a * z + b)) x =
            a ^ n * iterDeriv n (deriv f) (a * x + b) at hi
          rw [hi]
        _ = a ^ (n + 1) * iterDeriv n (deriv f) (a * x + b) := by
          rw [pow_succ]
          ring

theorem gap3 (f : ℝ → ℝ) (n : ℕ) (a b x : ℝ)
    (hf : ContDiff ℝ n f) :
    iterDeriv n (fun z : ℝ => f (a * z + b)) x =
      a ^ n * iterDeriv n f (a * x + b) := by
  exact gap2 f n a b x hf

end

end ProofGap.Exercise1186
