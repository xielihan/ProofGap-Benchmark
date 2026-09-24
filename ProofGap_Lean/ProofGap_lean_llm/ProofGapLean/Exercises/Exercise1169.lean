import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1169

noncomputable section

def nthDeriv : ℕ → (ℝ → ℝ) → ℝ → ℝ
  | 0, f => f
  | n + 1, f => deriv (nthDeriv n f)

def y (x : ℝ) : ℝ := Real.exp x * Real.cos x

theorem gap1 (x : ℝ) :
    deriv y x = Real.exp x * (Real.cos x - Real.sin x) := by
  unfold y
  have h :=
    (Real.hasDerivAt_exp x).mul (Real.hasDerivAt_cos x)
  convert h.deriv using 1 <;> ring

theorem gap2 (x : ℝ) :
    nthDeriv 2 y x =
      Real.exp x *
        (Real.cos x - Real.sin x + -Real.sin x - Real.cos x) := by
  change deriv (deriv y) x = _
  rw [show deriv y = fun t => Real.exp t * (Real.cos t - Real.sin t) from
    funext (fun t => gap1 t)]
  have h :=
    (Real.hasDerivAt_exp x).mul
      ((Real.hasDerivAt_cos x).sub (Real.hasDerivAt_sin x))
  convert h.deriv using 1 <;>
    simp only [Pi.sub_apply, Pi.add_apply] <;> ring

theorem gap3 (x : ℝ) :
    Real.exp x *
        (Real.cos x - Real.sin x + -Real.sin x - Real.cos x) =
      -2 * Real.exp x * Real.sin x := by
  ring

theorem gap4 (x : ℝ) :
    nthDeriv 2 y x = -2 * Real.exp x * Real.sin x := by
  exact (gap2 x).trans (gap3 x)

theorem gap5 (x : ℝ) :
    nthDeriv 3 y x =
      -2 * Real.exp x * (Real.sin x + Real.cos x) := by
  change deriv (nthDeriv 2 y) x = _
  rw [show nthDeriv 2 y = fun t => -2 * Real.exp t * Real.sin t from
    funext (fun t => gap4 t)]
  have h :=
    ((Real.hasDerivAt_exp x).const_mul (-2)).mul
      (Real.hasDerivAt_sin x)
  convert h.deriv using 1 <;> ring

theorem gap6 (x : ℝ) :
    nthDeriv 4 y x =
      -2 * Real.exp x *
        (Real.sin x + Real.cos x + Real.cos x - Real.sin x) := by
  change deriv (nthDeriv 3 y) x = _
  rw [show nthDeriv 3 y =
      fun t => -2 * Real.exp t * (Real.sin t + Real.cos t) from
    funext (fun t => gap5 t)]
  have h :=
    ((Real.hasDerivAt_exp x).const_mul (-2)).mul
      ((Real.hasDerivAt_sin x).add (Real.hasDerivAt_cos x))
  convert h.deriv using 1 <;>
    simp only [Pi.add_apply, Pi.sub_apply] <;> ring

theorem gap7 (x : ℝ) :
    -2 * Real.exp x *
        (Real.sin x + Real.cos x + Real.cos x - Real.sin x) =
      -4 * Real.exp x * Real.cos x := by
  ring

theorem gap8 (x : ℝ) :
    nthDeriv 4 y x = -4 * Real.exp x * Real.cos x := by
  exact (gap6 x).trans (gap7 x)

end

end ProofGap.Exercise1169
