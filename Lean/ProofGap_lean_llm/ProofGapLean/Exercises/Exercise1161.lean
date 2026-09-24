import ProofGapLean.Prelude.Elementary
import ProofGapLean.Prelude.Discrete
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1161

noncomputable section

def nthDeriv : ℕ → (ℝ → ℝ) → ℝ → ℝ
  | 0, f => f
  | n + 1, f => deriv (nthDeriv n f)

def y (x : ℝ) : ℝ := x ^ 2 * Real.exp (2 * x)
def expanded (x : ℝ) : ℝ :=
  x ^ 2 * nthDeriv 20 (fun z => Real.exp (2 * z)) x +
    2 * x * (Nat.choose 20 1 : ℝ) *
      nthDeriv 19 (fun z => Real.exp (2 * z)) x +
    2 * (Nat.choose 20 2 : ℝ) *
      nthDeriv 18 (fun z => Real.exp (2 * z)) x

private def coeffA : ℕ → ℝ
  | 0 => 1
  | n + 1 => 2 * coeffA n

private def coeffB : ℕ → ℝ
  | 0 => 0
  | n + 1 => 2 * coeffA n + 2 * coeffB n

private def coeffC : ℕ → ℝ
  | 0 => 0
  | n + 1 => coeffB n + 2 * coeffC n

private def model (n : ℕ) (x : ℝ) : ℝ :=
  (coeffA n * x ^ 2 + coeffB n * x + coeffC n) * Real.exp (2 * x)

private theorem hasDerivAt_model (n : ℕ) (x : ℝ) :
    HasDerivAt (model n) (model (n + 1) x) x := by
  have hpoly :
      HasDerivAt
        (fun z : ℝ => coeffA n * z ^ 2 + coeffB n * z + coeffC n)
        (2 * coeffA n * x + coeffB n) x := by
    convert ((((hasDerivAt_id x).pow 2).const_mul (coeffA n)).add
      ((hasDerivAt_id x).const_mul (coeffB n))).add_const (coeffC n)
      using 1 <;>
      simp only [Pi.add_apply, Pi.mul_apply, id_eq] <;> ring
  have hlin : HasDerivAt (fun z : ℝ => 2 * z) 2 x := by
    simpa using (hasDerivAt_id x).const_mul 2
  have hexp : HasDerivAt (fun z : ℝ => Real.exp (2 * z))
      (Real.exp (2 * x) * 2) x := by
    simpa only [Function.comp_def] using
      (Real.hasDerivAt_exp (2 * x)).comp x hlin
  unfold model
  convert hpoly.mul hexp using 1 <;>
    simp only [coeffA, coeffB, coeffC, Pi.mul_apply] <;> ring

private theorem nthDeriv_y_eq_model (n : ℕ) :
    nthDeriv n y = model n := by
  induction n with
  | zero =>
      funext x
      simp [nthDeriv, y, model, coeffA, coeffB, coeffC]
  | succ n ih =>
      funext x
      change deriv (nthDeriv n y) x = model (n + 1) x
      rw [ih]
      exact (hasDerivAt_model n x).deriv

private theorem nthDeriv_exp_two (n : ℕ) (x : ℝ) :
    nthDeriv n (fun z : ℝ => Real.exp (2 * z)) x =
      2 ^ n * Real.exp (2 * x) := by
  induction n generalizing x with
  | zero =>
      simp [nthDeriv]
  | succ n ih =>
      change deriv
        (nthDeriv n (fun z : ℝ => Real.exp (2 * z))) x =
          2 ^ (n + 1) * Real.exp (2 * x)
      rw [show nthDeriv n (fun z : ℝ => Real.exp (2 * z)) =
          fun z : ℝ => 2 ^ n * Real.exp (2 * z) from funext ih]
      have hlin : HasDerivAt (fun z : ℝ => 2 * z) 2 x := by
        simpa using (hasDerivAt_id x).const_mul 2
      have hexp : HasDerivAt (fun z : ℝ => Real.exp (2 * z))
          (Real.exp (2 * x) * 2) x := by
        simpa only [Function.comp_def] using
          (Real.hasDerivAt_exp (2 * x)).comp x hlin
      convert (hexp.const_mul (2 ^ n)).deriv using 1 <;>
        rw [pow_succ] <;> ring

theorem gap1 (x : ℝ) : nthDeriv 20 y x = expanded x := by
  rw [nthDeriv_y_eq_model]
  unfold model expanded
  rw [nthDeriv_exp_two, nthDeriv_exp_two, nthDeriv_exp_two]
  norm_num [coeffA, coeffB, coeffC, Nat.choose]
  ring

theorem gap2 (x : ℝ) :
    expanded x = 2 ^ 20 * Real.exp (2 * x) * (x ^ 2 + 20 * x + 95) := by
  unfold expanded
  rw [nthDeriv_exp_two, nthDeriv_exp_two, nthDeriv_exp_two]
  norm_num [Nat.choose]
  ring

theorem gap3 (x : ℝ) :
    nthDeriv 20 y x =
      2 ^ 20 * Real.exp (2 * x) * (x ^ 2 + 20 * x + 95) := by
  calc
    nthDeriv 20 y x = expanded x := gap1 x
    _ = 2 ^ 20 * Real.exp (2 * x) * (x ^ 2 + 20 * x + 95) :=
      gap2 x

end

end ProofGap.Exercise1161
