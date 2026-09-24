import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1206

noncomputable section

def iterDeriv (n : ℕ) (f : ℝ → ℝ) : ℝ → ℝ := (deriv^[n]) f
def y (x : ℝ) : ℝ := Real.exp x * Real.cos x

private theorem deriv_scaled_exp_cos (a c x : ℝ) :
    deriv (fun t : ℝ => a * Real.exp t * Real.cos (t + c)) x =
      a * Real.exp x * (Real.cos (x + c) - Real.sin (x + c)) := by
  have hshift : HasDerivAt (fun t : ℝ => t + c) 1 x := by
    exact (hasDerivAt_id x).add_const c
  have hcos :
      HasDerivAt (fun t : ℝ => Real.cos (t + c))
        (-Real.sin (x + c)) x := by
    simpa only [Function.comp_apply, mul_one] using
      (Real.hasDerivAt_cos (x + c)).comp x hshift
  have hprod :=
    ((hasDerivAt_const x a).mul (Real.hasDerivAt_exp x)).mul hcos
  simpa [sub_eq_add_neg, mul_add] using hprod.deriv

private theorem cos_sub_sin_shift (z : ℝ) :
    Real.cos z - Real.sin z =
      Real.sqrt 2 * Real.cos (z + Real.pi / 4) := by
  rw [Real.cos_add, Real.cos_pi_div_four, Real.sin_pi_div_four]
  have hs : (Real.sqrt 2) ^ 2 = (2 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  calc
    Real.cos z - Real.sin z =
        (Real.sqrt 2) ^ 2 / 2 * (Real.cos z - Real.sin z) := by
      rw [hs]
      ring
    _ = Real.sqrt 2 *
          (Real.cos z * (Real.sqrt 2 / 2) -
            Real.sin z * (Real.sqrt 2 / 2)) := by
      ring

private theorem iterDeriv_succ_eq (n : ℕ) (f : ℝ → ℝ) :
    iterDeriv (n + 1) f = deriv (iterDeriv n f) := by
  simpa [iterDeriv] using
    (Function.iterate_succ_apply' deriv n f)

theorem gap1 (x : ℝ) :
    deriv y x = Real.exp x * (Real.cos x - Real.sin x) := by
  change deriv (fun t : ℝ => Real.exp t * Real.cos t) x = _
  simpa only [one_mul, add_zero] using (deriv_scaled_exp_cos 1 0 x)

theorem gap2 (x : ℝ) :
    Real.exp x * (Real.cos x - Real.sin x) =
      Real.sqrt 2 * Real.exp x * Real.cos (x + Real.pi / 4) := by
  rw [cos_sub_sin_shift x]
  ring

theorem gap3 (x : ℝ) :
    deriv y x = Real.sqrt 2 * Real.exp x * Real.cos (x + Real.pi / 4) := by
  calc
    deriv y x = Real.exp x * (Real.cos x - Real.sin x) := gap1 x
    _ = Real.sqrt 2 * Real.exp x * Real.cos (x + Real.pi / 4) := gap2 x

theorem gap4 (x : ℝ) :
    iterDeriv 2 y x =
      Real.sqrt 2 * Real.exp x *
        (Real.cos (x + Real.pi / 4) - Real.sin (x + Real.pi / 4)) := by
  change deriv (deriv y) x = _
  have hfun :
      deriv y =
        (fun t : ℝ =>
          Real.sqrt 2 * Real.exp t * Real.cos (t + Real.pi / 4)) := by
    funext t
    exact gap3 t
  rw [hfun]
  exact deriv_scaled_exp_cos (Real.sqrt 2) (Real.pi / 4) x

theorem gap5 (x : ℝ) :
    Real.sqrt 2 * Real.exp x *
        (Real.cos (x + Real.pi / 4) - Real.sin (x + Real.pi / 4)) =
      (Real.sqrt 2) ^ 2 * Real.exp x * Real.cos (x + 2 * Real.pi / 4) := by
  rw [cos_sub_sin_shift (x + Real.pi / 4)]
  have hangle :
      (x + Real.pi / 4) + Real.pi / 4 = x + 2 * Real.pi / 4 := by
    ring
  rw [hangle]
  ring

theorem gap6 (x : ℝ) :
    iterDeriv 2 y x =
      (Real.sqrt 2) ^ 2 * Real.exp x * Real.cos (x + 2 * Real.pi / 4) := by
  calc
    iterDeriv 2 y x =
        Real.sqrt 2 * Real.exp x *
          (Real.cos (x + Real.pi / 4) - Real.sin (x + Real.pi / 4)) := gap4 x
    _ = (Real.sqrt 2) ^ 2 * Real.exp x *
          Real.cos (x + 2 * Real.pi / 4) := gap5 x

theorem gap7 (n : ℕ) (x : ℝ) :
    iterDeriv n y x =
      (Real.sqrt 2) ^ n * Real.exp x *
        Real.cos (x + (n : ℝ) * Real.pi / 4) := by
  induction n generalizing x with
  | zero =>
      simp [iterDeriv, y]
  | succ n ih =>
      rw [iterDeriv_succ_eq n y]
      have hfun :
          iterDeriv n y =
            (fun t : ℝ =>
              (Real.sqrt 2) ^ n * Real.exp t *
                Real.cos (t + (n : ℝ) * Real.pi / 4)) := by
        funext t
        exact ih t
      rw [hfun]
      rw [deriv_scaled_exp_cos]
      rw [cos_sub_sin_shift]
      have hangle :
          x + ((Nat.succ n : ℕ) : ℝ) * Real.pi / 4 =
            (x + (n : ℝ) * Real.pi / 4) + Real.pi / 4 := by
        rw [Nat.cast_succ]
        ring
      rw [pow_succ, hangle]
      ring

end

end ProofGap.Exercise1206
