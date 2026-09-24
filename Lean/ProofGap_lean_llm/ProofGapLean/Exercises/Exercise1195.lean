import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1195

noncomputable section

def iterDeriv (n : ℕ) (f : ℝ → ℝ) : ℝ → ℝ :=
  (deriv^[n]) f

def y (x : ℝ) : ℝ := Real.sin x ^ 3

theorem gap1 (x : ℝ) :
    y x = Real.sin x * Real.sin x ^ 2 := by
  unfold y
  ring

theorem gap2 (x : ℝ) :
    Real.sin x * Real.sin x ^ 2 =
      (1 / 2 : ℝ) * Real.sin x * (1 - Real.cos (2 * x)) := by
  have hs : Real.sin x ^ 2 =
      (1 / 2 : ℝ) * (1 - Real.cos (2 * x)) := by
    rw [Real.cos_two_mul]
    nlinarith [Real.sin_sq_add_cos_sq x]
  rw [hs]
  ring

theorem gap3 (x : ℝ) :
    (1 / 2 : ℝ) * Real.sin x * (1 - Real.cos (2 * x)) =
      (1 / 2 : ℝ) * Real.sin x -
        (1 / 2 : ℝ) * Real.sin x * Real.cos (2 * x) := by
  ring

theorem gap4 (x : ℝ) :
    (1 / 2 : ℝ) * Real.sin x -
        (1 / 2 : ℝ) * Real.sin x * Real.cos (2 * x) =
      (3 / 4 : ℝ) * Real.sin x - (1 / 4 : ℝ) * Real.sin (3 * x) := by
  rw [Real.cos_two_mul, Real.sin_three_mul]
  have h := congrArg (fun z : ℝ => Real.sin x * z)
    (Real.sin_sq_add_cos_sq x)
  nlinarith

theorem gap5 (x : ℝ) :
    y x = (3 / 4 : ℝ) * Real.sin x - (1 / 4 : ℝ) * Real.sin (3 * x) := by
  rw [gap1, gap2, gap3, gap4]

theorem gap6 (n : ℕ) (x : ℝ) :
    iterDeriv n y x =
      (3 / 4 : ℝ) * Real.sin (x + (n : ℝ) / 2 * Real.pi) -
        (3 : ℝ) ^ n / 4 * Real.sin (3 * x + (n : ℝ) / 2 * Real.pi) := by
  induction n generalizing x with
  | zero =>
      simpa [iterDeriv] using gap5 x
  | succ n ih =>
      have hfun : iterDeriv n y =
          fun t : ℝ =>
            (3 / 4 : ℝ) * Real.sin (t + (n : ℝ) / 2 * Real.pi) -
              (3 : ℝ) ^ n / 4 *
                Real.sin (3 * t + (n : ℝ) / 2 * Real.pi) := by
        funext t
        exact ih t
      have hsin1 :
          HasDerivAt
            (fun t : ℝ => Real.sin (t + (n : ℝ) / 2 * Real.pi))
            (Real.cos (x + (n : ℝ) / 2 * Real.pi)) x := by
        simpa [Function.comp_def] using
          (Real.hasDerivAt_sin (x + (n : ℝ) / 2 * Real.pi)).comp x
            ((hasDerivAt_id x).add_const ((n : ℝ) / 2 * Real.pi))
      have hsin3 :
          HasDerivAt
            (fun t : ℝ => Real.sin (3 * t + (n : ℝ) / 2 * Real.pi))
            (3 * Real.cos (3 * x + (n : ℝ) / 2 * Real.pi)) x := by
        simpa [Function.comp_def, mul_comm] using
          (Real.hasDerivAt_sin (3 * x + (n : ℝ) / 2 * Real.pi)).comp x
            (((hasDerivAt_id x).const_mul (3 : ℝ)).add_const
              ((n : ℝ) / 2 * Real.pi))
      have hderiv :
          HasDerivAt
            (fun t : ℝ =>
              (3 / 4 : ℝ) * Real.sin (t + (n : ℝ) / 2 * Real.pi) -
                (3 : ℝ) ^ n / 4 *
                  Real.sin (3 * t + (n : ℝ) / 2 * Real.pi))
            ((3 / 4 : ℝ) * Real.cos (x + (n : ℝ) / 2 * Real.pi) -
              (3 : ℝ) ^ n / 4 *
                (3 * Real.cos (3 * x + (n : ℝ) / 2 * Real.pi))) x := by
        exact
          (hsin1.const_mul (3 / 4 : ℝ)).sub
            (hsin3.const_mul ((3 : ℝ) ^ n / 4))
      have hiter :
          iterDeriv n.succ y x = deriv (iterDeriv n y) x := by
        simp only [iterDeriv, Function.iterate_succ_apply']
      have hphase (z : ℝ) :
          z + (n.succ : ℝ) / 2 * Real.pi =
            (z + (n : ℝ) / 2 * Real.pi) + Real.pi / 2 := by
        simp only [Nat.cast_succ]
        ring
      have hnext1 :
          Real.sin (x + (n.succ : ℝ) / 2 * Real.pi) =
            Real.cos (x + (n : ℝ) / 2 * Real.pi) := by
        rw [hphase x, Real.sin_add_pi_div_two]
      have hnext3 :
          Real.sin (3 * x + (n.succ : ℝ) / 2 * Real.pi) =
            Real.cos (3 * x + (n : ℝ) / 2 * Real.pi) := by
        rw [hphase (3 * x), Real.sin_add_pi_div_two]
      rw [hiter, hfun, hderiv.deriv, hnext1, hnext3, pow_succ]
      ring

end

end ProofGap.Exercise1195
