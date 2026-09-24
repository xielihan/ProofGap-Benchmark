import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1199

noncomputable section

def iterDeriv (n : ℕ) (f : ℝ → ℝ) : ℝ → ℝ :=
  (deriv^[n]) f

def y (a b x : ℝ) : ℝ :=
  Real.sin (a * x) * Real.cos (b * x)

theorem gap1 (a b x : ℝ) :
    y a b x =
      (1 / 2 : ℝ) * Real.sin ((a + b) * x) +
        (1 / 2 : ℝ) * Real.sin ((a - b) * x) := by
  unfold y
  rw [add_mul, sub_mul, Real.sin_add, Real.sin_sub]
  ring

theorem gap2 (a b : ℝ) (n : ℕ) (x : ℝ) :
    iterDeriv n (y a b) x =
      (1 / 2 : ℝ) * (a + b) ^ n *
          Real.sin ((a + b) * x + (n : ℝ) / 2 * Real.pi) +
        (1 / 2 : ℝ) * (a - b) ^ n *
          Real.sin ((a - b) * x + (n : ℝ) / 2 * Real.pi) := by
  induction n generalizing x with
  | zero =>
      simpa [iterDeriv] using gap1 a b x
  | succ n ih =>
      have hfun :
          (deriv^[n]) (y a b) =
            fun t : ℝ =>
              (1 / 2 : ℝ) * (a + b) ^ n *
                    Real.sin ((a + b) * t + (n : ℝ) / 2 * Real.pi) +
                (1 / 2 : ℝ) * (a - b) ^ n *
                    Real.sin ((a - b) * t + (n : ℝ) / 2 * Real.pi) := by
        funext t
        simpa [iterDeriv] using ih t
      have harg₁ :
          HasDerivAt
            (fun t : ℝ => (a + b) * t + (n : ℝ) / 2 * Real.pi)
            (a + b) x := by
        simpa using
          ((hasDerivAt_id x).const_mul (a + b)).add_const
            ((n : ℝ) / 2 * Real.pi)
      have harg₂ :
          HasDerivAt
            (fun t : ℝ => (a - b) * t + (n : ℝ) / 2 * Real.pi)
            (a - b) x := by
        simpa using
          ((hasDerivAt_id x).const_mul (a - b)).add_const
            ((n : ℝ) / 2 * Real.pi)
      have hterm₁ :
          HasDerivAt
            (fun t : ℝ =>
              (1 / 2 : ℝ) * (a + b) ^ n *
                Real.sin ((a + b) * t + (n : ℝ) / 2 * Real.pi))
            ((1 / 2 : ℝ) * (a + b) ^ n *
              (Real.cos ((a + b) * x + (n : ℝ) / 2 * Real.pi) * (a + b))) x := by
        exact
          (((Real.hasDerivAt_sin
              ((a + b) * x + (n : ℝ) / 2 * Real.pi)).comp x harg₁).const_mul
            ((1 / 2 : ℝ) * (a + b) ^ n))
      have hterm₂ :
          HasDerivAt
            (fun t : ℝ =>
              (1 / 2 : ℝ) * (a - b) ^ n *
                Real.sin ((a - b) * t + (n : ℝ) / 2 * Real.pi))
            ((1 / 2 : ℝ) * (a - b) ^ n *
              (Real.cos ((a - b) * x + (n : ℝ) / 2 * Real.pi) * (a - b))) x := by
        exact
          (((Real.hasDerivAt_sin
              ((a - b) * x + (n : ℝ) / 2 * Real.pi)).comp x harg₂).const_mul
            ((1 / 2 : ℝ) * (a - b) ^ n))
      have hphase (c : ℝ) :
          c * x + (Nat.succ n : ℝ) / 2 * Real.pi =
            (c * x + (n : ℝ) / 2 * Real.pi) + Real.pi / 2 := by
        rw [Nat.cast_succ]
        ring
      unfold iterDeriv
      rw [Function.iterate_succ_apply', hfun]
      simp only [hphase (a + b), hphase (a - b), Real.sin_add_pi_div_two]
      calc
        deriv
              (fun t : ℝ =>
                (1 / 2 : ℝ) * (a + b) ^ n *
                      Real.sin ((a + b) * t + (n : ℝ) / 2 * Real.pi) +
                  (1 / 2 : ℝ) * (a - b) ^ n *
                      Real.sin ((a - b) * t + (n : ℝ) / 2 * Real.pi))
              x = _ := (hterm₁.add hterm₂).deriv
        _ = _ := by
          simp only [pow_succ]
          ring

end

end ProofGap.Exercise1199
