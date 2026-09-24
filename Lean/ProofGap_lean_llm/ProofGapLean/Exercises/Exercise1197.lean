import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1197

noncomputable section

def iterDeriv (n : ℕ) (f : ℝ → ℝ) : ℝ → ℝ :=
  (deriv^[n]) f

def y (a b x : ℝ) : ℝ :=
  Real.sin (a * x) * Real.sin (b * x)

private theorem hasDerivAt_cosWave_succ (c : ℝ) (n : ℕ) (x : ℝ) :
    HasDerivAt
      (fun t : ℝ =>
        (1 / 2 : ℝ) * c ^ n *
          Real.cos (c * t + (n : ℝ) / 2 * Real.pi))
      ((1 / 2 : ℝ) * c ^ (Nat.succ n) *
        Real.cos
          (c * x + ((Nat.succ n : ℕ) : ℝ) / 2 * Real.pi))
      x := by
  have hlin :
      HasDerivAt
        (fun t : ℝ => c * t + (n : ℝ) / 2 * Real.pi) c x := by
    simpa using
      (((hasDerivAt_id x).const_mul c).add_const
        ((n : ℝ) / 2 * Real.pi))
  have hcos :
      HasDerivAt
        (fun t : ℝ =>
          Real.cos (c * t + (n : ℝ) / 2 * Real.pi))
        (-Real.sin (c * x + (n : ℝ) / 2 * Real.pi) * c) x :=
    (Real.hasDerivAt_cos _).comp x hlin
  have hphase :
      c * x + ((Nat.succ n : ℕ) : ℝ) / 2 * Real.pi =
        (c * x + (n : ℝ) / 2 * Real.pi) + Real.pi / 2 := by
    rw [Nat.cast_succ]
    ring
  have htrig :
      Real.cos
          (c * x + ((Nat.succ n : ℕ) : ℝ) / 2 * Real.pi) =
        -Real.sin (c * x + (n : ℝ) / 2 * Real.pi) := by
    rw [hphase, Real.cos_add, Real.cos_pi_div_two,
      Real.sin_pi_div_two]
    ring
  convert hcos.const_mul ((1 / 2 : ℝ) * c ^ n) using 1
  rw [htrig, pow_succ]
  ring

theorem gap1 (a b x : ℝ) :
    y a b x =
      (1 / 2 : ℝ) * Real.cos ((a - b) * x) -
        (1 / 2 : ℝ) * Real.cos ((a + b) * x) := by
  unfold y
  have hsub : (a - b) * x = a * x - b * x := by ring
  have hadd : (a + b) * x = a * x + b * x := by ring
  rw [hsub, hadd, Real.cos_sub, Real.cos_add]
  ring

theorem gap2 (a b : ℝ) (n : ℕ) (x : ℝ) :
    iterDeriv n (y a b) x =
      (1 / 2 : ℝ) * (a - b) ^ n *
          Real.cos ((a - b) * x + (n : ℝ) / 2 * Real.pi) -
        (1 / 2 : ℝ) * (a + b) ^ n *
          Real.cos ((a + b) * x + (n : ℝ) / 2 * Real.pi) := by
  induction n generalizing x with
  | zero =>
      simpa [iterDeriv] using gap1 a b x
  | succ n ih =>
      rw [iterDeriv, Function.iterate_succ_apply']
      have hfun :
          (deriv^[n]) (y a b) =
            fun t : ℝ =>
              (1 / 2 : ℝ) * (a - b) ^ n *
                  Real.cos ((a - b) * t + (n : ℝ) / 2 * Real.pi) -
                (1 / 2 : ℝ) * (a + b) ^ n *
                  Real.cos ((a + b) * t + (n : ℝ) / 2 * Real.pi) := by
        funext t
        simpa [iterDeriv] using ih t
      rw [hfun]
      exact
        ((hasDerivAt_cosWave_succ (a - b) n x).sub
          (hasDerivAt_cosWave_succ (a + b) n x)).deriv

end

end ProofGap.Exercise1197
