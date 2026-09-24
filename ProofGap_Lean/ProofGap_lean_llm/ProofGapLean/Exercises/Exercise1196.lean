import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1196

noncomputable section

def iterDeriv (n : ℕ) (f : ℝ → ℝ) : ℝ → ℝ :=
  (deriv^[n]) f

def y (x : ℝ) : ℝ := Real.cos x ^ 3

private theorem deriv_cos_affine_add
    (a b c d e f x : ℝ) :
    deriv
        (fun t : ℝ =>
          a * Real.cos (b * t + c) + d * Real.cos (e * t + f)) x =
      a * (-Real.sin (b * x + c) * b) +
        d * (-Real.sin (e * x + f) * e) := by
  have hb : HasDerivAt (fun t : ℝ => b * t + c) b x := by
    convert
      ((hasDerivAt_id x).const_mul b).add (hasDerivAt_const x c) using 1 <;>
      ring
  have he : HasDerivAt (fun t : ℝ => e * t + f) e x := by
    convert
      ((hasDerivAt_id x).const_mul e).add (hasDerivAt_const x f) using 1 <;>
      ring
  have h1 :
      HasDerivAt (fun t : ℝ => a * Real.cos (b * t + c))
        (a * (-Real.sin (b * x + c) * b)) x := by
    convert
      ((Real.hasDerivAt_cos (b * x + c)).comp x hb).const_mul a using 1 <;>
      ring
  have h2 :
      HasDerivAt (fun t : ℝ => d * Real.cos (e * t + f))
        (d * (-Real.sin (e * x + f) * e)) x := by
    convert
      ((Real.hasDerivAt_cos (e * x + f)).comp x he).const_mul d using 1 <;>
      ring
  exact (h1.add h2).deriv

theorem gap1 (x : ℝ) :
    y x = Real.cos x * Real.cos x ^ 2 := by
  unfold y
  ring

theorem gap2 (x : ℝ) :
    Real.cos x * Real.cos x ^ 2 =
      (1 / 2 : ℝ) * Real.cos x * (1 + Real.cos (2 * x)) := by
  rw [Real.cos_two_mul x]
  ring

theorem gap3 (x : ℝ) :
    (1 / 2 : ℝ) * Real.cos x * (1 + Real.cos (2 * x)) =
      (1 / 2 : ℝ) * Real.cos x +
        (1 / 2 : ℝ) * Real.cos x * Real.cos (2 * x) := by
  ring

theorem gap4 (x : ℝ) :
    (1 / 2 : ℝ) * Real.cos x +
        (1 / 2 : ℝ) * Real.cos x * Real.cos (2 * x) =
      (3 / 4 : ℝ) * Real.cos x + (1 / 4 : ℝ) * Real.cos (3 * x) := by
  rw [Real.cos_two_mul x, Real.cos_three_mul x]
  ring

theorem gap5 (x : ℝ) :
    y x = (3 / 4 : ℝ) * Real.cos x + (1 / 4 : ℝ) * Real.cos (3 * x) := by
  calc
    y x = Real.cos x * Real.cos x ^ 2 := gap1 x
    _ = (1 / 2 : ℝ) * Real.cos x * (1 + Real.cos (2 * x)) := gap2 x
    _ = (1 / 2 : ℝ) * Real.cos x +
          (1 / 2 : ℝ) * Real.cos x * Real.cos (2 * x) := gap3 x
    _ = (3 / 4 : ℝ) * Real.cos x +
          (1 / 4 : ℝ) * Real.cos (3 * x) := gap4 x

theorem gap6 (n : ℕ) (x : ℝ) :
    iterDeriv n y x =
      (3 / 4 : ℝ) * Real.cos (x + (n : ℝ) / 2 * Real.pi) +
        (3 : ℝ) ^ n / 4 * Real.cos (3 * x + (n : ℝ) / 2 * Real.pi) := by
  induction n generalizing x with
  | zero =>
      simpa [iterDeriv] using gap5 x
  | succ n ih =>
      have hiter : iterDeriv (Nat.succ n) y =
          deriv (iterDeriv n y) := by
        simp only [iterDeriv, Function.iterate_succ_apply']
      rw [hiter]
      have hfun : iterDeriv n y =
          fun t : ℝ =>
            (3 / 4 : ℝ) * Real.cos (t + (n : ℝ) / 2 * Real.pi) +
              (3 : ℝ) ^ n / 4 *
                Real.cos (3 * t + (n : ℝ) / 2 * Real.pi) := by
        funext t
        exact ih t
      rw [hfun]
      have hd :
          deriv
              (fun t : ℝ =>
                (3 / 4 : ℝ) * Real.cos (t + (n : ℝ) / 2 * Real.pi) +
                  (3 : ℝ) ^ n / 4 *
                    Real.cos (3 * t + (n : ℝ) / 2 * Real.pi)) x =
            (3 / 4 : ℝ) *
                (-Real.sin (x + (n : ℝ) / 2 * Real.pi)) +
              (3 : ℝ) ^ n / 4 *
                (-Real.sin (3 * x + (n : ℝ) / 2 * Real.pi) * 3) := by
        simpa only [one_mul, mul_one] using
          (deriv_cos_affine_add (3 / 4 : ℝ) 1
            ((n : ℝ) / 2 * Real.pi) ((3 : ℝ) ^ n / 4) 3
            ((n : ℝ) / 2 * Real.pi) x)
      rw [hd]
      have hphase :
          ((Nat.succ n : ℕ) : ℝ) / 2 * Real.pi =
            (n : ℝ) / 2 * Real.pi + Real.pi / 2 := by
        rw [Nat.cast_succ]
        ring
      have hcos1 :
          Real.cos
              (x + ((Nat.succ n : ℕ) : ℝ) / 2 * Real.pi) =
            -Real.sin (x + (n : ℝ) / 2 * Real.pi) := by
        rw [hphase]
        rw [show
          x + ((n : ℝ) / 2 * Real.pi + Real.pi / 2) =
            (x + (n : ℝ) / 2 * Real.pi) + Real.pi / 2 by ring]
        rw [Real.cos_add, Real.cos_pi_div_two, Real.sin_pi_div_two]
        ring
      have hcos3 :
          Real.cos
              (3 * x + ((Nat.succ n : ℕ) : ℝ) / 2 * Real.pi) =
            -Real.sin (3 * x + (n : ℝ) / 2 * Real.pi) := by
        rw [hphase]
        rw [show
          3 * x + ((n : ℝ) / 2 * Real.pi + Real.pi / 2) =
            (3 * x + (n : ℝ) / 2 * Real.pi) + Real.pi / 2 by ring]
        rw [Real.cos_add, Real.cos_pi_div_two, Real.sin_pi_div_two]
        ring
      rw [hcos1, hcos3, pow_succ]
      ring

end

end ProofGap.Exercise1196
