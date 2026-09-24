import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1194

noncomputable section

def iterDeriv (n : ℕ) (f : ℝ → ℝ) : ℝ → ℝ :=
  (deriv^[n]) f

def y (x : ℝ) : ℝ := Real.cos x ^ 2

private theorem iterDeriv_neg (n : ℕ) (f : ℝ → ℝ) (x : ℝ) :
    iterDeriv n (fun z => -f z) x = -iterDeriv n f x := by
  induction n generalizing x with
  | zero =>
      simp [iterDeriv]
  | succ n ih =>
      rw [show iterDeriv (Nat.succ n) (fun z => -f z) x =
          deriv (iterDeriv n (fun z => -f z)) x by
            simp only [iterDeriv, Function.iterate_succ_apply']]
      rw [show iterDeriv (Nat.succ n) f x = deriv (iterDeriv n f) x by
            simp only [iterDeriv, Function.iterate_succ_apply']]
      have hfun : iterDeriv n (fun z => -f z) =
          fun z => -iterDeriv n f z := by
        funext z
        exact ih z
      rw [hfun]
      change deriv (fun z : ℝ => -iterDeriv n f z) x =
        -deriv (iterDeriv n f) x
      by_cases h : DifferentiableAt ℝ (iterDeriv n f) x
      · exact h.hasDerivAt.neg.deriv
      · have hneg :
            ¬DifferentiableAt ℝ (fun z : ℝ => -iterDeriv n f z) x := by
          intro hdiff
          apply h
          have hdouble := hdiff.neg
          have hdouble_neg :
              -(fun z : ℝ => -iterDeriv n f z) = iterDeriv n f := by
            funext z
            simp
          rw [hdouble_neg] at hdouble
          exact hdouble
        rw [deriv_zero_of_not_differentiableAt hneg,
          deriv_zero_of_not_differentiableAt h, neg_zero]

private theorem iterDeriv_sin_two_formula (n : ℕ) (x : ℝ) :
    iterDeriv n (fun z : ℝ => Real.sin (2 * z)) x =
      (2 : ℝ) ^ n * Real.sin (2 * x + (n : ℝ) / 2 * Real.pi) := by
  induction n generalizing x with
  | zero =>
      simp [iterDeriv]
  | succ n ih =>
      rw [show iterDeriv (Nat.succ n) (fun z : ℝ => Real.sin (2 * z)) x =
          deriv (iterDeriv n (fun z : ℝ => Real.sin (2 * z))) x by
            simp only [iterDeriv, Function.iterate_succ_apply']]
      rw [show iterDeriv n (fun z : ℝ => Real.sin (2 * z)) =
          fun t : ℝ => (2 : ℝ) ^ n *
            Real.sin (2 * t + (n : ℝ) / 2 * Real.pi) by
            funext t
            exact ih t]
      have harg : HasDerivAt
          (fun t : ℝ => 2 * t + (n : ℝ) / 2 * Real.pi) 2 x := by
        convert (((hasDerivAt_id x).const_mul 2).add_const
          ((n : ℝ) / 2 * Real.pi)) using 1 <;> ring
      have hderiv :=
        (((Real.hasDerivAt_sin
          (2 * x + (n : ℝ) / 2 * Real.pi)).comp x harg).const_mul
            ((2 : ℝ) ^ n))
      have hd :
          deriv (fun t : ℝ => (2 : ℝ) ^ n *
            Real.sin (2 * t + (n : ℝ) / 2 * Real.pi)) x =
            (2 : ℝ) ^ n *
              (Real.cos (2 * x + (n : ℝ) / 2 * Real.pi) * 2) := by
        change deriv
          (fun t : ℝ => (2 : ℝ) ^ n *
            (Real.sin ∘ fun u : ℝ => 2 * u + (n : ℝ) / 2 * Real.pi) t) x = _
        exact hderiv.deriv
      rw [hd]
      have hphase :
          Real.sin (2 * x + ((Nat.succ n : ℕ) : ℝ) / 2 * Real.pi) =
            Real.cos (2 * x + (n : ℝ) / 2 * Real.pi) := by
        have harg_eq :
            2 * x + ((Nat.succ n : ℕ) : ℝ) / 2 * Real.pi =
              (2 * x + (n : ℝ) / 2 * Real.pi) + Real.pi / 2 := by
          simp only [Nat.cast_succ]
          ring
        rw [harg_eq, Real.sin_add, Real.sin_pi_div_two,
          Real.cos_pi_div_two]
        ring
      rw [hphase, pow_succ]
      ring

theorem gap1 (x : ℝ) :
    iterDeriv 1 y x = -2 * Real.cos x * Real.sin x := by
  change deriv (Real.cos ^ (2 : ℕ)) x = _
  rw [((Real.hasDerivAt_cos x).pow 2).deriv]
  ring

theorem gap2 (x : ℝ) :
    -2 * Real.cos x * Real.sin x = -Real.sin (2 * x) := by
  rw [Real.sin_two_mul]
  ring

theorem gap3 (x : ℝ) :
    iterDeriv 1 y x = -Real.sin (2 * x) := by
  rw [gap1, gap2]

theorem gap4 (n : ℕ) (x : ℝ) (hn : 1 ≤ n) :
    iterDeriv n y x =
      -iterDeriv (n - 1) (fun z : ℝ => Real.sin (2 * z)) x := by
  have hn' : n - 1 + 1 = n := Nat.sub_add_cancel hn
  calc
    iterDeriv n y x = iterDeriv (n - 1 + 1) y x := by rw [hn']
    _ = iterDeriv (n - 1) (deriv y) x := by
      simp only [iterDeriv, Function.iterate_succ_apply]
    _ = iterDeriv (n - 1) (fun z : ℝ => -Real.sin (2 * z)) x := by
      apply congrArg (fun f : ℝ → ℝ => iterDeriv (n - 1) f x)
      funext z
      simpa [iterDeriv] using gap3 z
    _ = -iterDeriv (n - 1) (fun z : ℝ => Real.sin (2 * z)) x :=
      iterDeriv_neg (n - 1) (fun z : ℝ => Real.sin (2 * z)) x

theorem gap5 (n : ℕ) (x : ℝ) :
    -iterDeriv (n - 1) (fun z : ℝ => Real.sin (2 * z)) x =
      -(2 : ℝ) ^ (n - 1) *
        Real.sin (2 * x + ((n - 1 : ℕ) : ℝ) / 2 * Real.pi) := by
  rw [iterDeriv_sin_two_formula]
  ring

theorem gap6 (n : ℕ) (x : ℝ) (hn : 1 ≤ n) :
    -(2 : ℝ) ^ (n - 1) *
        Real.sin (2 * x + ((n - 1 : ℕ) : ℝ) / 2 * Real.pi) =
      (2 : ℝ) ^ (n - 1) *
        Real.cos (2 * x + (n : ℝ) / 2 * Real.pi) := by
  have hcast : (n : ℝ) = ((n - 1 : ℕ) : ℝ) + 1 := by
    have h := congrArg (fun k : ℕ => (k : ℝ)) (Nat.sub_add_cancel hn)
    simpa only [Nat.cast_add, Nat.cast_one] using h.symm
  have hphase :
      2 * x + (n : ℝ) / 2 * Real.pi =
        (2 * x + ((n - 1 : ℕ) : ℝ) / 2 * Real.pi) + Real.pi / 2 := by
    rw [hcast]
    ring
  rw [hphase, Real.cos_add, Real.cos_pi_div_two, Real.sin_pi_div_two]
  ring

theorem gap7 (n : ℕ) (x : ℝ) (hn : 1 ≤ n) :
    iterDeriv n y x =
      (2 : ℝ) ^ (n - 1) *
        Real.cos (2 * x + (n : ℝ) / 2 * Real.pi) := by
  calc
    iterDeriv n y x =
        -iterDeriv (n - 1) (fun z : ℝ => Real.sin (2 * z)) x := gap4 n x hn
    _ = -(2 : ℝ) ^ (n - 1) *
          Real.sin (2 * x + ((n - 1 : ℕ) : ℝ) / 2 * Real.pi) := gap5 n x
    _ = (2 : ℝ) ^ (n - 1) *
          Real.cos (2 * x + (n : ℝ) / 2 * Real.pi) := gap6 n x hn

end

end ProofGap.Exercise1194
