import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1202

noncomputable section

def iterDeriv (n : ℕ) (f : ℝ → ℝ) : ℝ → ℝ :=
  (deriv^[n]) f

def y (a x : ℝ) : ℝ :=
  x * Real.cos (a * x)

def cosAffine (a : ℝ) : ℝ → ℝ :=
  fun x => Real.cos (a * x)

def phaseForm (a : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  a ^ n * x * Real.cos (a * x + (n : ℝ) / 2 * Real.pi) +
    (n : ℝ) * a ^ (n - 1) *
      Real.cos (a * x + ((n - 1 : ℕ) : ℝ) / 2 * Real.pi)

private theorem cosAffine_iterDeriv_spec (a : ℝ) (n : ℕ) (x : ℝ) :
    iterDeriv n (cosAffine a) x =
        a ^ n * Real.cos (a * x + (n : ℝ) / 2 * Real.pi) ∧
      HasDerivAt (iterDeriv n (cosAffine a))
        (iterDeriv (n + 1) (cosAffine a) x) x := by
  have hphaseDeriv (m : ℕ) (z : ℝ) :
      HasDerivAt
        (fun t : ℝ =>
          a ^ m * Real.cos (a * t + (m : ℝ) / 2 * Real.pi))
        (a ^ (m + 1) *
          Real.cos (a * z + ((m + 1 : ℕ) : ℝ) / 2 * Real.pi)) z := by
    have hinner :
        HasDerivAt
          (fun t : ℝ => a * t + (m : ℝ) / 2 * Real.pi) a z := by
      simpa using
        (((hasDerivAt_id z).const_mul a).add_const
          ((m : ℝ) / 2 * Real.pi))
    have hd :
        HasDerivAt
          (fun t : ℝ =>
            a ^ m * Real.cos (a * t + (m : ℝ) / 2 * Real.pi))
          (a ^ m *
            (-Real.sin (a * z + (m : ℝ) / 2 * Real.pi) * a)) z := by
      simpa using
        (((Real.hasDerivAt_cos
            (a * z + (m : ℝ) / 2 * Real.pi)).comp z hinner).const_mul
          (a ^ m))
    have hangle :
        a * z + ((m + 1 : ℕ) : ℝ) / 2 * Real.pi =
          (a * z + (m : ℝ) / 2 * Real.pi) + Real.pi / 2 := by
      simp only [Nat.cast_add, Nat.cast_one]
      ring
    convert hd using 1
    rw [pow_succ, hangle, Real.cos_add, Real.cos_pi_div_two,
      Real.sin_pi_div_two]
    ring
  have hformula : ∀ (m : ℕ) (z : ℝ),
      iterDeriv m (cosAffine a) z =
        a ^ m * Real.cos (a * z + (m : ℝ) / 2 * Real.pi) := by
    intro m
    induction m with
    | zero =>
        intro z
        simp [iterDeriv, cosAffine]
    | succ m ih =>
        intro z
        have hfun :
            iterDeriv m (cosAffine a) =
              fun t : ℝ =>
                a ^ m * Real.cos (a * t + (m : ℝ) / 2 * Real.pi) := by
          funext t
          exact ih t
        calc
          iterDeriv m.succ (cosAffine a) z =
              deriv (iterDeriv m (cosAffine a)) z := by
                simp [iterDeriv, Function.iterate_succ_apply',
                  Nat.succ_eq_add_one]
          _ = deriv
                (fun t : ℝ =>
                  a ^ m * Real.cos
                    (a * t + (m : ℝ) / 2 * Real.pi)) z := by
                rw [hfun]
          _ = a ^ m.succ *
                Real.cos
                  (a * z + (m.succ : ℝ) / 2 * Real.pi) := by
                simpa [Nat.succ_eq_add_one] using (hphaseDeriv m z).deriv
  constructor
  · exact hformula n x
  · have hfun :
        iterDeriv n (cosAffine a) =
          fun t : ℝ =>
            a ^ n * Real.cos (a * t + (n : ℝ) / 2 * Real.pi) := by
      funext t
      exact hformula n t
    rw [hfun, hformula (n + 1) x]
    exact hphaseDeriv n x

theorem gap1 (a : ℝ) (n : ℕ) (x : ℝ) :
    iterDeriv n (y a) x =
      x * iterDeriv n (cosAffine a) x +
        (n : ℝ) * iterDeriv (n - 1) (cosAffine a) x := by
  induction n generalizing x with
  | zero =>
      simp [iterDeriv, y, cosAffine]
  | succ n ih =>
      have hfun :
          iterDeriv n (y a) =
            fun z : ℝ =>
              z * iterDeriv n (cosAffine a) z +
                (n : ℝ) * iterDeriv (n - 1) (cosAffine a) z := by
        funext z
        exact ih z
      have hcalc :
          deriv
              (fun z : ℝ =>
                z * iterDeriv n (cosAffine a) z +
                  (n : ℝ) * iterDeriv (n - 1) (cosAffine a) z) x =
            iterDeriv n (cosAffine a) x +
                x * iterDeriv (n + 1) (cosAffine a) x +
              (n : ℝ) * iterDeriv ((n - 1) + 1) (cosAffine a) x := by
        simpa using
          ((((hasDerivAt_id x).mul
                (cosAffine_iterDeriv_spec a n x).2).add
              ((cosAffine_iterDeriv_spec a (n - 1) x).2.const_mul
                (n : ℝ))).deriv)
      calc
        iterDeriv n.succ (y a) x =
            deriv (iterDeriv n (y a)) x := by
              simp [iterDeriv, Function.iterate_succ_apply',
                Nat.succ_eq_add_one]
        _ = deriv
              (fun z : ℝ =>
                z * iterDeriv n (cosAffine a) z +
                  (n : ℝ) * iterDeriv (n - 1) (cosAffine a) z) x := by
              rw [hfun]
        _ = iterDeriv n (cosAffine a) x +
                x * iterDeriv (n + 1) (cosAffine a) x +
              (n : ℝ) * iterDeriv ((n - 1) + 1) (cosAffine a) x := hcalc
        _ = x * iterDeriv n.succ (cosAffine a) x +
              (n.succ : ℝ) * iterDeriv (n.succ - 1) (cosAffine a) x := by
              cases n <;>
                simp [Nat.cast_succ, Nat.succ_eq_add_one] <;> ring

theorem gap2 (a : ℝ) (n : ℕ) (x : ℝ) :
    x * iterDeriv n (cosAffine a) x +
        (n : ℝ) * iterDeriv (n - 1) (cosAffine a) x =
      phaseForm a n x := by
  unfold phaseForm
  rw [(cosAffine_iterDeriv_spec a n x).1,
    (cosAffine_iterDeriv_spec a (n - 1) x).1]
  ring

theorem gap3 (a : ℝ) (n : ℕ) (x : ℝ) :
    iterDeriv n (y a) x = phaseForm a n x := by
  exact (gap1 a n x).trans (gap2 a n x)

theorem gap4 (a : ℝ) (n : ℕ) (x : ℝ) :
    iterDeriv n (y a) x =
      a ^ n * x * Real.cos (a * x + (n : ℝ) / 2 * Real.pi) +
        (n : ℝ) * a ^ (n - 1) *
          Real.sin (a * x + (n : ℝ) / 2 * Real.pi) := by
  rw [gap3]
  cases n with
  | zero =>
      simp [phaseForm]
  | succ n =>
      have hangle :
          a * x + (n.succ : ℝ) / 2 * Real.pi =
            (a * x + (n : ℝ) / 2 * Real.pi) + Real.pi / 2 := by
        simp only [Nat.cast_succ]
        ring
      have htrig :
          Real.sin (a * x + (n.succ : ℝ) / 2 * Real.pi) =
            Real.cos (a * x + (n : ℝ) / 2 * Real.pi) := by
        rw [hangle, Real.sin_add, Real.sin_pi_div_two,
          Real.cos_pi_div_two]
        ring
      simp only [phaseForm, Nat.succ_sub_one]
      rw [htrig]

end

end ProofGap.Exercise1202
