import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp

namespace ProofGap.Exercise1203

noncomputable section

def iterDeriv (n : ℕ) (f : ℝ → ℝ) : ℝ → ℝ :=
  (deriv^[n]) f

def y (a x : ℝ) : ℝ :=
  x ^ 2 * Real.sin (a * x)

private def wave (a : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  a ^ n * Real.sin (a * x + (n : ℝ) / 2 * Real.pi)

private def rhs (a : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  x ^ 2 * wave a n x +
    (2 * (n : ℝ)) * (x * wave a (n - 1) x) +
    ((n : ℝ) * ((n - 1 : ℕ) : ℝ)) * wave a (n - 2) x

private theorem hasDerivAt_wave (a : ℝ) (n : ℕ) (x : ℝ) :
    HasDerivAt (wave a n) (wave a (n + 1) x) x := by
  have hlin :
      HasDerivAt
        (fun t : ℝ => a * t + (n : ℝ) / 2 * Real.pi) a x := by
    simpa using
      (((hasDerivAt_id x).const_mul a).add_const
        ((n : ℝ) / 2 * Real.pi))
  have h :=
    ((Real.hasDerivAt_sin
        (a * x + (n : ℝ) / 2 * Real.pi)).comp x hlin).const_mul
      (a ^ n)
  have hphase :
      a * x + ((n + 1 : ℕ) : ℝ) / 2 * Real.pi =
        (a * x + (n : ℝ) / 2 * Real.pi) + Real.pi / 2 := by
    norm_num [Nat.cast_succ] <;> ring
  have hder :
      a ^ n *
          (Real.cos (a * x + (n : ℝ) / 2 * Real.pi) * a) =
        wave a (n + 1) x := by
    rw [wave, hphase, Real.sin_add]
    simp [pow_succ]
    ring
  rw [← hder]
  simpa only [wave] using h

private theorem hasDerivAt_rhs (a : ℝ) (n : ℕ) (x : ℝ) :
    HasDerivAt (rhs a n) (rhs a (n + 1) x) x := by
  cases n with
  | zero =>
      have h :=
        ((hasDerivAt_id x).pow 2).mul (hasDerivAt_wave a 0 x)
      convert h using 1
      · funext t
        simp [rhs]
      · simp [rhs] <;> ring_nf
  | succ n =>
      cases n with
      | zero =>
          have h1 :=
            ((hasDerivAt_id x).pow 2).mul (hasDerivAt_wave a 1 x)
          have h2 :=
            ((hasDerivAt_id x).mul (hasDerivAt_wave a 0 x)).const_mul
              (2 : ℝ)
          have h := h1.add h2
          convert h using 1
          · funext t
            simp [rhs] <;> ring_nf
          · simp [rhs] <;> ring_nf
      | succ k =>
          have h1 :=
            ((hasDerivAt_id x).pow 2).mul
              (hasDerivAt_wave a (Nat.succ (Nat.succ k)) x)
          have h2 :=
            ((hasDerivAt_id x).mul
                (hasDerivAt_wave a (Nat.succ k) x)).const_mul
              (2 * ((Nat.succ (Nat.succ k) : ℕ) : ℝ))
          have h3 :=
            (hasDerivAt_wave a k x).const_mul
              (((Nat.succ (Nat.succ k) : ℕ) : ℝ) *
                ((Nat.succ k : ℕ) : ℝ))
          have h := (h1.add h2).add h3
          convert h using 1
          simp [rhs] <;> ring_nf

private theorem iterDeriv_y_eq_rhs (a : ℝ) (n : ℕ) (x : ℝ) :
    iterDeriv n (y a) x = rhs a n x := by
  induction n generalizing x with
  | zero =>
      simp [iterDeriv, y, rhs, wave]
  | succ n ih =>
      have hfun : iterDeriv n (y a) = rhs a n := by
        funext t
        exact ih t
      calc
        iterDeriv (n + 1) (y a) x =
            deriv (iterDeriv n (y a)) x := by
              simp only [iterDeriv, Function.iterate_succ_apply']
        _ = deriv (rhs a n) x := by rw [hfun]
        _ = rhs a (n + 1) x := (hasDerivAt_rhs a n x).deriv

theorem gap1 (a : ℝ) (n : ℕ) (x : ℝ) :
    iterDeriv n (y a) x =
      a ^ n * x ^ 2 *
          Real.sin (a * x + (n : ℝ) / 2 * Real.pi) +
        2 * (n : ℝ) * a ^ (n - 1) * x *
          Real.sin (a * x + ((n - 1 : ℕ) : ℝ) / 2 * Real.pi) +
        (n : ℝ) * ((n - 1 : ℕ) : ℝ) * a ^ (n - 2) *
          Real.sin (a * x + ((n - 2 : ℕ) : ℝ) / 2 * Real.pi) := by
  rw [iterDeriv_y_eq_rhs]
  simp only [rhs, wave]
  ring

theorem gap2 (a : ℝ) (n : ℕ) (x : ℝ) (ha : a ≠ 0) :
    iterDeriv n (y a) x =
      a ^ n * (x ^ 2 - (n : ℝ) * ((n - 1 : ℕ) : ℝ) / a ^ 2) *
          Real.sin (a * x + (n : ℝ) / 2 * Real.pi) -
        2 * (n : ℝ) * a ^ (n - 1) * x *
          Real.cos (a * x + (n : ℝ) / 2 * Real.pi) := by
  cases n with
  | zero =>
      simp [iterDeriv, y]
  | succ n =>
      cases n with
      | zero =>
          rw [gap1]
          simp only [Nat.succ_sub_succ_eq_sub, Nat.sub_zero]
          have hmid :
              Real.sin
                  (a * x + (0 : ℝ) / 2 * Real.pi) =
                -Real.cos
                  (a * x + ((Nat.succ 0 : ℕ) : ℝ) / 2 * Real.pi) := by
            have hp :
                a * x + (0 : ℝ) / 2 * Real.pi =
                  (a * x + ((Nat.succ 0 : ℕ) : ℝ) / 2 * Real.pi) -
                    Real.pi / 2 := by
              norm_num [Nat.cast_succ] <;> ring
            rw [hp]
            simp [Real.sin_sub]
          norm_num [Nat.cast_succ] at hmid ⊢
          rw [hmid]
          ring
      | succ k =>
          rw [gap1]
          simp only [Nat.succ_sub_succ_eq_sub, Nat.sub_zero]
          have hmid :
              Real.sin
                  (a * x + ((Nat.succ k : ℕ) : ℝ) / 2 * Real.pi) =
                -Real.cos
                  (a * x +
                    ((Nat.succ (Nat.succ k) : ℕ) : ℝ) / 2 * Real.pi) := by
            have hp :
                a * x + ((Nat.succ k : ℕ) : ℝ) / 2 * Real.pi =
                  (a * x +
                      ((Nat.succ (Nat.succ k) : ℕ) : ℝ) / 2 *
                        Real.pi) -
                    Real.pi / 2 := by
              norm_num [Nat.cast_succ] <;> ring
            rw [hp]
            simp [Real.sin_sub]
          have hthird :
              Real.sin (a * x + (k : ℝ) / 2 * Real.pi) =
                -Real.sin
                  (a * x +
                    ((Nat.succ (Nat.succ k) : ℕ) : ℝ) / 2 * Real.pi) := by
            have hp :
                a * x + (k : ℝ) / 2 * Real.pi =
                  (a * x +
                      ((Nat.succ (Nat.succ k) : ℕ) : ℝ) / 2 *
                        Real.pi) -
                    Real.pi := by
              norm_num [Nat.cast_succ] <;> ring
            rw [hp]
            simp [Real.sin_sub]
          rw [hmid, hthird]
          field_simp [ha, pow_succ] <;> ring

end

end ProofGap.Exercise1203
