import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow

namespace ProofGap.Exercise4203

noncomputable section

open MeasureTheory
open scoped Interval

def primitive (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..t, f s

def iteratedProductIntegral (f : ℝ → ℝ) : ℕ → ℝ → ℝ
  | 0, _ => 1
  | n + 1, t =>
      ∫ s in (0 : ℝ)..t, f s * iteratedProductIntegral f n s

private theorem iteratedProductIntegral_closedForm
    (f : ℝ → ℝ) (hf : Continuous f) :
    ∀ n t, iteratedProductIntegral f n t =
      (primitive f t) ^ n / (Nat.factorial n : ℝ) := by
  have hprim : ∀ x : ℝ, HasDerivAt (primitive f) (f x) x := by
    intro x
    simpa [primitive] using
      (intervalIntegral.integral_hasDerivAt_right
        (hf.intervalIntegrable (0 : ℝ) x)
        hf.stronglyMeasurable.stronglyMeasurableAtFilter
        hf.continuousAt)
  have hprim_cont : Continuous (primitive f) :=
    continuous_iff_continuousAt.mpr (fun x => (hprim x).continuousAt)
  intro n
  induction n with
  | zero =>
      intro t
      simp [iteratedProductIntegral]
  | succ n ih =>
      intro t
      rw [iteratedProductIntegral]
      simp_rw [ih]
      have hder : ∀ x : ℝ,
          HasDerivAt
            (fun y => primitive f y ^ (n + 1) /
              (Nat.factorial (n + 1) : ℝ))
            (f x * (primitive f x ^ n /
              (Nat.factorial n : ℝ))) x := by
        intro x
        convert (((hprim x).pow (n + 1)).mul_const
          (1 / (Nat.factorial (n + 1) : ℝ))) using 1 <;>
          field_simp [Nat.factorial_succ] <;>
          try ring
        · funext y
          simp only [Pi.pow_apply]
          rw [Nat.add_comm 1 n, pow_succ]
          ring
        · rw [Nat.add_comm 1 n]
          simp only [Nat.add_sub_cancel, Nat.factorial_succ,
            Nat.cast_mul, Nat.cast_add, Nat.cast_one]
          ring
      have hint : IntervalIntegrable
          (fun x => f x * (primitive f x ^ n /
            (Nat.factorial n : ℝ))) MeasureTheory.volume 0 t := by
        apply Continuous.intervalIntegrable
        exact hf.mul
          ((hprim_cont.pow n).div_const
            (Nat.factorial n : ℝ))
      calc
        (∫ x in (0 : ℝ)..t,
            f x * (primitive f x ^ n /
              (Nat.factorial n : ℝ))) =
            (primitive f t) ^ (n + 1) /
                (Nat.factorial (n + 1) : ℝ) -
              (primitive f 0) ^ (n + 1) /
                (Nat.factorial (n + 1) : ℝ) := by
          exact intervalIntegral.integral_eq_sub_of_hasDerivAt
            (fun x hx => hder x) hint
        _ = (primitive f t) ^ (n + 1) /
            (Nat.factorial (n + 1) : ℝ) := by
          simp [primitive]

theorem gap1 (f : ℝ → ℝ) (n : ℕ) (t : ℝ) :
    iteratedProductIntegral f (n + 1) t =
      ∫ s in (0 : ℝ)..t, f s * iteratedProductIntegral f n s := by
  rfl

theorem gap2 (f : ℝ → ℝ) (hf : Continuous f) (t : ℝ) :
    HasDerivAt (primitive f) (f t) t := by
  simpa [primitive] using
    (intervalIntegral.integral_hasDerivAt_right
      (hf.intervalIntegrable (0 : ℝ) t)
      hf.stronglyMeasurable.stronglyMeasurableAtFilter
      hf.continuousAt)

theorem gap3 (f : ℝ → ℝ) :
    primitive f 0 = 0 := by
  simp [primitive]

theorem gap4 (f : ℝ → ℝ) (hf : Continuous f) (t : ℝ) :
    iteratedProductIntegral f 2 t =
      ∫ s in (0 : ℝ)..t, primitive f s * f s := by
  simp [iteratedProductIntegral, primitive, mul_comm]

theorem gap5 (f : ℝ → ℝ) (hf : Continuous f) (t : ℝ) :
    iteratedProductIntegral f 2 t =
      (1 / 2 : ℝ) * (primitive f t) ^ 2 := by
  rw [iteratedProductIntegral_closedForm f hf 2 t]
  norm_num
  ring

theorem gap6
    (f : ℝ → ℝ) (hf : Continuous f) (n : ℕ) (hn : 1 ≤ n) (t : ℝ) :
    iteratedProductIntegral f (n - 1) t =
      (primitive f t) ^ (n - 1) /
        (Nat.factorial (n - 1) : ℝ) := by
  exact iteratedProductIntegral_closedForm f hf (n - 1) t

theorem gap7
    (f : ℝ → ℝ) (n : ℕ) (hn : 1 ≤ n)
    (hInd : ∀ t,
      iteratedProductIntegral f (n - 1) t =
        (primitive f t) ^ (n - 1) /
          (Nat.factorial (n - 1) : ℝ))
    (t : ℝ) :
    iteratedProductIntegral f n t =
      ∫ s in (0 : ℝ)..t,
        (primitive f s) ^ (n - 1) /
          (Nat.factorial (n - 1) : ℝ) * f s := by
  cases n with
  | zero => simp at hn
  | succ k =>
      simp only [Nat.succ_sub_one] at hInd ⊢
      rw [iteratedProductIntegral]
      apply intervalIntegral.integral_congr
      intro x hx
      change f x * iteratedProductIntegral f k x =
        primitive f x ^ k / (Nat.factorial k : ℝ) * f x
      rw [hInd x]
      ring

theorem gap8
    (f : ℝ → ℝ) (hf : Continuous f) (n : ℕ) (hn : 1 ≤ n)
    (t : ℝ) :
    (∫ s in (0 : ℝ)..t,
        (primitive f s) ^ (n - 1) /
          (Nat.factorial (n - 1) : ℝ) * f s) =
      (primitive f t) ^ n / (Nat.factorial n : ℝ) := by
  cases n with
  | zero => simp at hn
  | succ k =>
      simp only [Nat.succ_sub_one]
      rw [← iteratedProductIntegral_closedForm f hf (Nat.succ k) t]
      rw [iteratedProductIntegral]
      apply intervalIntegral.integral_congr
      intro x hx
      change primitive f x ^ k / (Nat.factorial k : ℝ) * f x =
        f x * iteratedProductIntegral f k x
      rw [iteratedProductIntegral_closedForm f hf k x]
      ring

theorem gap9
    (f : ℝ → ℝ) (hf : Continuous f) (n : ℕ) (t : ℝ) :
    iteratedProductIntegral f n t =
      (primitive f t) ^ n / (Nat.factorial n : ℝ) := by
  exact iteratedProductIntegral_closedForm f hf n t

theorem gap10
    (f : ℝ → ℝ) (hf : Continuous f) (n : ℕ) (t : ℝ) :
    iteratedProductIntegral f n t =
      (1 / (Nat.factorial n : ℝ)) *
        (∫ s in (0 : ℝ)..t, f s) ^ n := by
  rw [iteratedProductIntegral_closedForm f hf n t]
  simp [primitive, div_eq_mul_inv, mul_comm]

end

end ProofGap.Exercise4203
