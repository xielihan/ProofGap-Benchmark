import ProofGapLean.Prelude.Analysis
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.NormNum

open scoped Interval

namespace ProofGap.Exercise2296

noncomputable section

def I (n : ℕ) : ℝ :=
  ∫ x in 0..Real.pi,
    Real.cos x ^ (n + 1) * Real.sin ((n + 1 : ℕ) * x)

def auxiliary (n : ℕ) (x : ℝ) : ℝ :=
  Real.cos x ^ (n - 1) * Real.sin ((n + 1 : ℕ) * x)

def auxiliaryIntegral (n : ℕ) : ℝ :=
  ∫ x in 0..Real.pi, auxiliary n x

def OddFunction (f : ℝ → ℝ) : Prop := ∀ x, f (-x) = -f x

private theorem sin_add_nat_mul_pi_aux (x : ℝ) (k : ℕ) :
    Real.sin (x + (k : ℝ) * Real.pi) =
      (-1 : ℝ) ^ k * Real.sin x := by
  induction k with
  | zero =>
      simp
  | succ k ih =>
      rw [Nat.cast_succ]
      have harg :
          x + ((k : ℝ) + 1) * Real.pi =
            (x + (k : ℝ) * Real.pi) + Real.pi := by
        ring
      rw [harg, Real.sin_add_pi, ih, pow_succ]
      ring

private theorem auxiliary_periodic (n : ℕ) (hn : 0 < n) :
    Function.Periodic (auxiliary n) Real.pi := by
  intro x
  unfold auxiliary
  rw [Real.cos_add_pi]
  have harg :
      ((n + 1 : ℕ) : ℝ) * (x + Real.pi) =
        ((n + 1 : ℕ) : ℝ) * x +
          ((n + 1 : ℕ) : ℝ) * Real.pi := by
    ring
  rw [harg, sin_add_nat_mul_pi_aux]
  have hcos :
      -Real.cos x = (-1 : ℝ) * Real.cos x := by
    ring
  rw [hcos, mul_pow]
  have hsum : n - 1 + (n + 1) = 2 * n := by
    omega
  have hsign :
      (-1 : ℝ) ^ (n - 1) * (-1 : ℝ) ^ (n + 1) = 1 := by
    rw [← pow_add, hsum, pow_mul]
    norm_num
  calc
    _ = ((-1 : ℝ) ^ (n - 1) * (-1 : ℝ) ^ (n + 1)) *
        (Real.cos x ^ (n - 1) *
          Real.sin (((n + 1 : ℕ) : ℝ) * x)) := by
      ring
    _ = _ := by rw [hsign, one_mul]

private theorem auxiliary_odd (n : ℕ) : OddFunction (auxiliary n) := by
  intro x
  unfold auxiliary
  rw [Real.cos_neg]
  have harg :
      ((n + 1 : ℕ) : ℝ) * -x = -(((n + 1 : ℕ) : ℝ) * x) := by
    ring
  rw [harg, Real.sin_neg]
  ring

private theorem integral_eq_zero_of_odd_symmetric
    (f : ℝ → ℝ) (a : ℝ) (hodd : OddFunction f) :
    (∫ x in -a..a, f x) = 0 := by
  have hreflect :
      (∫ x in -a..a, f (-x)) = ∫ x in -a..a, f x := by
    rw [intervalIntegral.integral_comp_neg]
    ring_nf
  change (∀ x : ℝ, f (-x) = -f x) at hodd
  have hfun :
      (fun x : ℝ => f (-x)) = (fun x : ℝ => -f x) := by
    funext x
    exact hodd x
  have hneg :
      (∫ x in -a..a, f (-x)) = -(∫ x in -a..a, f x) := by
    rw [hfun, intervalIntegral.integral_neg]
  exact neg_eq_self.mp (hneg.symm.trans hreflect)

private theorem auxiliary_symmetric_integral_eq_zero (n : ℕ) :
    (∫ x in -Real.pi / 2..Real.pi / 2, auxiliary n x) = 0 := by
  simpa only [neg_div] using
    (integral_eq_zero_of_odd_symmetric
      (auxiliary n) (Real.pi / 2) (auxiliary_odd n))

private theorem shifted_auxiliary_odd (n : ℕ) (hn : 0 < n) :
    OddFunction (fun x => auxiliary n (x + Real.pi / 2)) := by
  intro x
  calc
    auxiliary n (-x + Real.pi / 2) =
        auxiliary n (-(x + Real.pi / 2) + Real.pi) := by
          congr 1
          ring
    _ = auxiliary n (-(x + Real.pi / 2)) := auxiliary_periodic n hn _
    _ = -auxiliary n (x + Real.pi / 2) := auxiliary_odd n _

private theorem shifted_auxiliary_integral (n : ℕ) :
    (∫ x in -Real.pi / 2..Real.pi / 2,
      auxiliary n (x + Real.pi / 2)) = auxiliaryIntegral n := by
  unfold auxiliaryIntegral
  rw [intervalIntegral.integral_comp_add_right]
  ring_nf

private theorem auxiliaryIntegral_eq_zero (n : ℕ) (hn : 0 < n) :
    auxiliaryIntegral n = 0 := by
  rw [← shifted_auxiliary_integral n]
  simpa only [neg_div] using
    (integral_eq_zero_of_odd_symmetric
      (fun x => auxiliary n (x + Real.pi / 2))
      (Real.pi / 2) (shifted_auxiliary_odd n hn))

theorem gap1 (n : ℕ) (hn : 0 < n) :
    I n = I n - (n : ℝ) / (n + 1 : ℝ) * auxiliaryIntegral n := by
  rw [auxiliaryIntegral_eq_zero n hn]
  ring

theorem gap2 (n : ℕ) (hn : 0 < n) :
    auxiliaryIntegral n = 0 := by
  exact auxiliaryIntegral_eq_zero n hn

theorem gap3 (n : ℕ) (hn : 0 < n) :
    Function.Periodic (auxiliary n) Real.pi := by
  exact auxiliary_periodic n hn

theorem gap4 (n : ℕ) (hn : 0 < n) :
    OddFunction (auxiliary n) := by
  exact auxiliary_odd n

theorem gap5 (n : ℕ) (hn : 0 < n) :
    auxiliaryIntegral n =
      ∫ x in -Real.pi / 2..Real.pi / 2, auxiliary n x := by
  rw [auxiliaryIntegral_eq_zero n hn,
    auxiliary_symmetric_integral_eq_zero n]

theorem gap6 (n : ℕ) (hn : 0 < n) :
    (∫ x in -Real.pi / 2..Real.pi / 2, auxiliary n x) = 0 := by
  exact auxiliary_symmetric_integral_eq_zero n

theorem gap7 (n : ℕ) (hn : 0 < n) :
    auxiliaryIntegral n = 0 := by
  exact auxiliaryIntegral_eq_zero n hn

end

end ProofGap.Exercise2296
