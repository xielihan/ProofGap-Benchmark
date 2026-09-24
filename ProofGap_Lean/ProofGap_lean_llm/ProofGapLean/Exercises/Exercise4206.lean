import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega

namespace ProofGap.Exercise4206

noncomputable section

open MeasureTheory
open scoped Interval

def orderedProductIntegral (f : ℝ → ℝ) : ℕ → ℝ → ℝ
  | 0, _ => 1
  | n + 1, t =>
      ∫ x in (0 : ℝ)..t, f x * orderedProductIntegral f n x

def reductionCoefficient (n : ℕ) : ℝ :=
  ∏ k ∈ Finset.range (n - 1), (1 / (2 * (k + 1) : ℝ))

def evenFactorProduct (n : ℕ) : ℝ :=
  ∏ k ∈ Finset.range n, (2 * (k + 1) : ℝ)

private theorem hasDerivAt_pow_succ (m : ℕ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => y ^ (m + 1))
      (((m + 1 : ℕ) : ℝ) * x ^ m) x := by
  induction m with
  | zero =>
      simpa [id_eq] using (hasDerivAt_id x)
  | succ m ih =>
      convert ih.mul (hasDerivAt_id x) using 1 <;>
        simp [Nat.succ_eq_add_one, pow_succ] <;> ring

private theorem integral_pow (m : ℕ) (a b : ℝ) :
    (∫ x in a..b, x ^ m) =
      (b ^ (m + 1) - a ^ (m + 1)) / (((m + 1 : ℕ) : ℝ)) := by
  have hm : (((m + 1 : ℕ) : ℝ)) ≠ 0 := by
    positivity
  calc
    (∫ x in a..b, x ^ m) =
        (1 / (((m + 1 : ℕ) : ℝ))) * b ^ (m + 1) -
          (1 / (((m + 1 : ℕ) : ℝ))) * a ^ (m + 1) := by
      apply intervalIntegral.integral_deriv_eq_sub'
      · funext x
        calc
          deriv (fun y : ℝ =>
              (1 / (((m + 1 : ℕ) : ℝ))) * y ^ (m + 1)) x =
              (1 / (((m + 1 : ℕ) : ℝ))) *
                ((((m + 1 : ℕ) : ℝ)) * x ^ m) := by
            exact
              ((hasDerivAt_pow_succ m x).const_mul
                (1 / (((m + 1 : ℕ) : ℝ)))).deriv
          _ = x ^ m := by
            field_simp [hm]
      · intro x hx
        exact
          ((hasDerivAt_pow_succ m x).const_mul
            (1 / (((m + 1 : ℕ) : ℝ)))).differentiableAt
      · simpa only [id_eq] using
          ((continuous_id : Continuous (fun y : ℝ => y)).pow m).continuousOn
    _ = (b ^ (m + 1) - a ^ (m + 1)) /
          (((m + 1 : ℕ) : ℝ)) := by
      ring

private theorem evenFactorProduct_eq (n : ℕ) :
    evenFactorProduct n =
      (2 : ℝ) ^ n * (Nat.factorial n : ℝ) := by
  induction n with
  | zero => simp [evenFactorProduct]
  | succ n ih =>
      unfold evenFactorProduct at ih ⊢
      rw [Finset.prod_range_succ, ih]
      norm_num [Nat.factorial_succ, pow_succ] <;> ring

private theorem reductionCoefficient_succ (n : ℕ) :
    reductionCoefficient (Nat.succ n) =
      1 / evenFactorProduct n := by
  simp only [reductionCoefficient, evenFactorProduct, Nat.succ_sub_one]
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.prod_range_succ, Finset.prod_range_succ, ih]
      have hprod :
          (∏ k ∈ Finset.range n, (2 * (k + 1) : ℝ)) ≠ 0 := by
        positivity
      have hfactor : (2 * ((n : ℝ) + 1)) ≠ 0 := by
        positivity
      field_simp [hprod, hfactor] <;> ring

private theorem orderedProductIntegral_id_closed (n : ℕ) (t : ℝ) :
    orderedProductIntegral id n t =
      t ^ (2 * n) /
        ((2 : ℝ) ^ n * (Nat.factorial n : ℝ)) := by
  induction n generalizing t with
  | zero =>
      simp [orderedProductIntegral]
  | succ n ih =>
      simp only [orderedProductIntegral]
      simp_rw [ih]
      have hfun :
          (fun x : ℝ =>
            id x *
              (x ^ (2 * n) /
                ((2 : ℝ) ^ n * (Nat.factorial n : ℝ)))) =
            (fun x : ℝ =>
              (1 / ((2 : ℝ) ^ n * (Nat.factorial n : ℝ))) *
                x ^ (2 * n + 1)) := by
        funext x
        simp only [id_eq, div_eq_mul_inv]
        rw [show 2 * n + 1 = Nat.succ (2 * n) by omega, pow_succ]
        ring
      rw [hfun, intervalIntegral.integral_const_mul, integral_pow]
      have he : 2 * n + 1 + 1 = 2 * Nat.succ n := by omega
      rw [he]
      simp only [zero_pow (by omega : 2 * Nat.succ n ≠ 0), sub_zero]
      have hdeneq :
          (2 : ℝ) ^ Nat.succ n * (Nat.factorial (Nat.succ n) : ℝ) =
            ((2 : ℝ) ^ n * (Nat.factorial n : ℝ)) *
              (((2 * n + 1 : ℕ) : ℝ) + 1) := by
        norm_num [Nat.factorial_succ, pow_succ] <;> ring
      rw [hdeneq]
      have hA :
          (2 : ℝ) ^ n * (Nat.factorial n : ℝ) ≠ 0 := by
        positivity
      have hq : (((2 * n + 1 : ℕ) : ℝ) + 1) ≠ 0 := by
        positivity
      field_simp [hA, hq] <;> norm_num <;> ring_nf <;> simp

theorem gap1 (c t : ℝ) :
    (∫ x in (0 : ℝ)..t, c * t * x) =
      (1 / 2 : ℝ) * c * t ^ 3 := by
  have hfun :
      (fun x : ℝ => c * t * x) =
        (fun x : ℝ => (c * t) * x ^ 1) := by
    funext x
    simp
  rw [hfun, intervalIntegral.integral_const_mul, integral_pow]
  norm_num <;> ring

theorem gap2 (n : ℕ) (hn : 1 ≤ n) :
    orderedProductIntegral id n 1 =
      reductionCoefficient n *
        ∫ x in (0 : ℝ)..1, x ^ (2 * n - 1) := by
  cases n with
  | zero => omega
  | succ m =>
      have hexp : 2 * Nat.succ m - 1 = 2 * m + 1 := by omega
      have hint :
          (∫ x in (0 : ℝ)..1, x ^ (2 * m + 1)) =
            1 / (((2 * m + 1 : ℕ) : ℝ) + 1) := by
        rw [integral_pow]
        norm_num
      rw [orderedProductIntegral_id_closed,
        reductionCoefficient_succ, evenFactorProduct_eq, hexp, hint]
      simp only [one_pow]
      have hdeneq :
          (2 : ℝ) ^ Nat.succ m * (Nat.factorial (Nat.succ m) : ℝ) =
            ((2 : ℝ) ^ m * (Nat.factorial m : ℝ)) *
              (((2 * m + 1 : ℕ) : ℝ) + 1) := by
        norm_num [Nat.factorial_succ, pow_succ] <;> ring
      rw [hdeneq]
      have hA :
          (2 : ℝ) ^ m * (Nat.factorial m : ℝ) ≠ 0 := by
        positivity
      have hq : (((2 * m + 1 : ℕ) : ℝ) + 1) ≠ 0 := by
        positivity
      field_simp [hA, hq] <;> ring

theorem gap3 (n : ℕ) (hn : 1 ≤ n) :
    orderedProductIntegral id n 1 =
      1 / evenFactorProduct n := by
  simpa [evenFactorProduct_eq] using
    (orderedProductIntegral_id_closed n 1)

theorem gap4 (n : ℕ) :
    orderedProductIntegral id n 1 =
      1 / ((2 : ℝ) ^ n * (Nat.factorial n : ℝ)) := by
  simpa using (orderedProductIntegral_id_closed n 1)

end

end ProofGap.Exercise4206
