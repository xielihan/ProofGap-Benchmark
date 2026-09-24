import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise2966

noncomputable section

open Filter
open scoped BigOperators

def denominator (q x : ℝ) : ℝ :=
  1 - 2 * q * Real.cos x + q ^ 2

def target (q x : ℝ) : ℝ :=
  q * Real.sin x / denominator q x

def epos (x : ℝ) : ℂ :=
  Complex.exp (Complex.I * x)

def eneg (x : ℝ) : ℂ :=
  Complex.exp (-Complex.I * x)

def sineTerm (q x : ℝ) (n : ℕ) : ℝ :=
  q ^ n * Real.sin ((n : ℝ) * x)

def sineSeries (q x : ℝ) : ℝ :=
  ∑' k : ℕ, sineTerm q x (k + 1)

def sinePartial (q : ℝ) (N : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range N, sineTerm q x (k + 1)

private theorem epos_euler (x : ℝ) :
    epos x = (Real.cos x : ℂ) + (Real.sin x : ℂ) * Complex.I := by
  rw [epos]
  convert Complex.exp_ofReal_mul_I x using 1 <;> ring

private theorem eneg_euler (x : ℝ) :
    eneg x = (Real.cos x : ℂ) - (Real.sin x : ℂ) * Complex.I := by
  rw [eneg]
  have harg :
      -Complex.I * (x : ℂ) = ((-x : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [harg, Complex.exp_ofReal_mul_I]
  simp [Real.cos_neg, Real.sin_neg]
  ring

private theorem epos_add_eneg (x : ℝ) :
    epos x + eneg x = 2 * (Real.cos x : ℂ) := by
  rw [epos_euler, eneg_euler]
  ring

private theorem epos_sub_eneg (x : ℝ) :
    epos x - eneg x = 2 * Complex.I * (Real.sin x : ℂ) := by
  rw [epos_euler, eneg_euler]
  ring

private theorem epos_mul_eneg (x : ℝ) : epos x * eneg x = 1 := by
  rw [epos, eneg, ← Complex.exp_add]
  convert Complex.exp_zero using 1 <;> ring

private theorem norm_epos (x : ℝ) : ‖epos x‖ = 1 := by
  simp [epos, Complex.norm_exp]

private theorem norm_eneg (x : ℝ) : ‖eneg x‖ = 1 := by
  simp [eneg, Complex.norm_exp]

private theorem norm_q_mul_epos_lt_one (q x : ℝ) (hq : |q| < 1) :
    ‖(q : ℂ) * epos x‖ < 1 := by
  rw [norm_mul, norm_epos, mul_one]
  simpa using hq

private theorem norm_q_mul_eneg_lt_one (q x : ℝ) (hq : |q| < 1) :
    ‖(q : ℂ) * eneg x‖ < 1 := by
  rw [norm_mul, norm_eneg, mul_one]
  simpa using hq

private theorem one_sub_q_epos_ne_zero (q x : ℝ) (hq : |q| < 1) :
    1 - (q : ℂ) * epos x ≠ 0 := by
  apply sub_ne_zero.mpr
  intro h
  have hn := norm_q_mul_epos_lt_one q x hq
  rw [← h] at hn
  norm_num at hn

private theorem one_sub_q_eneg_ne_zero (q x : ℝ) (hq : |q| < 1) :
    1 - (q : ℂ) * eneg x ≠ 0 := by
  apply sub_ne_zero.mpr
  intro h
  have hn := norm_q_mul_eneg_lt_one q x hq
  rw [← h] at hn
  norm_num at hn

private theorem denominator_factor (q x : ℝ) :
    (1 - (q : ℂ) * epos x) * (1 - (q : ℂ) * eneg x) =
      1 - (q : ℂ) * (epos x + eneg x) + (q : ℂ) ^ 2 := by
  calc
    (1 - (q : ℂ) * epos x) * (1 - (q : ℂ) * eneg x) =
        1 - (q : ℂ) * (epos x + eneg x) +
          (q : ℂ) ^ 2 * (epos x * eneg x) := by ring
    _ = 1 - (q : ℂ) * (epos x + eneg x) + (q : ℂ) ^ 2 := by
      rw [epos_mul_eneg]
      ring

private theorem denominator_complex (q x : ℝ) :
    (denominator q x : ℂ) =
      1 - (q : ℂ) * (epos x + eneg x) + (q : ℂ) ^ 2 := by
  rw [denominator, epos_add_eneg]
  push_cast
  ring

private theorem numerator_complex (q x : ℝ) :
    ((q * Real.sin x : ℝ) : ℂ) =
      ((q : ℂ) / (2 * Complex.I)) * (epos x - eneg x) := by
  rw [epos_sub_eneg]
  push_cast
  field_simp [Complex.I_ne_zero]

private theorem epos_pow (x : ℝ) (n : ℕ) :
    epos x ^ n =
      (Real.cos ((n : ℝ) * x) : ℂ) +
        (Real.sin ((n : ℝ) * x) : ℂ) * Complex.I := by
  rw [epos, ← Complex.exp_nat_mul]
  have harg :
      (n : ℂ) * (Complex.I * (x : ℂ)) =
        (((n : ℝ) * x : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [harg, Complex.exp_ofReal_mul_I]

private theorem eneg_pow (x : ℝ) (n : ℕ) :
    eneg x ^ n =
      (Real.cos ((n : ℝ) * x) : ℂ) -
        (Real.sin ((n : ℝ) * x) : ℂ) * Complex.I := by
  rw [eneg, ← Complex.exp_nat_mul]
  have harg :
      (n : ℂ) * (-Complex.I * (x : ℂ)) =
        ((-((n : ℝ) * x) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [harg, Complex.exp_ofReal_mul_I]
  simp [Real.cos_neg, Real.sin_neg]
  ring

private theorem epos_pow_sub_eneg_pow (x : ℝ) (n : ℕ) :
    epos x ^ n - eneg x ^ n =
      2 * Complex.I * (Real.sin ((n : ℝ) * x) : ℂ) := by
  rw [epos_pow, eneg_pow]
  ring

private theorem sineTerm_complex (q x : ℝ) (n : ℕ) :
    (sineTerm q x n : ℂ) =
      1 / (2 * Complex.I) *
        (((q : ℂ) * epos x) ^ n - ((q : ℂ) * eneg x) ^ n) := by
  rw [sineTerm, mul_pow, mul_pow, ← mul_sub, epos_pow_sub_eneg_pow]
  push_cast
  field_simp [Complex.I_ne_zero]

private theorem sineSeries_complex (q x : ℝ) (hq : |q| < 1) :
    (sineSeries q x : ℂ) =
      1 / (2 * Complex.I) *
        (1 / (1 - (q : ℂ) * epos x) -
          1 / (1 - (q : ℂ) * eneg x)) := by
  have hp := norm_q_mul_epos_lt_one q x hq
  have hn := norm_q_mul_eneg_lt_one q x hq
  have hsp :
      Summable (fun k : ℕ => ((q : ℂ) * epos x) ^ (k + 1)) := by
    simpa only [pow_succ'] using
      (summable_geometric_of_norm_lt_one hp).mul_left ((q : ℂ) * epos x)
  have hsn :
      Summable (fun k : ℕ => ((q : ℂ) * eneg x) ^ (k + 1)) := by
    simpa only [pow_succ'] using
      (summable_geometric_of_norm_lt_one hn).mul_left ((q : ℂ) * eneg x)
  rw [sineSeries, Complex.ofReal_tsum]
  calc
    (∑' k : ℕ, (sineTerm q x (k + 1) : ℂ)) =
        ∑' k : ℕ, 1 / (2 * Complex.I) *
          (((q : ℂ) * epos x) ^ (k + 1) -
            ((q : ℂ) * eneg x) ^ (k + 1)) := by
      apply tsum_congr
      intro k
      exact sineTerm_complex q x (k + 1)
    _ = 1 / (2 * Complex.I) *
        ((∑' k : ℕ, ((q : ℂ) * epos x) ^ (k + 1)) -
          ∑' k : ℕ, ((q : ℂ) * eneg x) ^ (k + 1)) :=
      ((hsp.hasSum.sub hsn.hasSum).mul_left _).tsum_eq
    _ = 1 / (2 * Complex.I) *
        (1 / (1 - (q : ℂ) * epos x) -
          1 / (1 - (q : ℂ) * eneg x)) := by
      rw [geom_series_succ _ hp, geom_series_succ _ hn,
        tsum_geometric_of_norm_lt_one hp, tsum_geometric_of_norm_lt_one hn]
      simp only [div_eq_mul_inv]
      ring

theorem gap1 (q : ℝ) (hq : |q| < 1) :
    ∀ x,
      (target q x : ℂ) =
        (((q : ℂ) / (2 * Complex.I)) * (epos x - eneg x)) /
          (1 - (q : ℂ) * (epos x + eneg x) + (q : ℂ) ^ 2) := by
  intro x
  rw [target, Complex.ofReal_div, numerator_complex, denominator_complex]

theorem gap2 (q : ℝ) (hq : |q| < 1) :
    ∀ x,
      (target q x : ℂ) =
        1 / (2 * Complex.I) *
          ((q : ℂ) * (epos x - eneg x) /
            ((1 - (q : ℂ) * epos x) *
              (1 - (q : ℂ) * eneg x))) := by
  intro x
  rw [gap1 q hq x, ← denominator_factor]
  ring

theorem gap3 (q : ℝ) (hq : |q| < 1) :
    ∀ x,
      1 / (2 * Complex.I) *
          ((q : ℂ) * (epos x - eneg x) /
            ((1 - (q : ℂ) * epos x) *
              (1 - (q : ℂ) * eneg x))) =
        1 / (2 * Complex.I) *
          (1 / (1 - (q : ℂ) * epos x) -
            1 / (1 - (q : ℂ) * eneg x)) := by
  intro x
  field_simp [one_sub_q_epos_ne_zero q x hq,
    one_sub_q_eneg_ne_zero q x hq, Complex.I_ne_zero]
  ring

theorem gap4 (q : ℝ) (hq : |q| < 1) :
    ∀ x,
      (target q x : ℂ) =
        1 / (2 * Complex.I) *
          (1 / (1 - (q : ℂ) * epos x) -
            1 / (1 - (q : ℂ) * eneg x)) := by
  intro x
  exact (gap2 q hq x).trans (gap3 q hq x)

theorem gap5 (q : ℝ) (hq : |q| < 1) :
    ∀ x, target q x = sineSeries q x := by
  intro x
  apply Complex.ofReal_injective
  exact (gap4 q hq x).trans (sineSeries_complex q x hq).symm

theorem gap6 (q : ℝ) (hq : |q| < 1) :
    ∀ n : ℕ, 1 ≤ n → ∀ x : ℝ,
      |sineTerm q x n| ≤ |q| ^ n := by
  intro n hn x
  rw [sineTerm, abs_mul, abs_pow]
  exact mul_le_of_le_one_right (pow_nonneg (abs_nonneg q) n)
    (Real.abs_sin_le_one ((n : ℝ) * x))

theorem gap7 (q : ℝ) (hq : |q| < 1) :
    Summable (fun k : ℕ => q ^ (k + 1)) := by
  simpa only [pow_succ'] using
    (summable_geometric_of_abs_lt_one hq).mul_left q

theorem gap8 (q : ℝ) (hq : |q| < 1) :
    TendstoUniformlyOn
      (sinePartial q) (target q) atTop Set.univ := by
  have hu : Summable (fun k : ℕ => |q| ^ (k + 1)) :=
    gap7 |q| (by simpa only [abs_abs] using hq)
  have hconv :
      TendstoUniformlyOn
        (fun N x => ∑ k ∈ Finset.range N, sineTerm q x (k + 1))
        (fun x => ∑' k : ℕ, sineTerm q x (k + 1)) atTop Set.univ := by
    apply tendstoUniformlyOn_tsum_nat hu
    intro k x hx
    simpa only [Real.norm_eq_abs] using
      gap6 q hq (k + 1) (Nat.succ_le_succ (Nat.zero_le k)) x
  have hseries :
      TendstoUniformlyOn
        (sinePartial q) (sineSeries q) atTop Set.univ := by
    simpa only [sinePartial, sineSeries] using hconv
  exact hseries.congr_right fun x hx => (gap5 q hq x).symm

theorem gap9 (q : ℝ) (hq : |q| < 1) :
    ∀ x, sineSeries q x = target q x := by
  intro x
  exact (gap5 q hq x).symm

end

end ProofGap.Exercise2966
