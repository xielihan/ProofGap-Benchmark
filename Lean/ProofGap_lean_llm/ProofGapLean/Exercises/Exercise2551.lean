import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise2551

noncomputable section

def point (q α : ℝ) : ℂ :=
  (q : ℂ) * (Real.cos α + Complex.I * Real.sin α)
def sinSeries (q α : ℝ) : ℝ :=
  ∑' n : ℕ, q ^ n * Real.sin (n * α)
def sinSeriesOne (q α : ℝ) : ℝ :=
  ∑' n : ℕ, q ^ (n + 1) * Real.sin ((n + 1) * α)
def cosSeries (q α : ℝ) : ℝ :=
  ∑' n : ℕ, q ^ n * Real.cos (n * α)
def cosSeriesOne (q α : ℝ) : ℝ :=
  ∑' n : ℕ, q ^ (n + 1) * Real.cos ((n + 1) * α)
def denominator (q α : ℝ) : ℝ :=
  1 - 2 * q * Real.cos α + q ^ 2

private theorem point_pow_formula (q α : ℝ) (n : ℕ) :
    point q α ^ n =
      ((q ^ n * Real.cos (n * α) : ℝ) : ℂ) +
        Complex.I * ((q ^ n * Real.sin (n * α) : ℝ) : ℂ) := by
  induction n with
  | zero => simp [point]
  | succ n ih =>
      rw [pow_succ, ih]
      apply Complex.ext <;>
        simp [point, Nat.cast_succ, add_mul, Real.cos_add,
          Real.sin_add, pow_succ] <;>
        ring

private theorem denominator_pos (q α : ℝ) (hq : |q| < 1) :
    0 < denominator q α := by
  have hc : q * Real.cos α ≤ |q| := by
    calc
      q * Real.cos α ≤ |q * Real.cos α| := le_abs_self _
      _ = |q| * |Real.cos α| := abs_mul _ _
      _ ≤ |q| * 1 :=
        mul_le_mul_of_nonneg_left (Real.abs_cos_le_one α) (abs_nonneg q)
      _ = |q| := mul_one _
  have hdiff : 0 < 1 - |q| := sub_pos.mpr hq
  have hs : 0 < (1 - |q|) ^ 2 := by
    nlinarith
  have hsq : |q| ^ 2 = q ^ 2 := sq_abs q
  unfold denominator
  nlinarith

private theorem denominator_eq_sq_add_sq (q α : ℝ) :
    denominator q α =
      (1 - q * Real.cos α) ^ 2 + (q * Real.sin α) ^ 2 := by
  unfold denominator
  nlinarith [Real.sin_sq_add_cos_sq α]

private theorem complex_div_ofReal (a b d : ℝ) (hd : d ≠ 0) :
    ((a : ℂ) + Complex.I * (b : ℂ)) / (d : ℂ) =
      ((a / d : ℝ) : ℂ) + Complex.I * ((b / d : ℝ) : ℂ) := by
  have hdc : (d : ℂ) ≠ 0 := by
    intro h
    apply hd
    simpa using congrArg Complex.re h
  apply (div_eq_iff hdc).2
  apply Complex.ext <;> simp [hd]

theorem gap1 : Complex.I ^ 2 = -1 := by
  norm_num [pow_two, Complex.I_mul_I]
theorem gap2 (q α : ℝ) : ‖point q α‖ = |q| := by
  have hunit :
      ‖(Real.cos α : ℂ) + Complex.I * (Real.sin α : ℂ)‖ = 1 := by
    rw [Complex.norm_def, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, zero_mul, mul_zero, one_mul,
      zero_add, add_zero, sub_zero]
    rw [show Real.cos α * Real.cos α + Real.sin α * Real.sin α = 1 by
      nlinarith [Real.sin_sq_add_cos_sq α]]
    norm_num
  calc
    ‖point q α‖ = ‖(q : ℂ)‖ *
        ‖(Real.cos α : ℂ) + Complex.I * (Real.sin α : ℂ)‖ := by
      rw [point, norm_mul]
    _ = |q| := by
      rw [hunit, mul_one]
      simp [Real.norm_eq_abs]
theorem gap3 (q : ℝ) (hq : |q| < 1) : |q| < 1 := by
  exact hq
theorem gap4 (q α : ℝ) (hq : |q| < 1) :
    ‖point q α‖ < 1 := by
  rw [gap2 q α]
  exact hq
theorem gap5 (q α : ℝ) (hq : |q| < 1) :
    (∑' n : ℕ, point q α ^ n) =
      (cosSeries q α : ℂ) + Complex.I * sinSeries q α := by
  have hp : Summable (fun n : ℕ => point q α ^ n) :=
    summable_geometric_of_norm_lt_one (gap4 q α hq)
  apply Complex.ext
  · simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, zero_mul,
      mul_zero, one_mul, add_zero, sub_zero]
    calc
      (∑' n : ℕ, point q α ^ n).re =
          ∑' n : ℕ, (point q α ^ n).re := by
        exact Complex.reCLM.map_tsum hp
      _ = cosSeries q α := by
        unfold cosSeries
        apply tsum_congr
        intro n
        have hn := congrArg Complex.re (point_pow_formula q α n)
        simpa only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
          Complex.ofReal_im, Complex.I_re, Complex.I_im, zero_mul,
          mul_zero, one_mul, add_zero, sub_zero] using hn
  · simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, zero_mul,
      mul_zero, one_mul, zero_add, add_zero]
    calc
      (∑' n : ℕ, point q α ^ n).im =
          ∑' n : ℕ, (point q α ^ n).im := by
        exact Complex.imCLM.map_tsum hp
      _ = sinSeries q α := by
        unfold sinSeries
        apply tsum_congr
        intro n
        have hn := congrArg Complex.im (point_pow_formula q α n)
        simpa only [Complex.add_im, Complex.mul_im, Complex.ofReal_re,
          Complex.ofReal_im, Complex.I_re, Complex.I_im, zero_mul,
          mul_zero, one_mul, zero_add, add_zero] using hn
theorem gap6 (q α : ℝ) (hq : |q| < 1) :
    (∑' n : ℕ, point q α ^ n) = 1 / (1 - point q α) := by
  simpa [div_eq_mul_inv] using
    (hasSum_geometric_of_norm_lt_one (gap4 q α hq)).tsum_eq
theorem gap7 (q α : ℝ) :
    1 / (1 - point q α) =
      1 / ((1 - q * Real.cos α : ℝ) - Complex.I * (q * Real.sin α)) := by
  apply congrArg (fun z : ℂ => 1 / z)
  apply Complex.ext <;> simp [point] <;> ring
theorem gap8 (q α : ℝ) (hq : |q| < 1) :
    1 / ((1 - q * Real.cos α : ℝ) - Complex.I * (q * Real.sin α)) =
      ((1 - q * Real.cos α : ℝ) + Complex.I * (q * Real.sin α)) /
        denominator q α := by
  have hd : denominator q α ≠ 0 :=
    ne_of_gt (denominator_pos q α hq)
  have hdc : (denominator q α : ℂ) ≠ 0 := by
    intro h
    apply hd
    simpa using congrArg Complex.re h
  have hprod :
      (((1 - q * Real.cos α : ℝ) : ℂ) -
          Complex.I * ((q * Real.sin α : ℝ) : ℂ)) *
        (((1 - q * Real.cos α : ℝ) : ℂ) +
          Complex.I * ((q * Real.sin α : ℝ) : ℂ)) =
        (denominator q α : ℂ) := by
    rw [denominator_eq_sq_add_sq]
    apply Complex.ext <;>
      simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re,
        Complex.sub_im, Complex.add_re, Complex.add_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
        Complex.I_im, zero_mul, mul_zero, one_mul, zero_add,
        add_zero, sub_zero, zero_sub] <;>
      ring
  have hz :
      (((1 - q * Real.cos α : ℝ) : ℂ) -
          Complex.I * ((q * Real.sin α : ℝ) : ℂ)) ≠ 0 := by
    intro hz
    apply hdc
    rw [← hprod, hz, zero_mul]
  have hmul : ((q * Real.sin α : ℝ) : ℂ) =
      (q : ℂ) * (Real.sin α : ℂ) := by
    apply Complex.ext <;>
      simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, mul_zero, zero_add, add_zero,
        sub_zero]
  simp only [hmul] at hprod hz
  apply (eq_div_iff hdc).2
  rw [← hprod, one_div, ← mul_assoc, inv_mul_cancel₀ hz, one_mul]
theorem gap9 (q α : ℝ) (hq : |q| < 1) :
    (∑' n : ℕ, point q α ^ n) =
      ((1 - q * Real.cos α : ℝ) + Complex.I * (q * Real.sin α)) /
        denominator q α := by
  calc
    (∑' n : ℕ, point q α ^ n) = 1 / (1 - point q α) :=
      gap6 q α hq
    _ = 1 / ((1 - q * Real.cos α : ℝ) -
        Complex.I * (q * Real.sin α)) := gap7 q α
    _ = ((1 - q * Real.cos α : ℝ) +
          Complex.I * (q * Real.sin α)) /
        denominator q α := gap8 q α hq
theorem gap10 (q α : ℝ) (hq : |q| < 1) :
    sinSeriesOne q α = sinSeries q α := by
  have hp : Summable (fun n : ℕ => point q α ^ n) :=
    summable_geometric_of_norm_lt_one (gap4 q α hq)
  have hi0 : Summable (fun n : ℕ => (point q α ^ n).im) := by
    simpa only [Function.comp_apply] using
      (hp.map Complex.imCLM Complex.imCLM.continuous)
  have hi : Summable (fun n : ℕ => q ^ n * Real.sin (n * α)) := by
    simpa only [point_pow_formula, Complex.add_im, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, zero_mul, mul_zero, one_mul, zero_add,
      add_zero] using hi0
  have ht := hi.sum_add_tsum_nat_add 1
  simpa [sinSeries, sinSeriesOne, Nat.add_comm, Nat.add_left_comm,
    Nat.add_assoc] using ht
theorem gap11 (q α : ℝ) (hq : |q| < 1) :
    sinSeries q α = q * Real.sin α / denominator q α := by
  have hd : denominator q α ≠ 0 :=
    ne_of_gt (denominator_pos q α hq)
  have hs := (gap5 q α hq).symm.trans (gap9 q α hq)
  have hs' :
      (cosSeries q α : ℂ) + Complex.I * (sinSeries q α : ℂ) =
        (((1 - q * Real.cos α) / denominator q α : ℝ) : ℂ) +
          Complex.I * (((q * Real.sin α) / denominator q α : ℝ) : ℂ) := by
    calc
      (cosSeries q α : ℂ) + Complex.I * (sinSeries q α : ℂ) =
          (((1 - q * Real.cos α : ℝ) : ℂ) +
            Complex.I * ((q * Real.sin α : ℝ) : ℂ)) /
              (denominator q α : ℂ) := by simpa using hs
      _ = (((1 - q * Real.cos α) / denominator q α : ℝ) : ℂ) +
          Complex.I * (((q * Real.sin α) / denominator q α : ℝ) : ℂ) :=
        complex_div_ofReal (1 - q * Real.cos α)
          (q * Real.sin α) (denominator q α) hd
  have h := congrArg Complex.im hs'
  simpa only [Complex.add_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, zero_mul, mul_zero,
    one_mul, zero_add, add_zero] using h
theorem gap12 (q α : ℝ) (hq : |q| < 1) :
    sinSeriesOne q α = q * Real.sin α / denominator q α := by
  rw [gap10 q α hq, gap11 q α hq]
theorem gap13 (q α : ℝ) (hq : |q| < 1) :
    cosSeriesOne q α = cosSeries q α - 1 := by
  have hp : Summable (fun n : ℕ => point q α ^ n) :=
    summable_geometric_of_norm_lt_one (gap4 q α hq)
  have hr0 : Summable (fun n : ℕ => (point q α ^ n).re) := by
    simpa only [Function.comp_apply] using
      (hp.map Complex.reCLM Complex.reCLM.continuous)
  have hr : Summable (fun n : ℕ => q ^ n * Real.cos (n * α)) := by
    simpa only [point_pow_formula, Complex.add_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, zero_mul, mul_zero, one_mul, add_zero,
      sub_zero] using hr0
  have ht := hr.sum_add_tsum_nat_add 1
  have heq : 1 + cosSeriesOne q α = cosSeries q α := by
    simpa [cosSeries, cosSeriesOne, Nat.add_comm, Nat.add_left_comm,
      Nat.add_assoc] using ht
  linarith
theorem gap14 (q α : ℝ) (hq : |q| < 1) :
    cosSeries q α - 1 =
      (1 - q * Real.cos α) / denominator q α - 1 := by
  have hd : denominator q α ≠ 0 :=
    ne_of_gt (denominator_pos q α hq)
  have hs := (gap5 q α hq).symm.trans (gap9 q α hq)
  have hs' :
      (cosSeries q α : ℂ) + Complex.I * (sinSeries q α : ℂ) =
        ((1 - q * Real.cos α) / denominator q α : ℝ) +
          Complex.I * ((q * Real.sin α / denominator q α : ℝ) : ℂ) := by
    calc
      (cosSeries q α : ℂ) + Complex.I * (sinSeries q α : ℂ) =
          (((1 - q * Real.cos α : ℝ) : ℂ) +
            Complex.I * ((q * Real.sin α : ℝ) : ℂ)) /
              (denominator q α : ℂ) := by simpa using hs
      _ = ((1 - q * Real.cos α) / denominator q α : ℝ) +
          Complex.I * ((q * Real.sin α / denominator q α : ℝ) : ℂ) := by
        rw [complex_div_ofReal (1 - q * Real.cos α)
          (q * Real.sin α) (denominator q α) hd]
  have h := congrArg Complex.re hs'
  have hc :
      cosSeries q α = (1 - q * Real.cos α) / denominator q α := by
    simpa only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, zero_mul, mul_zero,
      one_mul, add_zero, sub_zero] using h
  rw [hc]
theorem gap15 (q α : ℝ) (hq : |q| < 1) :
    (1 - q * Real.cos α) / denominator q α - 1 =
      (q * Real.cos α - q ^ 2) / denominator q α := by
  have hd : denominator q α ≠ 0 :=
    ne_of_gt (denominator_pos q α hq)
  have hnum :
      (1 - q * Real.cos α) - denominator q α =
        q * Real.cos α - q ^ 2 := by
    unfold denominator
    ring
  calc
    (1 - q * Real.cos α) / denominator q α - 1 =
        (1 - q * Real.cos α) / denominator q α -
          denominator q α / denominator q α := by
      rw [div_self hd]
    _ = ((1 - q * Real.cos α) - denominator q α) /
          denominator q α := by
      ring
    _ = (q * Real.cos α - q ^ 2) / denominator q α := by
      rw [hnum]
theorem gap16 (q α : ℝ) (hq : |q| < 1) :
    cosSeriesOne q α =
      (q * Real.cos α - q ^ 2) / denominator q α := by
  rw [gap13 q α hq, gap14 q α hq, gap15 q α hq]

end

end ProofGap.Exercise2551
