import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Algebra.InfiniteSum.Order

namespace ProofGap.Exercise2932_2

noncomputable section

open scoped BigOperators Interval

def integrand (x : ℝ) : ℝ :=
  Real.exp (1 / x)

def exponentialTerm (n : ℕ) (x : ℝ) : ℝ :=
  1 / ((Nat.factorial n : ℝ) * x ^ n)

def integratedTailTerm (k : ℕ) : ℝ :=
  let n := k + 2
  ((1 / (2 : ℝ) ^ (n - 1)) - (1 / (4 : ℝ) ^ (n - 1))) /
    (((n - 1 : ℕ) : ℝ) * (Nat.factorial n : ℝ))

def targetIntegral : ℝ :=
  ∫ x in (2 : ℝ)..4, integrand x

def Approx (u v ε : ℝ) : Prop :=
  |u - v| < ε

private theorem exponentialTerm_hasSum (x : ℝ) :
    HasSum (fun n : ℕ => exponentialTerm n x) (integrand x) := by
  have h := NormedSpace.expSeries_div_hasSum_exp (1 / x : ℝ)
  rw [← Real.exp_eq_exp_ℝ] at h
  apply h.congr
  intro n
  unfold exponentialTerm
  field_simp
  ring

private theorem exponentialTerm_nonneg (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ exponentialTerm n x := by
  unfold exponentialTerm
  positivity

private theorem exponentialTerm_intervalIntegrable (n : ℕ) :
    IntervalIntegrable (exponentialTerm n) MeasureTheory.volume (2 : ℝ) 4 := by
  apply ContinuousOn.intervalIntegrable
  unfold exponentialTerm
  apply ContinuousOn.div continuousOn_const
    (continuousOn_const.mul (continuousOn_id.pow n))
  intro x hx
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) hx.1
  exact mul_ne_zero (by positivity) (pow_ne_zero n hxpos.ne')

private theorem integral_exponentialTerm_zero :
    (∫ x in (2 : ℝ)..4, exponentialTerm 0 x) = 2 := by
  norm_num [exponentialTerm, integral_one]

private theorem integral_exponentialTerm_one :
    (∫ x in (2 : ℝ)..4, exponentialTerm 1 x) = Real.log 2 := by
  simp only [exponentialTerm, Nat.factorial_one, Nat.cast_one, one_mul, pow_one]
  rw [integral_one_div_of_pos (by norm_num) (by norm_num)]
  norm_num [Real.log_div, Real.log_pow]

private theorem integral_exponentialTerm_tail (k : ℕ) :
    (∫ x in (2 : ℝ)..4, exponentialTerm (k + 2) x) =
      integratedTailTerm k := by
  have hz := integral_zpow
    (a := (2 : ℝ)) (b := 4) (n := -((k + 2 : ℕ) : ℤ))
    (Or.inr ⟨by omega, by norm_num [Set.mem_uIcc]⟩)
  have hexp :
      -((k + 2 : ℕ) : ℤ) + 1 = -((k + 1 : ℕ) : ℤ) := by
    omega
  rw [hexp] at hz
  simp only [zpow_neg, zpow_natCast] at hz
  have heq :
      exponentialTerm (k + 2) =
        fun x : ℝ =>
          (1 / (Nat.factorial (k + 2) : ℝ)) * (x ^ (k + 2))⁻¹ := by
    funext x
    unfold exponentialTerm
    ring
  calc
    (∫ x in (2 : ℝ)..4, exponentialTerm (k + 2) x) =
        (1 / (Nat.factorial (k + 2) : ℝ)) *
          ∫ x in (2 : ℝ)..4, (x ^ (k + 2))⁻¹ := by
            rw [heq, intervalIntegral.integral_const_mul]
    _ = integratedTailTerm k := by
      rw [hz]
      simp only [integratedTailTerm]
      dsimp
      norm_num
      rw [show (-2 : ℝ) + -(k : ℝ) + 1 = -((k : ℝ) + 1) by ring]
      field_simp [show (Nat.factorial (k + 2) : ℝ) ≠ 0 by positivity,
        show (k : ℝ) + 1 ≠ 0 by positivity]
      ring

private def tailMajorant (k : ℕ) : ℝ :=
  2 * (1 / 2 : ℝ) ^ (k + 2) / (Nat.factorial (k + 2) : ℝ)

private theorem integratedTailTerm_nonneg (k : ℕ) :
    0 ≤ integratedTailTerm k := by
  simp only [integratedTailTerm]
  dsimp
  apply div_nonneg
  · apply sub_nonneg.mpr
    have hpow :
        (2 : ℝ) ^ (k + 1) ≤ (4 : ℝ) ^ (k + 1) := by
      gcongr
      norm_num
    exact one_div_le_one_div_of_le (by positivity) hpow
  · positivity

private theorem integratedTailTerm_le_majorant (k : ℕ) :
    integratedTailTerm k ≤ tailMajorant k := by
  have hnum :
      (1 / (2 : ℝ) ^ (k + 1)) - (1 / (4 : ℝ) ^ (k + 1)) ≤
        1 / (2 : ℝ) ^ (k + 1) := by
    exact sub_le_self _ (by positivity)
  have hden :
      (Nat.factorial (k + 2) : ℝ) ≤
        ((k + 1 : ℕ) : ℝ) * (Nat.factorial (k + 2) : ℝ) := by
    have hk : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by norm_num
    nlinarith [show (0 : ℝ) < (Nat.factorial (k + 2) : ℝ) by positivity]
  calc
    integratedTailTerm k ≤
        (1 / (2 : ℝ) ^ (k + 1)) /
          (Nat.factorial (k + 2) : ℝ) := by
      simp only [integratedTailTerm]
      dsimp
      exact div_le_div₀ (by positivity) hnum
        (by positivity) hden
    _ = tailMajorant k := by
      unfold tailMajorant
      rw [← one_div_pow]
      rw [show k + 2 = (k + 1) + 1 by omega, pow_succ]
      ring

private theorem summable_tailMajorant : Summable tailMajorant := by
  have hinj : Function.Injective (fun k : ℕ => k + 2) := by
    intro a b h
    exact Nat.add_right_cancel h
  have hs :
      Summable (fun k : ℕ =>
        (1 / 2 : ℝ) ^ (k + 2) / (Nat.factorial (k + 2) : ℝ)) := by
    simpa [Function.comp_def] using
      (Real.summable_pow_div_factorial (1 / 2 : ℝ)).comp_injective hinj
  apply (Summable.mul_left 2 hs).congr
  intro k
  unfold tailMajorant
  ring

private theorem summable_integratedTailTerm : Summable integratedTailTerm :=
  Summable.of_nonneg_of_le integratedTailTerm_nonneg
    integratedTailTerm_le_majorant summable_tailMajorant

private theorem integral_norm_exponentialTerm (n : ℕ) :
    (∫ x in (2 : ℝ)..4, ‖exponentialTerm n x‖) =
      ∫ x in (2 : ℝ)..4, exponentialTerm n x := by
  apply intervalIntegral.integral_congr
  intro x hx
  rw [Set.uIcc_of_le (by norm_num : (2 : ℝ) ≤ 4)] at hx
  change |exponentialTerm n x| = exponentialTerm n x
  rw [abs_of_nonneg]
  exact exponentialTerm_nonneg n (by nlinarith [hx.1])

private theorem summable_integral_exponentialTerm :
    Summable (fun n : ℕ => ∫ x in (2 : ℝ)..4, exponentialTerm n x) := by
  apply (summable_nat_add_iff 2).mp
  apply summable_integratedTailTerm.congr
  intro k
  exact (integral_exponentialTerm_tail k).symm

private theorem summable_integral_norm_exponentialTerm :
    Summable (fun n : ℕ => ∫ x in (2 : ℝ)..4, ‖exponentialTerm n x‖) := by
  apply summable_integral_exponentialTerm.congr
  intro n
  exact (integral_norm_exponentialTerm n).symm

private theorem intervalIntegral_tsum_exponentialTerm :
    (∫ x in (2 : ℝ)..4, ∑' n : ℕ, exponentialTerm n x) =
      ∑' n : ℕ, ∫ x in (2 : ℝ)..4, exponentialTerm n x := by
  have hint (n : ℕ) :
      MeasureTheory.IntegrableOn (exponentialTerm n) (Set.Ioc (2 : ℝ) 4) :=
    (exponentialTerm_intervalIntegrable n).1
  have hnorm :
      Summable (fun n : ℕ =>
        ∫ x in Set.Ioc (2 : ℝ) 4, ‖exponentialTerm n x‖) := by
    simpa only [intervalIntegral.integral_of_le (by norm_num : (2 : ℝ) ≤ 4)] using
      summable_integral_norm_exponentialTerm
  rw [intervalIntegral.integral_of_le (by norm_num : (2 : ℝ) ≤ 4)]
  rw [← MeasureTheory.integral_tsum_of_summable_integral_norm hint hnorm]
  apply tsum_congr
  intro n
  exact (intervalIntegral.integral_of_le
    (μ := MeasureTheory.volume) (f := exponentialTerm n)
    (by norm_num : (2 : ℝ) ≤ 4)).symm

private theorem tsum_tailMajorant_add_three_le :
    (∑' k : ℕ, tailMajorant (k + 3)) ≤ (1 / 1600 : ℝ) := by
  let f : ℕ → ℝ :=
    fun n => (1 / 2 : ℝ) ^ n / (Nat.factorial n : ℝ)
  have hf : HasSum f (Real.exp (1 / 2 : ℝ)) := by
    have h := NormedSpace.expSeries_div_hasSum_exp (1 / 2 : ℝ)
    rw [← Real.exp_eq_exp_ℝ] at h
    simpa [f] using h
  have hsplit := hf.summable.sum_add_tsum_nat_add 5
  rw [hf.tsum_eq] at hsplit
  have htail :
      (∑' k : ℕ, tailMajorant (k + 3)) =
        2 * ∑' k : ℕ, f (k + 5) := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro k
    unfold tailMajorant f
    rw [show k + 3 + 2 = k + 5 by omega]
    ring
  have hfinite :
      (∑ n ∈ Finset.range 5, f n) = (211 / 128 : ℝ) := by
    norm_num [f, Finset.sum_range_succ, Nat.factorial]
  rw [hfinite] at hsplit
  have hsum :
      (∑' k : ℕ, f (k + 5)) =
        Real.exp (1 / 2 : ℝ) - 211 / 128 := by
    linarith
  have hbound := Real.exp_bound
    (x := (1 / 2 : ℝ)) (n := 5) (by norm_num) (by omega)
  norm_num [Finset.sum_range_succ, Nat.factorial] at hbound
  rw [htail, hsum]
  nlinarith [abs_le.mp hbound |>.1, abs_le.mp hbound |>.2]

private theorem integratedTail_tsum_bounds :
    (∑ k ∈ Finset.range 3, integratedTailTerm k) ≤
        ∑' k : ℕ, integratedTailTerm k ∧
      (∑' k : ℕ, integratedTailTerm k) < (1428 / 10000 : ℝ) := by
  have hsplit := summable_integratedTailTerm.sum_add_tsum_nat_add 3
  have htail_nonneg :
      0 ≤ ∑' k : ℕ, integratedTailTerm (k + 3) :=
    tsum_nonneg (fun k => integratedTailTerm_nonneg (k + 3))
  have hinj : Function.Injective (fun k : ℕ => k + 3) := by
    intro a b h
    exact Nat.add_right_cancel h
  have ha : Summable (fun k : ℕ => integratedTailTerm (k + 3)) :=
    summable_integratedTailTerm.comp_injective hinj
  have hb : Summable (fun k : ℕ => tailMajorant (k + 3)) :=
    summable_tailMajorant.comp_injective hinj
  have htail_le :
      (∑' k : ℕ, integratedTailTerm (k + 3)) ≤
        ∑' k : ℕ, tailMajorant (k + 3) :=
    ha.tsum_le_tsum
      (fun k => integratedTailTerm_le_majorant (k + 3)) hb
  have hmajor := tsum_tailMajorant_add_three_le
  have hfinite :
      (∑ k ∈ Finset.range 3, integratedTailTerm k) =
        (655 / 4608 : ℝ) := by
    norm_num [integratedTailTerm, Finset.sum_range_succ, Nat.factorial]
  rw [hfinite] at hsplit
  constructor
  · rw [hfinite]
    linarith
  · linarith

theorem gap1 :
    targetIntegral =
      ∫ x in (2 : ℝ)..4, ∑' n : ℕ, exponentialTerm n x := by
  apply intervalIntegral.integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x _
  exact (exponentialTerm_hasSum x).tsum_eq.symm

theorem gap2 :
    targetIntegral =
      2 + Real.log 2 + ∑' k : ℕ, integratedTailTerm k := by
  rw [gap1, intervalIntegral_tsum_exponentialTerm]
  have hsplit := summable_integral_exponentialTerm.sum_add_tsum_nat_add 2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at hsplit
  rw [integral_exponentialTerm_zero, integral_exponentialTerm_one] at hsplit
  have htail :
      (∑' k : ℕ, ∫ x in (2 : ℝ)..4, exponentialTerm (k + 2) x) =
        ∑' k : ℕ, integratedTailTerm k := by
    apply tsum_congr
    intro k
    exact integral_exponentialTerm_tail k
  rw [htail] at hsplit
  linarith

theorem gap3 :
    Approx targetIntegral (28352 / 10000 : ℝ)
      (1 / 1000 : ℝ) := by
  rw [Approx, gap2, abs_lt]
  rcases integratedTail_tsum_bounds with ⟨htail_lo, htail_hi⟩
  have hfinite :
      (∑ k ∈ Finset.range 3, integratedTailTerm k) =
        (655 / 4608 : ℝ) := by
    norm_num [integratedTailTerm, Finset.sum_range_succ, Nat.factorial]
  rw [hfinite] at htail_lo
  constructor <;>
    nlinarith [Real.log_two_gt_d9, Real.log_two_lt_d9]

theorem gap4 :
    Approx targetIntegral (2835 / 1000 : ℝ)
      (1 / 1000 : ℝ) := by
  rw [Approx, gap2, abs_lt]
  rcases integratedTail_tsum_bounds with ⟨htail_lo, htail_hi⟩
  have hfinite :
      (∑ k ∈ Finset.range 3, integratedTailTerm k) =
        (655 / 4608 : ℝ) := by
    norm_num [integratedTailTerm, Finset.sum_range_succ, Nat.factorial]
  rw [hfinite] at htail_lo
  constructor <;>
    nlinarith [Real.log_two_gt_d9, Real.log_two_lt_d9]

end

end ProofGap.Exercise2932_2
