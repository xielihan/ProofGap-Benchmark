import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open scoped Interval

namespace ProofGap.Exercise2539

noncomputable section

open Finset Filter Set

def integrand (x : ℝ) : ℝ := if x = 0 then 1 else Real.arctan x / x
def mesh (i : ℕ) : ℝ := i / 10
def sample (i : ℕ) : ℝ := integrand (mesh i)
def catalanIntegral : ℝ := ∫ x in (0 : ℝ)..1, integrand x
def roundedSimpson : ℝ :=
  1 / 30 * (1.78540 + 18.32888 + 7.36476)

private def atanPartial (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ range n,
    (-1 : ℝ) ^ k * x ^ (2 * k + 1) / ((2 * k + 1 : ℕ) : ℝ)

private def quotientPartial (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ range n,
    (-1 : ℝ) ^ k * x ^ (2 * k) / ((2 * k + 1 : ℕ) : ℝ)

private def catalanPartial (n : ℕ) : ℝ :=
  ∑ k ∈ range n, (-1 : ℝ) ^ k / (((2 * k + 1 : ℕ) : ℝ) ^ 2)

private theorem arctanTerm_antitone (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Antitone
      (fun n : ℕ => x ^ (2 * n + 1) / ((2 * n + 1 : ℕ) : ℝ)) := by
  intro m n hmn
  have hpow :
      x ^ (2 * n + 1) ≤ x ^ (2 * m + 1) :=
    pow_le_pow_of_le_one hx0 hx1 (by omega)
  have hden :
      ((2 * m + 1 : ℕ) : ℝ) ≤ ((2 * n + 1 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 2 * m + 1 ≤ 2 * n + 1)
  exact div_le_div₀ (pow_nonneg hx0 _) hpow (by positivity) hden

private theorem arctanTerm_summable (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1) :
    Summable
      (fun n : ℕ => x ^ (2 * n + 1) / ((2 * n + 1 : ℕ) : ℝ)) := by
  have hfac : 0 < (1 - x) * (1 + x) :=
    mul_pos (sub_pos.mpr hx1) (by linarith)
  have hsq : ‖x ^ 2‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg x)]
    nlinarith
  have hgeo : Summable (fun n : ℕ => x * (x ^ 2) ^ n) :=
    (summable_geometric_of_norm_lt_one hsq).mul_left x
  refine hgeo.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
  calc
    x ^ (2 * n + 1) / ((2 * n + 1 : ℕ) : ℝ) =
        ((x ^ 2) ^ n * x) / ((2 * n + 1 : ℕ) : ℝ) := by
      rw [pow_succ, ← pow_mul]
    _ ≤ (x ^ 2) ^ n * x :=
      div_le_self (by positivity) (by norm_num)
    _ = x * (x ^ 2) ^ n := by ring

private theorem arctan_error (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1) (n : ℕ) :
    |Real.arctan x - atanPartial n x| ≤
      x ^ (2 * n + 1) / ((2 * n + 1 : ℕ) : ℝ) := by
  have hs := Real.hasSum_arctan (x := x) (by
      rw [Real.norm_eq_abs, abs_of_nonneg hx0]
      exact hx1)
  have hsum := arctanTerm_summable x hx0 hx1
  have hbound :=
    alternating_series_error_bound
      (fun k : ℕ =>
        x ^ (2 * k + 1) / ((2 * k + 1 : ℕ) : ℝ))
      (arctanTerm_antitone x hx0 hx1.le) hsum n
  have htsum :
      (∑' k : ℕ,
          (-1 : ℝ) ^ k *
            (x ^ (2 * k + 1) / ((2 * k + 1 : ℕ) : ℝ))) =
        Real.arctan x := by
    simpa only [mul_div_assoc] using hs.tsum_eq
  rw [htsum] at hbound
  simpa [atanPartial, mul_div_assoc] using hbound

private theorem atanPartial_div (x : ℝ) (hx : x ≠ 0) (n : ℕ) :
    atanPartial n x / x = quotientPartial n x := by
  unfold atanPartial quotientPartial
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k hk
  rw [pow_succ]
  field_simp [hx]

private theorem arctanQuotient_error (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1)
    (n : ℕ) :
    |Real.arctan x / x - quotientPartial n x| ≤
      x ^ (2 * n) / ((2 * n + 1 : ℕ) : ℝ) := by
  have h := arctan_error x hx0.le hx1 n
  calc
    |Real.arctan x / x - quotientPartial n x| =
        |Real.arctan x - atanPartial n x| / x := by
      rw [← atanPartial_div x hx0.ne' n, ← sub_div, abs_div,
        abs_of_pos hx0]
    _ ≤ (x ^ (2 * n + 1) / ((2 * n + 1 : ℕ) : ℝ)) / x :=
      div_le_div_of_nonneg_right h hx0.le
    _ = x ^ (2 * n) / ((2 * n + 1 : ℕ) : ℝ) := by
      rw [pow_succ]
      field_simp [hx0.ne']

private theorem integrand_continuous : Continuous integrand := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x = 0
  · subst x
    have hfun : integrand =
        Function.update
          (fun y : ℝ => (Real.arctan y - Real.arctan 0) / (y - 0)) 0 1 := by
      funext y
      by_cases hy : y = 0
      · subst y
        simp [integrand]
      · simp [integrand, hy, Real.arctan_zero]
    rw [hfun]
    simpa using (Real.hasDerivAt_arctan 0).continuousAt_div
  · have hlocal :
        integrand =ᶠ[nhds x] fun y : ℝ => Real.arctan y / y := by
      filter_upwards [compl_singleton_mem_nhds_iff.mpr hx] with y hy
      have hy0 : y ≠ 0 := by simpa using hy
      simp [integrand, hy0]
    exact
      ((Real.continuous_arctan.continuousAt.div continuousAt_id hx).congr_of_eventuallyEq
        hlocal)

private theorem quotientPartial_continuous (n : ℕ) :
    Continuous (quotientPartial n) := by
  unfold quotientPartial
  fun_prop

private theorem integral_quotientPartial (n : ℕ) :
    (∫ x in (0 : ℝ)..1, quotientPartial n x) = catalanPartial n := by
  unfold quotientPartial catalanPartial
  rw [intervalIntegral.integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro k hk
    calc
      (∫ x in (0 : ℝ)..1,
          (-1 : ℝ) ^ k * x ^ (2 * k) / ((2 * k + 1 : ℕ) : ℝ)) =
          ((-1 : ℝ) ^ k / ((2 * k + 1 : ℕ) : ℝ)) *
            (∫ x in (0 : ℝ)..1, x ^ (2 * k)) := by
        rw [← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        intro x hx
        ring
      _ = (-1 : ℝ) ^ k / (((2 * k + 1 : ℕ) : ℝ) ^ 2) := by
        rw [integral_pow]
        norm_num
        field_simp
  · intro k hk
    exact
      (by
        fun_prop :
        Continuous
          (fun x : ℝ =>
            (-1 : ℝ) ^ k * x ^ (2 * k) /
              ((2 * k + 1 : ℕ) : ℝ))).intervalIntegrable _ _

private theorem integral_remainder (n : ℕ) :
    (∫ x in (0 : ℝ)..1,
      x ^ (2 * n) / ((2 * n + 1 : ℕ) : ℝ)) =
      1 / (((2 * n + 1 : ℕ) : ℝ) ^ 2) := by
  rw [intervalIntegral.integral_div, integral_pow]
  norm_num
  field_simp

private theorem catalan_error (n : ℕ) :
    |catalanIntegral - catalanPartial n| ≤
      1 / (((2 * n + 1 : ℕ) : ℝ) ^ 2) := by
  have hdiff :
      catalanIntegral - catalanPartial n =
        ∫ x in (0 : ℝ)..1, (integrand x - quotientPartial n x) := by
    rw [catalanIntegral, intervalIntegral.integral_sub
      (integrand_continuous.intervalIntegrable 0 1)
      ((quotientPartial_continuous n).intervalIntegrable 0 1),
      integral_quotientPartial n]
  have hbound :
      ‖∫ x in (0 : ℝ)..1, (integrand x - quotientPartial n x)‖ ≤
        ∫ x in (0 : ℝ)..1,
          x ^ (2 * n) / ((2 * n + 1 : ℕ) : ℝ) := by
    apply intervalIntegral.norm_integral_le_of_norm_le (by norm_num)
    · filter_upwards [MeasureTheory.Measure.ae_ne MeasureTheory.volume (1 : ℝ)]
        with x hx hmem
      have hx0 : 0 < x := hmem.1
      have hx1 : x < 1 := lt_of_le_of_ne hmem.2 hx
      simpa [Real.norm_eq_abs, integrand, hx0.ne'] using
        arctanQuotient_error x hx0 hx1 n
    · exact
        (by
          fun_prop :
          Continuous
            (fun x : ℝ =>
              x ^ (2 * n) /
                ((2 * n + 1 : ℕ) : ℝ))).intervalIntegrable _ _
  rw [hdiff, ← Real.norm_eq_abs]
  exact hbound.trans_eq (integral_remainder n)

private theorem sample1_tight :
    |sample 1 - 0.99668652| < 0.00000001 := by
  have h :=
    arctanQuotient_error (1 / 10 : ℝ) (by norm_num) (by norm_num) 4
  rw [abs_le] at h
  rw [abs_lt]
  norm_num [sample, mesh, integrand, quotientPartial,
    Finset.sum_range_succ] at h ⊢
  constructor <;> linarith

private theorem sample2_tight :
    |sample 2 - 0.98697780| < 0.00000001 := by
  have h :=
    arctanQuotient_error (2 / 10 : ℝ) (by norm_num) (by norm_num) 6
  rw [abs_le] at h
  rw [abs_lt]
  norm_num [sample, mesh, integrand, quotientPartial,
    Finset.sum_range_succ] at h ⊢
  constructor <;> linarith

private theorem sample3_tight :
    |sample 3 - 0.97152265| < 0.00000001 := by
  have h :=
    arctanQuotient_error (3 / 10 : ℝ) (by norm_num) (by norm_num) 7
  rw [abs_le] at h
  rw [abs_lt]
  norm_num [sample, mesh, integrand, quotientPartial,
    Finset.sum_range_succ] at h ⊢
  constructor <;> linarith

private theorem sample4_tight :
    |sample 4 - 0.95126594| < 0.00000001 := by
  have h :=
    arctanQuotient_error (4 / 10 : ℝ) (by norm_num) (by norm_num) 9
  rw [abs_le] at h
  rw [abs_lt]
  norm_num [sample, mesh, integrand, quotientPartial,
    Finset.sum_range_succ] at h ⊢
  constructor <;> linarith

private theorem sample5_tight :
    |sample 5 - 0.92729522| < 0.00000001 := by
  have h :=
    arctanQuotient_error (5 / 10 : ℝ) (by norm_num) (by norm_num) 12
  rw [abs_le] at h
  rw [abs_lt]
  norm_num [sample, mesh, integrand, quotientPartial,
    Finset.sum_range_succ] at h ⊢
  constructor <;> linarith

private theorem sample6_tight :
    |sample 6 - 0.90069917| < 0.00000001 := by
  have h :=
    arctanQuotient_error (6 / 10 : ℝ) (by norm_num) (by norm_num) 18
  rw [abs_le] at h
  rw [abs_lt]
  norm_num [sample, mesh, integrand, quotientPartial,
    Finset.sum_range_succ] at h ⊢
  constructor <;> linarith

private theorem sample7_tight :
    |sample 7 - 0.87246566| < 0.00000001 := by
  have h :=
    arctanQuotient_error (7 / 10 : ℝ) (by norm_num) (by norm_num) 25
  rw [abs_le] at h
  rw [abs_lt]
  norm_num [sample, mesh, integrand, quotientPartial,
    Finset.sum_range_succ] at h ⊢
  constructor <;> linarith

private theorem sample8_tight :
    |sample 8 - 0.84342618| < 0.00000001 := by
  have h :=
    arctanQuotient_error (8 / 10 : ℝ) (by norm_num) (by norm_num) 40
  rw [abs_le] at h
  rw [abs_lt]
  norm_num [sample, mesh, integrand, quotientPartial,
    Finset.sum_range_succ] at h ⊢
  constructor <;> linarith

private theorem sample9_tight :
    |sample 9 - 0.81423900| < 0.00000001 := by
  have h :=
    arctanQuotient_error (9 / 10 : ℝ) (by norm_num) (by norm_num) 70
  rw [abs_le] at h
  rw [abs_lt]
  norm_num [sample, mesh, integrand, quotientPartial,
    Finset.sum_range_succ] at h ⊢
  constructor <;> linarith

private theorem sample10_tight :
    |sample 10 - 0.78539816| < 0.00000001 := by
  have hpLower := Real.pi_gt_d20
  have hpUpper := Real.pi_lt_d20
  rw [abs_lt]
  norm_num [sample, mesh, integrand, Real.arctan_one] at hpLower hpUpper ⊢
  constructor <;> linarith

set_option maxHeartbeats 800000 in
set_option maxRecDepth 10000 in
private theorem catalan_tight :
    |catalanIntegral - 0.91596794| < 0.00000467 := by
  have h := catalan_error 231
  rw [abs_le] at h
  rw [abs_lt]
  norm_num [catalanPartial, Finset.sum_range_succ] at h ⊢
  constructor <;> linarith

private theorem simpson_tight :
    |1 / 30 * (sample 0 + sample 10 +
        4 * (sample 1 + sample 3 + sample 5 + sample 7 + sample 9) +
        2 * (sample 2 + sample 4 + sample 6 + sample 8)) -
      (1373948627 / 1500000000 : ℝ)| < 0.00000001 := by
  have h0 : sample 0 = 1 := by
    norm_num [sample, mesh, integrand]
  have h1 := sample1_tight
  have h2 := sample2_tight
  have h3 := sample3_tight
  have h4 := sample4_tight
  have h5 := sample5_tight
  have h6 := sample6_tight
  have h7 := sample7_tight
  have h8 := sample8_tight
  have h9 := sample9_tight
  have h10 := sample10_tight
  rw [abs_lt] at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 ⊢
  constructor <;>
    norm_num at * <;>
    linarith

theorem gap1 (G : ℝ) (hG : G = catalanIntegral) :
    G = ∫ x in (0 : ℝ)..1, integrand x := by
  simpa [catalanIntegral] using hG
theorem gap2 : mesh 0 = 0 := by norm_num [mesh]
theorem gap3 : sample 0 = 1 := by norm_num [sample, mesh, integrand]
theorem gap4 : mesh 1 = 0.1 := by norm_num [mesh]
theorem gap5 : |sample 1 - 0.99669| < 0.00001 := by
  have ht := sample1_tight
  rw [abs_lt] at ht ⊢
  constructor <;> linarith [ht.1, ht.2]
theorem gap6 : mesh 2 = 0.2 := by norm_num [mesh]
theorem gap7 : |sample 2 - 0.98698| < 0.00001 := by
  have ht := sample2_tight
  rw [abs_lt] at ht ⊢
  constructor <;> linarith [ht.1, ht.2]
theorem gap8 : mesh 3 = 0.3 := by norm_num [mesh]
theorem gap9 : |sample 3 - 0.97152| < 0.00001 := by
  have ht := sample3_tight
  rw [abs_lt] at ht ⊢
  constructor <;> linarith [ht.1, ht.2]
theorem gap10 : mesh 4 = 0.4 := by norm_num [mesh]
theorem gap11 : |sample 4 - 0.95127| < 0.00001 := by
  have ht := sample4_tight
  rw [abs_lt] at ht ⊢
  constructor <;> linarith [ht.1, ht.2]
theorem gap12 : mesh 5 = 0.5 := by norm_num [mesh]
theorem gap13 : |sample 5 - 0.92730| < 0.00001 := by
  have ht := sample5_tight
  rw [abs_lt] at ht ⊢
  constructor <;> linarith [ht.1, ht.2]
theorem gap14 : mesh 6 = 0.6 := by norm_num [mesh]
theorem gap15 : |sample 6 - 0.90070| < 0.00001 := by
  have ht := sample6_tight
  rw [abs_lt] at ht ⊢
  constructor <;> linarith [ht.1, ht.2]
theorem gap16 : mesh 7 = 0.7 := by norm_num [mesh]
theorem gap17 : |sample 7 - 0.87247| < 0.00001 := by
  have ht := sample7_tight
  rw [abs_lt] at ht ⊢
  constructor <;> linarith [ht.1, ht.2]
theorem gap18 : mesh 8 = 0.8 := by norm_num [mesh]
theorem gap19 : |sample 8 - 0.84343| < 0.00001 := by
  have ht := sample8_tight
  rw [abs_lt] at ht ⊢
  constructor <;> linarith [ht.1, ht.2]
theorem gap20 : mesh 9 = 0.9 := by norm_num [mesh]
theorem gap21 : |sample 9 - 0.81424| < 0.00001 := by
  have ht := sample9_tight
  rw [abs_lt] at ht ⊢
  constructor <;> linarith [ht.1, ht.2]
theorem gap22 : mesh 10 = 1 := by norm_num [mesh]
theorem gap23 : |sample 10 - 0.78540| < 0.00001 := by
  have ht := sample10_tight
  rw [abs_lt] at ht ⊢
  constructor <;> linarith [ht.1, ht.2]

theorem gap24 :
    |catalanIntegral -
      1 / 30 * (sample 0 + sample 10 +
        4 * (sample 1 + sample 3 + sample 5 + sample 7 + sample 9) +
        2 * (sample 2 + sample 4 + sample 6 + sample 8))| <
      0.00001 := by
  have hc := catalan_tight
  have hs := simpson_tight
  rw [abs_lt] at hc hs ⊢
  constructor <;>
    norm_num at * <;>
    linarith

theorem gap25 :
    |catalanIntegral - roundedSimpson| < 0.00002 := by
  have hc := catalan_tight
  rw [abs_lt] at hc ⊢
  norm_num [roundedSimpson] at *
  constructor <;> linarith

theorem gap26 : |roundedSimpson - 0.91597| < 0.00001 := by
  norm_num [roundedSimpson, abs_lt]

theorem gap27 : |catalanIntegral - 0.91597| < 0.00001 := by
  have hc := catalan_tight
  rw [abs_lt] at hc ⊢
  norm_num at *
  constructor <;> linarith

end

end ProofGap.Exercise2539
