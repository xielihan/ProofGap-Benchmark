import ProofGapLean.Prelude.Analysis
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.PSeries

namespace ProofGap.Exercise2904

noncomputable section

open scoped BigOperators Interval

def arctangentQuotientTerm (t : ℝ) (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n * t ^ (2 * n) / (2 * n + 1 : ℝ)

def integratedArctangentTerm (x : ℝ) (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n * x ^ (2 * n + 1) / (2 * n + 1 : ℝ) ^ 2

private theorem arctangentQuotientTerm_hasSum
    {t : ℝ} (ht0 : t ≠ 0) (ht1 : |t| < 1) :
    HasSum (arctangentQuotientTerm t) (Real.arctan t / t) := by
  have h :=
    (Real.hasSum_arctan (by simpa [Real.norm_eq_abs] using ht1)).div_const t
  convert h using 1
  funext n
  unfold arctangentQuotientTerm
  rw [show 2 * n + 1 = 2 * n + 1 by rfl, pow_succ]
  field_simp
  norm_num

private theorem integral_arctangentQuotientTerm (x : ℝ) (n : ℕ) :
    (∫ t in (0 : ℝ)..x, arctangentQuotientTerm t n) =
      integratedArctangentTerm x n := by
  have hfun :
      (fun t : ℝ => arctangentQuotientTerm t n) =
        fun t : ℝ =>
          ((-1 : ℝ) ^ n / (2 * n + 1 : ℝ)) * t ^ (2 * n) := by
    funext t
    unfold arctangentQuotientTerm
    ring
  rw [hfun, intervalIntegral.integral_const_mul, integral_pow]
  simp [integratedArctangentTerm]
  field_simp

private theorem norm_arctangentQuotientTerm (t : ℝ) (n : ℕ) :
    ‖arctangentQuotientTerm t n‖ =
      (1 / (2 * n + 1 : ℝ)) * t ^ (2 * n) := by
  rw [Real.norm_eq_abs]
  unfold arctangentQuotientTerm
  have ht : 0 ≤ t ^ (2 * n) := by
    rw [pow_mul]
    positivity
  rw [abs_div, abs_mul, abs_of_nonneg ht,
    abs_of_pos (by positivity : 0 < (2 * n + 1 : ℝ))]
  simp
  ring

private theorem intervalIntegral_norm_arctangentQuotientTerm
    (x : ℝ) (n : ℕ) :
    (∫ t in (0 : ℝ)..x, ‖arctangentQuotientTerm t n‖) =
      x ^ (2 * n + 1) / (2 * n + 1 : ℝ) ^ 2 := by
  simp_rw [norm_arctangentQuotientTerm]
  rw [intervalIntegral.integral_const_mul, integral_pow]
  simp
  field_simp

private theorem setIntegral_norm_arctangentQuotientTerm_le
    (x : ℝ) (hx : |x| ≤ 1) (n : ℕ) :
    (∫ t in Ι (0 : ℝ) x, ‖arctangentQuotientTerm t n‖) ≤
      1 / (n + 1 : ℝ) ^ 2 := by
  have hnonneg :
      0 ≤ ∫ t in Ι (0 : ℝ) x, ‖arctangentQuotientTerm t n‖ :=
    MeasureTheory.integral_nonneg fun _ => norm_nonneg _
  have hpow : |x| ^ (2 * n + 1) ≤ 1 := by
    simpa using
      pow_le_pow_left₀ (abs_nonneg x) hx (2 * n + 1)
  have hden :
      (n + 1 : ℝ) ^ 2 ≤ (2 * n + 1 : ℝ) ^ 2 := by
    gcongr
    norm_cast
    omega
  calc
    (∫ t in Ι (0 : ℝ) x, ‖arctangentQuotientTerm t n‖) =
        |∫ t in Ι (0 : ℝ) x, ‖arctangentQuotientTerm t n‖| :=
      (abs_of_nonneg hnonneg).symm
    _ = |∫ t in (0 : ℝ)..x, ‖arctangentQuotientTerm t n‖| :=
      (intervalIntegral.abs_intervalIntegral_eq
        (fun t => ‖arctangentQuotientTerm t n‖) 0 x MeasureTheory.volume).symm
    _ = |x ^ (2 * n + 1) / (2 * n + 1 : ℝ) ^ 2| := by
      rw [intervalIntegral_norm_arctangentQuotientTerm]
    _ = |x| ^ (2 * n + 1) / (2 * n + 1 : ℝ) ^ 2 := by
      rw [abs_div, abs_pow,
        abs_of_pos (by positivity : 0 < (2 * n + 1 : ℝ) ^ 2)]
    _ ≤ 1 / (n + 1 : ℝ) ^ 2 :=
      div_le_div₀ zero_le_one hpow (by positivity) hden

private theorem tsum_intervalIntegral_arctangentQuotientTerm
    (x : ℝ) (hx : |x| ≤ 1) :
    (∑' n : ℕ, ∫ t in (0 : ℝ)..x, arctangentQuotientTerm t n) =
      ∫ t in (0 : ℝ)..x, ∑' n : ℕ, arctangentQuotientTerm t n := by
  let μ : MeasureTheory.Measure ℝ :=
    MeasureTheory.volume.restrict (Ι (0 : ℝ) x)
  have htermIntegrable :
      ∀ n : ℕ, MeasureTheory.Integrable
        (fun t : ℝ => arctangentQuotientTerm t n) μ := by
    intro n
    have hc : Continuous (fun t : ℝ => arctangentQuotientTerm t n) := by
      unfold arctangentQuotientTerm
      fun_prop
    exact (hc.intervalIntegrable 0 x).def'
  have hpSeries :
      Summable (fun n : ℕ => (1 : ℝ) / (n + 1 : ℝ) ^ 2) := by
    simpa [Real.norm_eq_abs, abs_of_nonneg] using
      (summable_pow_div_add (1 : ℝ) 2 1 Nat.one_lt_two)
  have hnormSummable :
      Summable (fun n : ℕ =>
        ∫ t, ‖arctangentQuotientTerm t n‖ ∂μ) :=
    Summable.of_nonneg_of_le
      (fun n => MeasureTheory.integral_nonneg fun _ => norm_nonneg _)
      (fun n => by
        simpa [μ] using
          setIntegral_norm_arctangentQuotientTerm_le x hx n)
      hpSeries
  simp_rw [intervalIntegral.intervalIntegral_eq_integral_uIoc]
  simp only [smul_eq_mul]
  rw [tsum_mul_left]
  congr 1
  simpa [μ] using
    (MeasureTheory.integral_tsum_of_summable_integral_norm
      htermIntegrable hnormSummable)

theorem gap1 :
    ∀ x : ℝ, |x| ≤ 1 →
      (∫ t in (0 : ℝ)..x, Real.arctan t / t) =
        ∫ t in (0 : ℝ)..x, ∑' n, arctangentQuotientTerm t n := by
  intro x hx
  apply intervalIntegral.integral_congr_ae
  filter_upwards
    [MeasureTheory.Measure.ae_ne MeasureTheory.volume 0,
      MeasureTheory.Measure.ae_ne MeasureTheory.volume 1,
      MeasureTheory.Measure.ae_ne MeasureTheory.volume (-1)]
      with t ht0 ht1 htm1
  intro ht
  have htAbsLe : |t| ≤ |x| := by
    simpa using
      Set.abs_sub_left_of_mem_uIcc (Set.uIoc_subset_uIcc ht)
  have htAbsNe : |t| ≠ 1 := by
    intro habs
    have hsquare : t * t = 1 := by
      have h :=
        (abs_eq_iff_mul_self_eq (a := t) (b := (1 : ℝ))).mp (by
          simpa using habs)
      norm_num at h ⊢
      exact h
    have hfactor : (t - 1) * (t + 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp hfactor with h | h
    · exact ht1 (by linarith)
    · exact htm1 (by linarith)
  have htAbs : |t| < 1 :=
    lt_of_le_of_ne (htAbsLe.trans hx) htAbsNe
  exact (arctangentQuotientTerm_hasSum ht0 htAbs).tsum_eq.symm

theorem gap2 :
    ∀ x : ℝ, |x| ≤ 1 →
      (∫ t in (0 : ℝ)..x, Real.arctan t / t) =
        ∑' n, integratedArctangentTerm x n := by
  intro x hx
  calc
    (∫ t in (0 : ℝ)..x, Real.arctan t / t) =
        ∫ t in (0 : ℝ)..x, ∑' n, arctangentQuotientTerm t n :=
      gap1 x hx
    _ = ∑' n : ℕ, ∫ t in (0 : ℝ)..x,
        arctangentQuotientTerm t n :=
      (tsum_intervalIntegral_arctangentQuotientTerm x hx).symm
    _ = ∑' n, integratedArctangentTerm x n :=
      tsum_congr (fun n => integral_arctangentQuotientTerm x n)

end

end ProofGap.Exercise2904
