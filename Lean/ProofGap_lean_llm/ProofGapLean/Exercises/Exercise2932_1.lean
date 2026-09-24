import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace ProofGap.Exercise2932_1

noncomputable section

open scoped BigOperators Interval

def integrand (x : ℝ) : ℝ :=
  Real.exp (-x ^ 2)

def exponentialTerm (n : ℕ) (x : ℝ) : ℝ :=
  (-1 : ℝ) ^ n * x ^ (2 * n) / (Nat.factorial n : ℝ)

def integratedTerm (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n /
    (((2 * n + 1 : ℕ) : ℝ) * (Nat.factorial n : ℝ))

def gaussianIntegral : ℝ :=
  ∫ x in (0 : ℝ)..1, integrand x

def Approx (u v ε : ℝ) : Prop :=
  |u - v| < ε

private theorem hasSum_exponentialTerm (x : ℝ) :
    HasSum (fun n => exponentialTerm n x) (integrand x) := by
  have h := NormedSpace.expSeries_div_hasSum_exp (-x ^ 2)
  convert h using 1
  · ext n
    simp only [exponentialTerm]
    rw [neg_pow, pow_mul]
    ring
  · simp [integrand, Real.exp_eq_exp_ℝ]

private theorem integral_exponentialTerm (n : ℕ) :
    (∫ x in (0 : ℝ)..1, exponentialTerm n x) = integratedTerm n := by
  simp only [exponentialTerm]
  rw [show (fun x : ℝ => (-1) ^ n * x ^ (2 * n) / (Nat.factorial n : ℝ)) =
      fun x : ℝ => ((-1) ^ n / (Nat.factorial n : ℝ)) * x ^ (2 * n) by
    funext x
    ring]
  rw [intervalIntegral.integral_const_mul, integral_pow]
  simp only [one_pow, zero_pow, Nat.succ_ne_zero, ne_eq, not_false_eq_true,
    sub_zero, integratedTerm]
  push_cast
  have hf : (Nat.factorial n : ℝ) ≠ 0 := by positivity
  have ho : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
  field_simp [hf, ho]

private theorem hasSum_integratedTerm_gaussianIntegral :
    HasSum integratedTerm gaussianIntegral := by
  have hmeas : ∀ n : ℕ, MeasureTheory.AEStronglyMeasurable (exponentialTerm n)
      (MeasureTheory.volume.restrict (Ι (0 : ℝ) 1)) := by
    intro n
    have hc : Continuous (fun t : ℝ =>
        (-1 : ℝ) ^ n * t ^ (2 * n) / (Nat.factorial n : ℝ)) := by
      fun_prop
    have hc' : Continuous (exponentialTerm n) := by
      simpa only [exponentialTerm] using hc
    exact hc'.aestronglyMeasurable
  have hbound : ∀ n : ℕ, ∀ᵐ t ∂MeasureTheory.volume,
      t ∈ Ι (0 : ℝ) 1 →
        ‖exponentialTerm n t‖ ≤ (1 : ℝ) / (Nat.factorial n : ℝ) := by
    intro n
    filter_upwards with t ht
    have ht' : t ∈ Set.Ioc (0 : ℝ) 1 := by
      simpa [Set.uIoc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using ht
    have habs : |t| ≤ 1 := by
      rw [abs_of_nonneg ht'.1.le]
      exact ht'.2
    have hp : |t| ^ (2 * n) ≤ (1 : ℝ) := by
      exact pow_le_one₀ (abs_nonneg t) habs
    simp only [exponentialTerm, norm_div, norm_mul, norm_pow,
      Real.norm_eq_abs, abs_neg, abs_one, one_pow]
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (Nat.factorial n : ℝ))]
    simpa only [one_mul] using div_le_div_of_nonneg_right hp (by positivity)
  have hsum : Summable (fun n : ℕ => (1 : ℝ) / (Nat.factorial n : ℝ)) := by
    simpa using (NormedSpace.expSeries_div_summable (1 : ℝ))
  have hbound_summable : ∀ᵐ t ∂MeasureTheory.volume,
      t ∈ Ι (0 : ℝ) 1 →
        Summable (fun n : ℕ => (1 : ℝ) / (Nat.factorial n : ℝ)) := by
    exact MeasureTheory.ae_of_all _ (fun _ _ => hsum)
  have hbound_integrable : IntervalIntegrable
      (fun _ : ℝ => ∑' n : ℕ, (1 : ℝ) / (Nat.factorial n : ℝ))
      MeasureTheory.volume 0 1 := intervalIntegrable_const
  have hlim : ∀ᵐ t ∂MeasureTheory.volume, t ∈ Ι (0 : ℝ) 1 →
      HasSum (fun n => exponentialTerm n t) (integrand t) := by
    exact MeasureTheory.ae_of_all _ (fun t _ => hasSum_exponentialTerm t)
  have h := intervalIntegral.hasSum_integral_of_dominated_convergence
    (a := (0 : ℝ)) (b := 1) (f := integrand) (F := fun n t => exponentialTerm n t)
    (fun n (_ : ℝ) => (1 : ℝ) / (Nat.factorial n : ℝ))
    hmeas hbound hbound_summable hbound_integrable hlim
  have h' : HasSum (fun n => ∫ t in (0 : ℝ)..1, exponentialTerm n t)
      gaussianIntegral := by
    simpa only [gaussianIntegral] using h
  convert h' using 1
  ext n
  exact (integral_exponentialTerm n).symm

private theorem gaussianIntegral_eq_integral_tsum :
    gaussianIntegral =
      ∫ x in (0 : ℝ)..1, ∑' n : ℕ, exponentialTerm n x := by
  unfold gaussianIntegral
  apply intervalIntegral.integral_congr
  intro t ht
  exact (hasSum_exponentialTerm t).tsum_eq.symm

private def coefficient (n : ℕ) : ℝ :=
  1 / (((2 * n + 1 : ℕ) : ℝ) * (Nat.factorial n : ℝ))

private theorem integratedTerm_eq (n : ℕ) :
    integratedTerm n = (-1 : ℝ) ^ n * coefficient n := by
  simp only [integratedTerm, coefficient]
  ring

private theorem antitone_coefficient : Antitone coefficient := by
  apply antitone_nat_of_succ_le
  intro n
  simp only [coefficient, Nat.factorial_succ]
  push_cast
  apply one_div_le_one_div_of_le
  · positivity
  · have hn : (0 : ℝ) ≤ n := by positivity
    have hf : (0 : ℝ) ≤ Nat.factorial n := by positivity
    nlinarith [mul_nonneg hn hf]

private theorem tendsto_integratedPartial :
    Tendsto (fun m => ∑ n ∈ Finset.range m, (-1 : ℝ) ^ n * coefficient n)
      atTop (nhds gaussianIntegral) := by
  convert hasSum_integratedTerm_gaussianIntegral.tendsto_sum_nat using 1
  ext m
  apply Finset.sum_congr rfl
  intro n hn
  exact (integratedTerm_eq n).symm

private theorem gaussianIntegral_lower :
    (7463 / 10000 : ℝ) < gaussianIntegral := by
  have hlo := antitone_coefficient.alternating_series_le_tendsto
    tendsto_integratedPartial 3
  norm_num [coefficient, Finset.sum_range_succ] at hlo ⊢
  linarith

private theorem gaussianIntegral_upper :
    gaussianIntegral < (7476 / 10000 : ℝ) := by
  have hhi := antitone_coefficient.tendsto_le_alternating_series
    tendsto_integratedPartial 2
  norm_num [coefficient, Finset.sum_range_succ] at hhi ⊢
  linarith

theorem gap1 :
    gaussianIntegral =
      ∫ x in (0 : ℝ)..1, ∑' n : ℕ, exponentialTerm n x := by
  exact gaussianIntegral_eq_integral_tsum

theorem gap2 :
    gaussianIntegral = ∑' n : ℕ, integratedTerm n := by
  exact hasSum_integratedTerm_gaussianIntegral.tsum_eq.symm

theorem gap3 :
    (7463 / 10000 : ℝ) < gaussianIntegral := by
  exact gaussianIntegral_lower

theorem gap4 :
    gaussianIntegral < (7476 / 10000 : ℝ) := by
  exact gaussianIntegral_upper

theorem gap5 :
    (7463 / 10000 : ℝ) < (7476 / 10000 : ℝ) := by
  norm_num

theorem gap6 :
    Approx gaussianIntegral (747 / 1000 : ℝ)
      (1 / 1000 : ℝ) := by
  have hlo := gaussianIntegral_lower
  have hhi := gaussianIntegral_upper
  rw [Approx, abs_lt]
  norm_num at hlo hhi ⊢
  constructor <;> linarith

end

end ProofGap.Exercise2932_1
