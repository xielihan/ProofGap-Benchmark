import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic

namespace ProofGap.Exercise2649

noncomputable section

open Filter
open scoped Interval

def integrand (x : ℝ) : ℝ :=
  Real.exp (-Real.sqrt x)

def u (n : ℕ) : ℝ :=
  ∫ x in (n : ℝ)..n + 1, integrand x

def majorant (n : ℕ) : ℝ :=
  Real.exp (-Real.sqrt n)

def comparison (n : ℕ) : ℝ :=
  1 / (n : ℝ) ^ 2

def ratio (n : ℕ) : ℝ :=
  majorant n / comparison n

def rewrittenRatio (n : ℕ) : ℝ :=
  (n : ℝ) ^ 2 / Real.exp (Real.sqrt n)

private theorem continuous_integrand : Continuous integrand := by
  unfold integrand
  fun_prop

theorem gap1 :
    ∀ n : ℕ, 0 < u n := by
  intro n
  unfold u
  refine intervalIntegral.integral_pos (by norm_num) continuous_integrand.continuousOn ?_ ?_
  · intro x hx
    exact (Real.exp_pos _).le
  · refine ⟨(n : ℝ), ⟨le_rfl, by norm_num⟩, ?_⟩
    exact Real.exp_pos _

theorem gap2 :
    ∀ n : ℕ, u n ≤ majorant n := by
  intro n
  have hab : (n : ℝ) ≤ n + 1 := by norm_num
  unfold u
  calc
    (∫ x in (n : ℝ)..n + 1, integrand x) ≤
        ∫ _ in (n : ℝ)..n + 1, majorant n := by
      exact intervalIntegral.integral_mono_on hab
        (continuous_integrand.intervalIntegrable _ _)
        (continuous_const.intervalIntegrable _ _) fun x hx => by
          unfold integrand majorant
          exact Real.exp_le_exp.mpr (neg_le_neg (Real.sqrt_le_sqrt hx.1))
    _ = majorant n := by simp

theorem gap3 :
    ∀ n : ℕ, 0 < majorant n := by
  intro n
  unfold majorant
  exact Real.exp_pos _

theorem gap4 :
    ∀ n : ℕ, 1 ≤ n → ratio n = rewrittenRatio n := by
  intro n hn
  have hn0 : (n : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hn))
  unfold ratio majorant comparison rewrittenRatio
  rw [Real.exp_neg]
  field_simp [hn0, Real.exp_ne_zero]

theorem gap5 :
    Tendsto (fun n : ℕ => rewrittenRatio (n + 1)) atTop (nhds 0) := by
  have hsqrt : Tendsto
      (fun n : ℕ => Real.sqrt (((n + 1 : ℕ) : ℝ))) atTop atTop :=
    (Real.tendsto_sqrt_atTop.comp
      (tendsto_natCast_atTop_atTop (R := ℝ))).comp (tendsto_add_atTop_nat 1)
  have hlimit := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 4).comp hsqrt
  refine Tendsto.congr' (Filter.Eventually.of_forall fun n => ?_) hlimit
  unfold rewrittenRatio
  change Real.sqrt (((n + 1 : ℕ) : ℝ)) ^ 4 *
      Real.exp (-Real.sqrt (((n + 1 : ℕ) : ℝ))) =
    (((n + 1 : ℕ) : ℝ)) ^ 2 / Real.exp (Real.sqrt (((n + 1 : ℕ) : ℝ)))
  rw [Real.exp_neg, div_eq_mul_inv]
  congr 1
  calc
    Real.sqrt (((n + 1 : ℕ) : ℝ)) ^ 4 =
        (Real.sqrt (((n + 1 : ℕ) : ℝ)) ^ 2) ^ 2 := by ring
    _ = (((n + 1 : ℕ) : ℝ)) ^ 2 := by
      rw [Real.sq_sqrt (by positivity)]

theorem gap6 :
    Tendsto (fun n : ℕ => ratio (n + 1)) atTop (nhds 0) := by
  refine Tendsto.congr' (Filter.Eventually.of_forall fun n => ?_) gap5
  exact (gap4 (n + 1) (by omega)).symm

theorem gap7 :
    Summable (fun n : ℕ => majorant (n + 1)) := by
  have hfull : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hcomparison : Summable (fun n : ℕ => comparison (n + 1)) := by
    simpa [comparison] using (summable_nat_add_iff 1).mpr hfull
  apply hcomparison.of_norm_bounded_eventually_nat
  filter_upwards [(tendsto_order.1 gap6).2 1 (by norm_num)] with n hn
  rw [Real.norm_eq_abs, abs_of_pos (gap3 (n + 1))]
  have hcpos : 0 < comparison (n + 1) := by
    unfold comparison
    positivity
  have hratio : majorant (n + 1) / comparison (n + 1) ≤ 1 := by
    simpa [ratio] using hn.le
  exact (div_le_one hcpos).mp hratio

theorem gap8
    (hpos : ∀ n : ℕ, 0 ≤ u n)
    (hbound : ∀ n : ℕ, u n ≤ majorant n)
    (hmajorant : Summable (fun n : ℕ => majorant (n + 1))) :
    Summable (fun n : ℕ => u (n + 1)) := by
  exact hmajorant.of_nonneg_of_le
    (fun n => hpos (n + 1))
    (fun n => hbound (n + 1))

theorem gap9
    (hsum : Summable (fun n : ℕ => u (n + 1))) :
    Summable (fun n : ℕ => u (n + 1)) := by
  exact hsum

end

end ProofGap.Exercise2649
