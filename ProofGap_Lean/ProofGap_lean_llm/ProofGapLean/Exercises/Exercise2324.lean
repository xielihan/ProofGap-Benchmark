import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open scoped Interval

namespace ProofGap.Exercise2324

noncomputable section

def integrand (x : ℝ) : ℝ := x ^ 9 / Real.sqrt (1 + x)
def targetIntegral : ℝ := ∫ x in 0..1, integrand x
def monomialIntegral : ℝ := ∫ x in 0..1, x ^ 9

private theorem integrand_intervalIntegrable :
    IntervalIntegrable integrand MeasureTheory.volume 0 1 := by
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  unfold integrand
  apply ContinuousOn.div
  · fun_prop
  · fun_prop
  · intro x hx
    exact ne_of_gt (Real.sqrt_pos.2 (by linarith [hx.1]))

theorem gap1 (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    x ^ 9 / Real.sqrt 2 ≤ integrand x := by
  unfold integrand
  have hxpow : 0 ≤ x ^ 9 := pow_nonneg hx.1 9
  have hspos : 0 < Real.sqrt (1 + x) := Real.sqrt_pos.2 (by linarith [hx.1])
  have hsle : Real.sqrt (1 + x) ≤ Real.sqrt 2 :=
    Real.sqrt_le_sqrt (by linarith [hx.2])
  exact div_le_div_of_nonneg_left hxpow hspos hsle

theorem gap2 (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    integrand x ≤ x ^ 9 := by
  unfold integrand
  apply div_le_self (pow_nonneg hx.1 9)
  exact Real.one_le_sqrt.mpr (by linarith [hx.1])

theorem gap3 (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    x ^ 9 / Real.sqrt 2 ≤ x ^ 9 := by
  exact (gap1 x hx).trans (gap2 x hx)

theorem gap4 :
    1 / Real.sqrt 2 * monomialIntegral ≤ targetIntegral := by
  rw [monomialIntegral, targetIntegral]
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_mono_on (by norm_num)
  · exact (((by fun_prop) : Continuous fun x : ℝ =>
      1 / Real.sqrt 2 * x ^ 9).intervalIntegrable 0 1)
  · exact integrand_intervalIntegrable
  · intro x hx
    simpa [div_eq_mul_inv, mul_comm] using gap1 x hx

theorem gap5 :
    targetIntegral ≤ monomialIntegral := by
  rw [targetIntegral, monomialIntegral]
  apply intervalIntegral.integral_mono_on (by norm_num)
  · exact integrand_intervalIntegrable
  · exact (((by fun_prop) : Continuous fun x : ℝ => x ^ 9).intervalIntegrable 0 1)
  · intro x hx
    exact gap2 x hx

theorem gap6 :
    1 / Real.sqrt 2 * monomialIntegral ≤ monomialIntegral := by
  exact gap4.trans gap5

theorem gap7 :
    1 / (10 * Real.sqrt 2) ≤ targetIntegral := by
  convert gap4 using 1
  unfold monomialIntegral
  rw [integral_pow]
  norm_num

theorem gap8 :
    targetIntegral ≤ (1 / 10 : ℝ) := by
  convert gap5 using 1
  unfold monomialIntegral
  rw [integral_pow]
  norm_num

theorem gap9 :
    1 / (10 * Real.sqrt 2) ≤ (1 / 10 : ℝ) := by
  exact gap7.trans gap8

end

end ProofGap.Exercise2324
