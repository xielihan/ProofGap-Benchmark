import ProofGapLean.Prelude.Analysis
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

open Filter
open scoped Interval

namespace ProofGap.Exercise2334

noncomputable section

def integrand (x : ℝ) : ℝ := 1 / x ^ 2
def truncatedIntegral (a b : ℝ) : ℝ := ∫ x in a..b, integrand x
def improperIntegral (a : ℝ) : ℝ := ∫ x in Set.Ioi a, integrand x

theorem gap1 (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    truncatedIntegral a b = 1 / a - 1 / b := by
  unfold truncatedIntegral integrand
  have hpos : ∀ x ∈ Set.uIcc a b, 0 < x := by
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    exact ha.trans_le hx.1
  have hderiv : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (fun y : ℝ => -(y⁻¹)) (1 / x ^ 2) x := by
    intro x hx
    have hx0 : x ≠ 0 := (hpos x hx).ne'
    convert ((hasDerivAt_id x).inv hx0).neg using 1 <;> simp [id] <;> field_simp
  have hcont : ContinuousOn (fun x : ℝ => 1 / x ^ 2) (Set.uIcc a b) := by
    intro x hx
    have hx0 : x ≠ 0 := (hpos x hx).ne'
    exact
      (continuousAt_const.div (continuousAt_id.pow 2) (pow_ne_zero 2 hx0)).continuousWithinAt
  calc
    (∫ x in a..b, 1 / x ^ 2) = -(b⁻¹) - -(a⁻¹) :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable
    _ = 1 / a - 1 / b := by ring

theorem gap2 (a : ℝ) (ha : 0 < a) :
    Tendsto (fun b : ℝ => 1 / a - 1 / b) atTop (nhds (1 / a)) := by
  simpa [one_div] using
    (tendsto_const_nhds.sub (tendsto_inv_atTop_zero :
      Tendsto (fun b : ℝ => b⁻¹) atTop (nhds 0)))

theorem gap3 (a : ℝ) (ha : 0 < a) :
    Tendsto (truncatedIntegral a) atTop (nhds (1 / a)) := by
  apply (gap2 a ha).congr'
  filter_upwards [eventually_ge_atTop a] with b hb
  exact (gap1 a b ha hb).symm

theorem gap4 (a : ℝ) (ha : 0 < a) :
    improperIntegral a = 1 / a := by
  unfold improperIntegral integrand
  calc
    (∫ x in Set.Ioi a, 1 / x ^ 2) = ∫ x in Set.Ioi a, x ^ (-2 : ℝ) := by
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      have hx0 : 0 ≤ x := (ha.trans hx).le
      change 1 / x ^ 2 = x ^ (-2 : ℝ)
      rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num, Real.rpow_neg hx0]
      simp [one_div]
    _ = 1 / a := by
      rw [integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) ha]
      rw [show (-2 : ℝ) + 1 = -1 by norm_num, Real.rpow_neg_one]
      ring

end

end ProofGap.Exercise2334
