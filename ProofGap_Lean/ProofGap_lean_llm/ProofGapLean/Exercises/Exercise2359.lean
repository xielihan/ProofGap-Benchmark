import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace ProofGap.Exercise2359
noncomputable section

open Filter MeasureTheory

def integrand (x : ℝ) : ℝ :=
  1 / (x * Real.rpow (x ^ 2 + 1) (1 / 3 : ℝ))

def comparisonExpression (x : ℝ) : ℝ :=
  Real.rpow x (5 / 3 : ℝ) * integrand x

private theorem comparison_eq {x : ℝ} (hx : 0 < x) :
    comparisonExpression x = (x ^ 2 / (x ^ 2 + 1)) ^ (1 / 3 : ℝ) := by
  have hx53 : x ^ (5 / 3 : ℝ) = x * (x ^ 2) ^ (1 / 3 : ℝ) := by
    calc
      x ^ (5 / 3 : ℝ) = x ^ ((1 : ℝ) + 2 * (1 / 3 : ℝ)) := by
        congr 1
        norm_num
      _ = x ^ (1 : ℝ) * x ^ ((2 : ℝ) * (1 / 3 : ℝ)) :=
        Real.rpow_add hx _ _
      _ = x * (x ^ (2 : ℝ)) ^ (1 / 3 : ℝ) := by
        rw [Real.rpow_one, Real.rpow_mul hx.le]
      _ = x * (x ^ 2) ^ (1 / 3 : ℝ) := by
        exact congrArg (fun z : ℝ => x * z ^ (1 / 3 : ℝ))
          (Real.rpow_natCast x 2)
  have hqpos : 0 < x ^ 2 + 1 := by positivity
  unfold comparisonExpression integrand
  change x ^ (5 / 3 : ℝ) *
    (1 / (x * (x ^ 2 + 1) ^ (1 / 3 : ℝ))) =
      (x ^ 2 / (x ^ 2 + 1)) ^ (1 / 3 : ℝ)
  rw [hx53, Real.div_rpow (sq_nonneg x) hqpos.le]
  field_simp [hx.ne']

theorem gap1 :
    Tendsto comparisonExpression atTop (nhds 1) := by
  have hinv : Tendsto (fun x : ℝ => 1 / x) atTop (nhds 0) := by
    simpa [one_div] using (tendsto_inv_atTop_zero :
      Tendsto (fun x : ℝ => x⁻¹) atTop (nhds 0))
  have hinv2 : Tendsto (fun x : ℝ => 1 / x ^ 2) atTop (nhds 0) := by
    simpa [div_pow] using hinv.pow 2
  have hone : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (nhds 1) :=
    tendsto_const_nhds
  have hqalt :
      Tendsto (fun x : ℝ => 1 / (1 + 1 / x ^ 2)) atTop (nhds 1) := by
    convert hone.div (hone.add hinv2) (by positivity) using 1 <;> norm_num
  have hqcont :
      Tendsto (fun x : ℝ => x ^ 2 / (x ^ 2 + 1)) atTop (nhds 1) := by
    apply hqalt.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    field_simp [hx.ne']
  have hqpos : (0 : ℝ) < 1 := zero_lt_one
  have hrcont := hqcont.rpow_const (p := (1 / 3 : ℝ)) (Or.inl hqpos.ne')
  have hr :
      Tendsto (fun x : ℝ => (x ^ 2 / (x ^ 2 + 1)) ^ (1 / 3 : ℝ))
        atTop (nhds 1) := by
    simpa using hrcont
  apply hr.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  exact (comparison_eq hx).symm

theorem gap2 :
    IntegrableOn integrand (Set.Ioi (1 : ℝ)) := by
  have hg : IntegrableOn (fun x : ℝ => x ^ (-5 / 3 : ℝ)) (Set.Ioi (1 : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) (by norm_num)
  unfold IntegrableOn at hg
  change Integrable integrand (volume.restrict (Set.Ioi (1 : ℝ)))
  apply hg.mono
  case hf =>
    unfold integrand
    measurability
  case h =>
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hxpos : 0 < x := lt_trans zero_lt_one hx
    have hqpos : 0 < x ^ 2 + 1 := by positivity
    have hbase0 : 0 ≤ x ^ 2 / (x ^ 2 + 1) :=
      div_nonneg (sq_nonneg x) hqpos.le
    have hbase_le : x ^ 2 / (x ^ 2 + 1) ≤ 1 := by
      apply (div_le_one hqpos).2
      linarith
    have hcomp_le : comparisonExpression x ≤ 1 := by
      rw [comparison_eq hxpos]
      exact Real.rpow_le_one hbase0 hbase_le (by norm_num)
    have hp : 0 < x ^ (5 / 3 : ℝ) := Real.rpow_pos_of_pos hxpos _
    have hi : 0 < integrand x := by
      unfold integrand
      exact one_div_pos.mpr (mul_pos hxpos (Real.rpow_pos_of_pos hqpos _))
    have hid : integrand x = comparisonExpression x / x ^ (5 / 3 : ℝ) := by
      apply (eq_div_iff hp.ne').2
      unfold comparisonExpression
      exact mul_comm _ _
    have hneg : x ^ (-5 / 3 : ℝ) = 1 / x ^ (5 / 3 : ℝ) := by
      rw [show (-5 / 3 : ℝ) = -(5 / 3 : ℝ) by ring]
      simpa [one_div] using Real.rpow_neg hxpos.le (5 / 3 : ℝ)
    rw [Real.norm_eq_abs, abs_of_pos hi, Real.norm_eq_abs,
      abs_of_pos (Real.rpow_pos_of_pos hxpos _), hid, hneg]
    exact (div_le_div_iff_of_pos_right hp).2 hcomp_le

end
end ProofGap.Exercise2359
