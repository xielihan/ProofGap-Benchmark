import ProofGapLean.Prelude.Analysis
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace ProofGap.Exercise2434
noncomputable section

open scoped Interval

def arcIntegrand (x : ℝ) : ℝ := Real.sqrt (1 + Real.exp (2 * x))
def primitive (x : ℝ) : ℝ :=
  arcIntegrand x +
    (1 / 2 : ℝ) *
      Real.log ((arcIntegrand x - 1) / (arcIntegrand x + 1))
def s (x₀ : ℝ) : ℝ := ∫ x in (0 : ℝ)..x₀, arcIntegrand x

private theorem primitive_hasDerivAt (x : ℝ) :
    HasDerivAt primitive (arcIntegrand x) x := by
  have hexp : 0 < Real.exp (2 * x) := Real.exp_pos _
  have hbase : 0 < 1 + Real.exp (2 * x) := by
    linarith
  have hsq : arcIntegrand x ^ 2 = 1 + Real.exp (2 * x) := by
    unfold arcIntegrand
    exact Real.sq_sqrt (le_of_lt hbase)
  have hapos : 0 < arcIntegrand x := by
    unfold arcIntegrand
    exact Real.sqrt_pos.2 hbase
  have haone : 1 < arcIntegrand x := by
    nlinarith
  have hapos_ne : arcIntegrand x ≠ 0 := ne_of_gt hapos
  have hminus_ne : arcIntegrand x - 1 ≠ 0 :=
    ne_of_gt (sub_pos.mpr haone)
  have hplus_ne : arcIntegrand x + 1 ≠ 0 :=
    ne_of_gt (by linarith)
  have hlin : HasDerivAt (fun y : ℝ => 2 * y) 2 x := by
    simpa using (hasDerivAt_id x).const_mul (2 : ℝ)
  have hExp :
      HasDerivAt (fun y : ℝ => Real.exp (2 * y))
        (Real.exp (2 * x) * 2) x :=
    (Real.hasDerivAt_exp (2 * x)).comp x hlin
  have hinside :
      HasDerivAt (fun y : ℝ => 1 + Real.exp (2 * y))
        (Real.exp (2 * x) * 2) x :=
    hExp.const_add 1
  have hsqrt :=
    (Real.hasDerivAt_sqrt (ne_of_gt hbase)).comp x hinside
  have hArc :
      HasDerivAt arcIntegrand
        (Real.exp (2 * x) / arcIntegrand x) x := by
    change HasDerivAt
      (fun y : ℝ => Real.sqrt (1 + Real.exp (2 * y)))
      (Real.exp (2 * x) / Real.sqrt (1 + Real.exp (2 * x))) x
    convert hsqrt using 1 <;>
      field_simp [ne_of_gt hbase, hapos_ne] <;> ring
  have hquot :=
    (hArc.sub_const 1).div (hArc.add_const 1) hplus_ne
  have hratio_ne :
      (arcIntegrand x - 1) / (arcIntegrand x + 1) ≠ 0 :=
    div_ne_zero hminus_ne hplus_ne
  have hlog :=
    (Real.hasDerivAt_log hratio_ne).comp x hquot
  have hlog' :
      HasDerivAt
        (fun y : ℝ =>
          Real.log ((arcIntegrand y - 1) / (arcIntegrand y + 1)))
        (2 / arcIntegrand x) x := by
    convert hlog using 1 <;>
      field_simp [hapos_ne, hminus_ne, hplus_ne] <;>
      nlinarith [hsq]
  unfold primitive
  convert hArc.add (hlog'.const_mul (1 / 2 : ℝ)) using 1 <;>
    field_simp [hapos_ne] <;>
    nlinarith [hsq]

private theorem half_log_arc_ratio (x : ℝ) :
    (1 / 2 : ℝ) *
        Real.log ((arcIntegrand x - 1) / (arcIntegrand x + 1)) =
      x - Real.log (1 + arcIntegrand x) := by
  have hexp : 0 < Real.exp (2 * x) := Real.exp_pos _
  have hbase : 0 < 1 + Real.exp (2 * x) := by
    linarith
  have hsq : arcIntegrand x ^ 2 = 1 + Real.exp (2 * x) := by
    unfold arcIntegrand
    exact Real.sq_sqrt (le_of_lt hbase)
  have hapos : 0 < arcIntegrand x := by
    unfold arcIntegrand
    exact Real.sqrt_pos.2 hbase
  have haone : 1 < arcIntegrand x := by
    nlinarith
  have hminus_ne : arcIntegrand x - 1 ≠ 0 :=
    ne_of_gt (sub_pos.mpr haone)
  have hplus_ne : arcIntegrand x + 1 ≠ 0 :=
    ne_of_gt (by linarith)
  have hprod :
      (arcIntegrand x - 1) * (arcIntegrand x + 1) =
        Real.exp (2 * x) := by
    nlinarith [hsq]
  have hlogprod :
      Real.log (arcIntegrand x - 1) +
          Real.log (arcIntegrand x + 1) =
        2 * x := by
    calc
      Real.log (arcIntegrand x - 1) +
          Real.log (arcIntegrand x + 1) =
          Real.log ((arcIntegrand x - 1) *
            (arcIntegrand x + 1)) := by
              rw [Real.log_mul hminus_ne hplus_ne]
      _ = Real.log (Real.exp (2 * x)) := by rw [hprod]
      _ = 2 * x := Real.log_exp _
  have hadd : 1 + arcIntegrand x = arcIntegrand x + 1 := by
    ring
  rw [Real.log_div hminus_ne hplus_ne, hadd]
  linarith [hlogprod]

theorem gap1 (x₀ : ℝ) :
    s x₀ = ∫ x in (0 : ℝ)..x₀, Real.sqrt (1 + Real.exp (2 * x)) := by
  rfl

theorem gap2 (x₀ : ℝ) :
    (∫ x in (0 : ℝ)..x₀, arcIntegrand x) =
      primitive x₀ - primitive 0 := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x hx
    exact primitive_hasDerivAt x
  · have hcont : Continuous arcIntegrand := by
      unfold arcIntegrand
      exact Real.continuous_sqrt.comp
        (continuous_const.add
          (Real.continuous_exp.comp (continuous_const.mul continuous_id)))
    exact hcont.intervalIntegrable (μ := MeasureTheory.volume) (0 : ℝ) x₀

theorem gap3 (x₀ : ℝ) :
    s x₀ = primitive x₀ - primitive 0 := by
  rw [gap1]
  exact gap2 x₀

theorem gap4 (x₀ : ℝ) :
    s x₀ =
      arcIntegrand x₀ - Real.sqrt 2 +
        (1 / 2 : ℝ) * Real.log ((arcIntegrand x₀ - 1) / (arcIntegrand x₀ + 1)) -
          (1 / 2 : ℝ) * Real.log ((Real.sqrt 2 - 1) / (Real.sqrt 2 + 1)) := by
  rw [gap3]
  norm_num [primitive, arcIntegrand] <;> ring

theorem gap5 (x₀ : ℝ) :
    s x₀ =
      x₀ - Real.sqrt 2 + arcIntegrand x₀ -
        Real.log ((1 + arcIntegrand x₀) / (1 + Real.sqrt 2)) := by
  rw [gap4, half_log_arc_ratio x₀]
  have hzero := half_log_arc_ratio 0
  norm_num [arcIntegrand] at hzero
  rw [hzero]
  have ha : 0 ≤ arcIntegrand x₀ := by
    unfold arcIntegrand
    exact Real.sqrt_nonneg _
  have hnum : 1 + arcIntegrand x₀ ≠ 0 :=
    ne_of_gt (by linarith)
  have hsqrt : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hden : 1 + Real.sqrt 2 ≠ 0 :=
    ne_of_gt (by linarith)
  rw [Real.log_div hnum hden]
  ring

end
end ProofGap.Exercise2434
