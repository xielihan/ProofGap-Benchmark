import ProofGapLean.Prelude.Analysis
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace ProofGap.Exercise2438
noncomputable section

open Set
open scoped Interval

def xCurve (a y : ℝ) : ℝ :=
  a * Real.log ((a + Real.sqrt (a ^ 2 - y ^ 2)) / y) -
    Real.sqrt (a ^ 2 - y ^ 2)
def s (a b : ℝ) : ℝ := ∫ y in b..a, a / y

theorem gap1 (a b y : ℝ) (hb : 0 < b) (hba : b < a)
    (hy : y ∈ Ioo b a) :
    HasDerivAt (xCurve a) (-Real.sqrt (a ^ 2 - y ^ 2) / y) y := by
  unfold xCurve
  have hypos : 0 < y := lt_trans hb hy.1
  have hy0 : y ≠ 0 := ne_of_gt hypos
  have hapos : 0 < a := lt_trans hb hba
  have hprod : 0 < (a - y) * (a + y) :=
    mul_pos (sub_pos.mpr hy.2) (by linarith)
  have hrad : 0 < a ^ 2 - y ^ 2 := by
    nlinarith
  have hsne : Real.sqrt (a ^ 2 - y ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hrad)
  have hsq : Real.sqrt (a ^ 2 - y ^ 2) ^ 2 = a ^ 2 - y ^ 2 :=
    Real.sq_sqrt (le_of_lt hrad)
  have hinner :
      HasDerivAt (fun z : ℝ => a ^ 2 - z ^ 2) (-2 * y) y := by
    simpa [mul_comm] using
      (hasDerivAt_const y (a ^ 2)).sub ((hasDerivAt_id y).pow 2)
  have hu0 :=
    (Real.hasDerivAt_sqrt (ne_of_gt hrad)).comp y hinner
  have hu :
      HasDerivAt (fun z : ℝ => Real.sqrt (a ^ 2 - z ^ 2))
        (-y / Real.sqrt (a ^ 2 - y ^ 2)) y := by
    convert hu0 using 1 <;> field_simp [hsne] <;> ring
  have hnum :
      HasDerivAt
        (fun z : ℝ => a + Real.sqrt (a ^ 2 - z ^ 2))
        (-y / Real.sqrt (a ^ 2 - y ^ 2)) y :=
    hu.const_add a
  have hnumpos : 0 < a + Real.sqrt (a ^ 2 - y ^ 2) :=
    add_pos_of_pos_of_nonneg hapos (Real.sqrt_nonneg _)
  have hqpos :
      0 < (a + Real.sqrt (a ^ 2 - y ^ 2)) / y :=
    div_pos hnumpos hypos
  have hq :
      HasDerivAt
        (fun z : ℝ => (a + Real.sqrt (a ^ 2 - z ^ 2)) / z)
        (((-y / Real.sqrt (a ^ 2 - y ^ 2)) * y -
            (a + Real.sqrt (a ^ 2 - y ^ 2))) / y ^ 2) y := by
    simpa using hnum.div (hasDerivAt_id y) hy0
  have hlog :
      HasDerivAt
        (fun z : ℝ => Real.log ((a + Real.sqrt (a ^ 2 - z ^ 2)) / z))
        ((((-y / Real.sqrt (a ^ 2 - y ^ 2)) * y -
            (a + Real.sqrt (a ^ 2 - y ^ 2))) / y ^ 2) /
          ((a + Real.sqrt (a ^ 2 - y ^ 2)) / y)) y :=
    hq.log (ne_of_gt hqpos)
  convert (hlog.const_mul a).sub hu using 1 <;>
    field_simp [hy0, hsne, ne_of_gt hnumpos] <;>
    nlinarith [hsq]

theorem gap2 (a b y : ℝ) (hb : 0 < b) (hba : b < a)
    (hy : y ∈ Ioo b a) :
    Real.sqrt (1 + (-Real.sqrt (a ^ 2 - y ^ 2) / y) ^ 2) = a / y := by
  have hypos : 0 < y := lt_trans hb hy.1
  have hy0 : y ≠ 0 := ne_of_gt hypos
  have hapos : 0 < a := lt_trans hb hba
  have hrad : 0 ≤ a ^ 2 - y ^ 2 := by
    have hprod : 0 < (a - y) * (a + y) :=
      mul_pos (sub_pos.mpr hy.2) (by linarith)
    nlinarith
  have hsq : Real.sqrt (a ^ 2 - y ^ 2) ^ 2 = a ^ 2 - y ^ 2 :=
    Real.sq_sqrt hrad
  have hinside :
      1 + (-Real.sqrt (a ^ 2 - y ^ 2) / y) ^ 2 = (a / y) ^ 2 := by
    field_simp [hy0]
    nlinarith [hsq]
  rw [hinside]
  exact Real.sqrt_sq (le_of_lt (div_pos hapos hypos))

theorem gap3 (a b : ℝ) (hb : 0 < b) (hba : b < a) :
    s a b = ∫ y in b..a, a / y := by
  rfl

theorem gap4 (a b : ℝ) (hb : 0 < b) (hba : b < a) :
    (∫ y in b..a, a / y) = a * Real.log (a / b) := by
  have hapos : 0 < a := lt_trans hb hba
  have hnonzero : ∀ z ∈ uIcc b a, z ≠ 0 := by
    intro z hz
    rw [uIcc_of_le (le_of_lt hba)] at hz
    exact ne_of_gt (lt_of_lt_of_le hb hz.1)
  have hderiv : ∀ z ∈ uIcc b a, HasDerivAt Real.log z⁻¹ z := by
    intro z hz
    exact Real.hasDerivAt_log (hnonzero z hz)
  have hcont : ContinuousOn (fun z : ℝ => z⁻¹) (uIcc b a) := by
    intro z hz
    exact (continuousAt_id.inv₀ (hnonzero z hz)).continuousWithinAt
  have hinv :
      (∫ z in b..a, z⁻¹) = Real.log a - Real.log b := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      hcont.intervalIntegrable
  calc
    (∫ y in b..a, a / y) = ∫ y in b..a, a * y⁻¹ := by
      congr 1
    _ = a * ∫ y in b..a, y⁻¹ := by
      rw [intervalIntegral.integral_const_mul]
    _ = a * (Real.log a - Real.log b) := by
      rw [hinv]
    _ = a * Real.log (a / b) := by
      rw [Real.log_div (ne_of_gt hapos) (ne_of_gt hb)]

theorem gap5 (a b : ℝ) (hb : 0 < b) (hba : b < a) :
    s a b = a * Real.log (a / b) := by
  rw [gap3 a b hb hba, gap4 a b hb hba]

end
end ProofGap.Exercise2438
