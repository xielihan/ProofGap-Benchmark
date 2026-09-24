import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3906

noncomputable section

open MeasureTheory
open scoped Interval

private lemma integral_const_add_id (c : ℝ) :
    (∫ y in (0 : ℝ)..1, c + y) = c + 1 / 2 := by
  calc
    (∫ y in (0 : ℝ)..1, c + y) =
        ((c + 1 / 2) * 1) - ((c + 0 / 2) * 0) := by
      exact intervalIntegral.integral_eq_sub_of_hasDerivAt
        (f := fun y : ℝ => (c + y / 2) * y)
        (f' := fun y : ℝ => c + y)
        (fun y _ => by
          convert (((hasDerivAt_const y c).add
              ((hasDerivAt_id y).div_const 2)).mul
              (hasDerivAt_id y)) using 1 <;>
            simp only [id_eq, Pi.add_apply] <;> ring)
        (show IntervalIntegrable (fun y : ℝ => c + y) volume 0 1 from
          (show Continuous (fun y : ℝ => c + y) from
            continuous_const.add continuous_id).intervalIntegrable 0 1)
    _ = c + 1 / 2 := by ring

theorem gap1 :
    (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, x + y) =
      ∫ x in (0 : ℝ)..1, x + 1 / 2 := by
  simp_rw [integral_const_add_id]

theorem gap2 :
    (∫ x in (0 : ℝ)..1, x + 1 / 2) = 1 := by
  calc
    (∫ x in (0 : ℝ)..1, x + 1 / 2) = (1 / 2 : ℝ) + 1 / 2 := by
      simpa [add_comm] using (integral_const_add_id (1 / 2 : ℝ))
    _ = 1 := by norm_num

theorem gap3 :
    (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, x + y) = 1 := by
  exact gap1.trans gap2

end

end ProofGap.Exercise3906
