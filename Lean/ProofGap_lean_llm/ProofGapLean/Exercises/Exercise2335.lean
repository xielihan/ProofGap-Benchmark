import ProofGapLean.Prelude.Analysis
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace ProofGap.Exercise2335
noncomputable section

open Filter
open scoped Interval

def truncatedIntegral (ε : ℝ) : ℝ :=
  ∫ x in ε..1, Real.log x

def boundaryExpression (ε : ℝ) : ℝ :=
  ε - ε * Real.log ε - 1

theorem gap1 :
    Tendsto truncatedIntegral (nhdsWithin 0 (Set.Ioi 0)) (nhds (-1)) ↔
      Tendsto boundaryExpression (nhdsWithin 0 (Set.Ioi 0)) (nhds (-1)) := by
  have hfun : truncatedIntegral = boundaryExpression := by
    funext ε
    unfold truncatedIntegral boundaryExpression
    rw [integral_log]
    simp
    ring
  rw [hfun]

theorem gap2 :
    Tendsto boundaryExpression (nhdsWithin 0 (Set.Ioi 0)) (nhds (-1)) := by
  have hid : Tendsto (fun x : ℝ => x) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have hprod : Tendsto (fun x : ℝ => x * Real.log x)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    simpa [Real.rpow_one, mul_comm] using
      (tendsto_log_mul_rpow_nhdsGT_zero zero_lt_one)
  simpa [boundaryExpression] using (hid.sub hprod).sub tendsto_const_nhds

theorem gap3 :
    Tendsto truncatedIntegral (nhdsWithin 0 (Set.Ioi 0)) (nhds (-1)) := by
  exact gap1.mpr gap2

theorem gap4 :
    (∫ x in (0 : ℝ)..1, Real.log x) = -1 := by
  rw [integral_log]
  norm_num

end
end ProofGap.Exercise2335
