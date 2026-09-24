import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise506_1

noncomputable section

def seq (x : ℝ) : ℝ :=
  Real.rpow ((1 + x) / (2 + x)) ((1 - Real.sqrt x) / (1 - x))

/-- Exercise 506_1, gap 1. -/
theorem gap1 :
    Filter.Tendsto seq (nhds 0) (nhds (1 / 2 : ℝ)) := by
  have hbase :
      ContinuousAt (fun x : ℝ => (1 + x) / (2 + x)) 0 := by
    exact
      (continuousAt_const.add continuousAt_id).div
        (continuousAt_const.add continuousAt_id) (by norm_num)
  have hexp :
      ContinuousAt (fun x : ℝ => (1 - Real.sqrt x) / (1 - x)) 0 := by
    exact
      (continuousAt_const.sub Real.continuous_sqrt.continuousAt).div
        (continuousAt_const.sub continuousAt_id) (by norm_num)
  have hlogbase :
      ContinuousAt (fun x : ℝ => Real.log ((1 + x) / (2 + x))) 0 := by
    exact hbase.log (by norm_num)
  have hexponential :
      ContinuousAt
        (fun x : ℝ => Real.exp
          (Real.log ((1 + x) / (2 + x)) *
            ((1 - Real.sqrt x) / (1 - x)))) 0 := by
    exact Real.continuous_exp.continuousAt.comp (hlogbase.mul hexp)
  have hpos :
      ∀ᶠ x : ℝ in nhds 0, 0 < (1 + x) / (2 + x) := by
    exact hbase.tendsto (Ioi_mem_nhds (by norm_num))
  have heq :
      (fun x : ℝ => Real.exp
        (Real.log ((1 + x) / (2 + x)) *
          ((1 - Real.sqrt x) / (1 - x)))) =ᶠ[nhds 0] seq := by
    filter_upwards [hpos] with x hx
    rw [seq]
    exact
      (Real.rpow_def_of_pos hx
        ((1 - Real.sqrt x) / (1 - x))).symm
  have ht :
      Filter.Tendsto seq (nhds 0)
        (nhds ((fun x : ℝ => Real.exp
          (Real.log ((1 + x) / (2 + x)) *
            ((1 - Real.sqrt x) / (1 - x)))) 0)) :=
    hexponential.tendsto.congr' heq
  have hzero :
      ((fun x : ℝ => Real.exp
        (Real.log ((1 + x) / (2 + x)) *
          ((1 - Real.sqrt x) / (1 - x)))) 0) = (1 / 2 : ℝ) := by
    simpa only [Real.sqrt_zero, add_zero, sub_zero, div_one, mul_one] using
      (Real.exp_log (by norm_num : (0 : ℝ) < 1 / 2))
  rw [hzero] at ht
  exact ht

end

end ProofGap.Exercise506_1
