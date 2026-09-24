import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise513

noncomputable section

def f (x : ℝ) : ℝ :=
  Real.rpow ((x ^ 2 + 2 * x - 1) / (2 * x ^ 2 - 3 * x - 2)) (1 / x)

/-- Exercise 513, gap 1; encode the real variable power by `Real.rpow`. -/
theorem gap1 : Filter.Tendsto f Filter.atTop (nhds ((1 / 2 : ℝ) ^ (0 : ℕ))) := by
  have hinv :
      Filter.Tendsto (fun x : ℝ => 1 / x) Filter.atTop (nhds 0) := by
    simpa only [one_div] using
      (tendsto_inv_atTop_zero :
        Filter.Tendsto (fun x : ℝ => x⁻¹) Filter.atTop (nhds 0))
  have hconst (c : ℝ) :
      Filter.Tendsto (fun _ : ℝ => c) Filter.atTop (nhds c) :=
    tendsto_const_nhds
  have hnum :
      Filter.Tendsto
        (fun x : ℝ => 1 + 2 * (1 / x) - (1 / x) ^ 2)
        Filter.atTop (nhds 1) := by
    simpa using
      (((hconst 1).add ((hconst 2).mul hinv)).sub (hinv.pow 2))
  have hden :
      Filter.Tendsto
        (fun x : ℝ => 2 - 3 * (1 / x) - 2 * (1 / x) ^ 2)
        Filter.atTop (nhds 2) := by
    simpa using
      (((hconst 2).sub ((hconst 3).mul hinv)).sub
        ((hconst 2).mul (hinv.pow 2)))
  have hquot :
      Filter.Tendsto
        (fun x : ℝ =>
          (1 + 2 * (1 / x) - (1 / x) ^ 2) /
            (2 - 3 * (1 / x) - 2 * (1 / x) ^ 2))
        Filter.atTop (nhds (1 / 2 : ℝ)) := by
    simpa using hnum.div hden (by norm_num : (2 : ℝ) ≠ 0)
  have hbase :
      Filter.Tendsto
        (fun x : ℝ =>
          (x ^ 2 + 2 * x - 1) / (2 * x ^ 2 - 3 * x - 2))
        Filter.atTop (nhds (1 / 2 : ℝ)) := by
    refine hquot.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop (4 : ℝ)] with x hx
    have hxpos : 0 < x := by linarith
    have hx0 : x ≠ 0 := ne_of_gt hxpos
    have hmul : 0 < x * (x - 3) := by
      exact mul_pos hxpos (by linarith)
    have hx2 : 9 < x ^ 2 := by
      nlinarith [sq_nonneg (x - 3)]
    have hdenpos : 0 < 2 * x ^ 2 - 3 * x - 2 := by
      nlinarith [hmul, hx2]
    have hden0 : 2 * x ^ 2 - 3 * x - 2 ≠ 0 := ne_of_gt hdenpos
    have hqden0 :
        2 - 3 * (1 / x) - 2 * (1 / x) ^ 2 ≠ 0 := by
      intro hz
      apply hden0
      field_simp [hx0] at hz
      nlinarith [hz]
    field_simp [hx0, hden0, hqden0]
    <;> ring
  have hlog :
      Filter.Tendsto
        (fun x : ℝ =>
          Real.log
            ((x ^ 2 + 2 * x - 1) / (2 * x ^ 2 - 3 * x - 2)))
        Filter.atTop (nhds (Real.log (1 / 2 : ℝ))) := by
    exact
      (Real.continuousAt_log (by norm_num : (1 / 2 : ℝ) ≠ 0)).tendsto.comp
        hbase
  have hprod :
      Filter.Tendsto
        (fun x : ℝ =>
          Real.log
              ((x ^ 2 + 2 * x - 1) / (2 * x ^ 2 - 3 * x - 2)) *
            (1 / x))
        Filter.atTop (nhds 0) := by
    simpa using hlog.mul hinv
  have hexp :
      Filter.Tendsto
        (fun x : ℝ =>
          Real.exp
            (Real.log
                ((x ^ 2 + 2 * x - 1) / (2 * x ^ 2 - 3 * x - 2)) *
              (1 / x)))
        Filter.atTop (nhds 1) := by
    simpa [Function.comp_def] using
      (Real.continuous_exp.continuousAt.tendsto.comp hprod)
  have hpos :
      ∀ᶠ (x : ℝ) in Filter.atTop,
        0 < (x ^ 2 + 2 * x - 1) / (2 * x ^ 2 - 3 * x - 2) := by
    exact hbase.eventually (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  have hfinal : Filter.Tendsto f Filter.atTop (nhds 1) := by
    refine hexp.congr' ?_
    filter_upwards [hpos] with x hx
    simp only [f]
    have hrpow :
        Real.rpow
            ((x ^ 2 + 2 * x - 1) / (2 * x ^ 2 - 3 * x - 2))
            (1 / x) =
          Real.exp
            (Real.log
                ((x ^ 2 + 2 * x - 1) / (2 * x ^ 2 - 3 * x - 2)) *
              (1 / x)) := by
      exact Real.rpow_def_of_pos hx (1 / x)
    exact hrpow.symm
  simpa only [pow_zero] using hfinal

/-- Exercise 513, gap 2. -/
theorem gap2 : (1 / 2 : ℝ) ^ (0 : ℕ) = 1 := by
  norm_num

/-- Exercise 513, gap 3. -/
theorem gap3 : Filter.Tendsto f Filter.atTop (nhds 1) := by
  simpa only [pow_zero] using gap1

end

end ProofGap.Exercise513
