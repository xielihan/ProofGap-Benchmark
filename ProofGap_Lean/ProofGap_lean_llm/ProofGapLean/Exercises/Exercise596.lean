import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise596

noncomputable section

def f (x : ℝ) : ℝ := 1 / (1 + Real.exp (1 / x))
def leftFilter : Filter ℝ := nhdsWithin 0 (Set.Iio 0)
def rightFilter : Filter ℝ := nhdsWithin 0 (Set.Ioi 0)

/-- Exercise 596, gap 1. -/
theorem gap1 : Filter.Tendsto f leftFilter (nhds 1) := by
  unfold f
  have hinv :
      Filter.Tendsto (fun x : ℝ => 1 / x) leftFilter Filter.atBot := by
    simpa only [leftFilter, one_div] using
      (tendsto_inv_nhdsLT_zero :
        Filter.Tendsto (fun x : ℝ => x⁻¹)
          (nhdsWithin 0 (Set.Iio 0)) Filter.atBot)
  have hexp :
      Filter.Tendsto (fun x : ℝ => Real.exp (1 / x)) leftFilter (nhds 0) :=
    Real.tendsto_exp_atBot.comp hinv
  have hone :
      Filter.Tendsto (fun _ : ℝ => (1 : ℝ)) leftFilter (nhds 1) :=
    tendsto_const_nhds
  have hquot :=
    hone.div (hone.add hexp) (by positivity : (1 : ℝ) + 0 ≠ 0)
  change
    Filter.Tendsto
      (fun x : ℝ => 1 / (1 + Real.exp (1 / x)))
      leftFilter (nhds ((1 : ℝ) / (1 + 0))) at hquot
  simpa only [add_zero, div_one] using hquot

/-- Exercise 596, gap 2. -/
theorem gap2 : Filter.Tendsto f rightFilter (nhds 0) := by
  have hinv :
      Filter.Tendsto (fun x : ℝ => 1 / x) rightFilter Filter.atTop := by
    simpa only [rightFilter, one_div] using
      (tendsto_inv_nhdsGT_zero :
        Filter.Tendsto (fun x : ℝ => x⁻¹)
          (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop)
  have hneg :
      Filter.Tendsto (fun x : ℝ => -(1 / x)) rightFilter Filter.atBot := by
    refine Filter.tendsto_atBot.2 fun b => ?_
    filter_upwards [Filter.tendsto_atTop.1 hinv (-b)] with x hx
    simpa only [neg_neg] using (neg_le_neg hx)
  have hsmall :
      Filter.Tendsto (fun x : ℝ => Real.exp (-(1 / x))) rightFilter (nhds 0) :=
    Real.tendsto_exp_atBot.comp hneg
  have hone :
      Filter.Tendsto (fun _ : ℝ => (1 : ℝ)) rightFilter (nhds 1) :=
    tendsto_const_nhds
  have hratio :
      Filter.Tendsto
        (fun x : ℝ =>
          Real.exp (-(1 / x)) / (1 + Real.exp (-(1 / x))))
        rightFilter (nhds 0) := by
    simpa using
      hsmall.div (hone.add hsmall) (by positivity : (1 : ℝ) + 0 ≠ 0)
  have hf :
      f = fun x : ℝ =>
        Real.exp (-(1 / x)) / (1 + Real.exp (-(1 / x))) := by
    funext x
    unfold f
    apply (div_eq_div_iff (by positivity) (by positivity)).2
    rw [Real.exp_neg]
    field_simp [Real.exp_ne_zero] <;> ring
  rw [hf]
  exact hratio

end

end ProofGap.Exercise596
