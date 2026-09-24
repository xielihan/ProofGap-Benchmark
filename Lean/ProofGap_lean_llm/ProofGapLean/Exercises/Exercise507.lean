import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise507

noncomputable section

def f (x : ℝ) : ℝ := Real.rpow ((x + 2) / (2 * x - 1)) (x ^ 2)

/-- Source: `proof_gap/exercise_507/1.txt`; interpret the variable exponent by `Real.rpow`. -/
theorem gap1 : Filter.Tendsto f Filter.atTop (nhds 0) := by
  let c : ℝ := Real.log (2 / 3 : ℝ)
  have hc : c < 0 := by
    dsimp [c]
    exact Real.log_neg (by norm_num) (by norm_num)
  have hexp :
      Filter.Tendsto
        (fun x : ℝ => Real.log ((x + 2) / (2 * x - 1)) * x ^ 2)
        Filter.atTop Filter.atBot := by
    refine Filter.tendsto_atBot.2 ?_
    intro b
    filter_upwards [Filter.eventually_ge_atTop
      (max (8 : ℝ) ((-b) / (-c)))] with x hx
    have hx8 : (8 : ℝ) ≤ x :=
      le_trans (le_max_left _ _) hx
    have hden : 0 < 2 * x - 1 := by
      nlinarith
    have hnum : 0 < x + 2 := by
      nlinarith
    have hbasepos : 0 < (x + 2) / (2 * x - 1) :=
      div_pos hnum hden
    have hbasele : (x + 2) / (2 * x - 1) ≤ (2 / 3 : ℝ) := by
      exact (div_le_iff₀ hden).2 (by nlinarith)
    have hlogle :
        Real.log ((x + 2) / (2 * x - 1)) ≤ c := by
      have hmono := Real.strictMonoOn_log.monotoneOn
        hbasepos (show 0 < (2 / 3 : ℝ) by norm_num) hbasele
      simpa [c] using hmono
    have hthreshold : (-b) / (-c) ≤ x :=
      le_trans (le_max_right _ _) hx
    have hbx : -b ≤ x * (-c) :=
      (div_le_iff₀ (neg_pos.mpr hc)).1 hthreshold
    have hcx : c * x ≤ b := by
      nlinarith
    have hx0 : 0 ≤ x := by
      nlinarith
    have hx1 : 0 ≤ x - 1 := by
      nlinarith
    have hprod : 0 ≤ x * (x - 1) :=
      mul_nonneg hx0 hx1
    have hsq : x ≤ x ^ 2 := by
      nlinarith
    calc
      Real.log ((x + 2) / (2 * x - 1)) * x ^ 2
          ≤ c * x ^ 2 := mul_le_mul_of_nonneg_right hlogle (sq_nonneg x)
      _ ≤ c * x := mul_le_mul_of_nonpos_left hsq hc.le
      _ ≤ b := hcx
  refine (Real.tendsto_exp_atBot.comp hexp).congr' ?_
  filter_upwards [Filter.eventually_ge_atTop (8 : ℝ)] with x hx
  have hden : 0 < 2 * x - 1 := by
    nlinarith
  have hnum : 0 < x + 2 := by
    nlinarith
  have hbasepos : 0 < (x + 2) / (2 * x - 1) :=
    div_pos hnum hden
  simpa [Function.comp_def, f, Real.rpow_def_of_pos hbasepos]

end

end ProofGap.Exercise507
