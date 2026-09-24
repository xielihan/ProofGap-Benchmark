import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise568

noncomputable section

def original (x : ℝ) : ℝ :=
  (x + 2) * Real.log (x + 2) - 2 * (x + 1) * Real.log (x + 1) +
    x * Real.log x
def logPowerRatio (x : ℝ) : ℝ :=
  Real.log ((Real.rpow (x + 2) (x + 2) * Real.rpow x x) /
    Real.rpow (x + 1) (2 * x + 2))
def normalized (x : ℝ) : ℝ :=
  Real.log (Real.rpow (1 + 2 / x) (x + 2) /
    Real.rpow (1 + 1 / x) (2 * x + 2))
def HasLimitAtPosInfinity (f : ℝ → ℝ) (L : ℝ) : Prop :=
  Filter.Tendsto f Filter.atTop (nhds L)

/-- Source: `proof_gap/exercise_568/1.txt`. -/
private theorem eventual_original_forms :
    (original =ᶠ[Filter.atTop] logPowerRatio) ∧
      (original =ᶠ[Filter.atTop] normalized) := by
  constructor
  · filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with x hx
    have hx1 : 0 < x + 1 := by positivity
    have hx2 : 0 < x + 2 := by positivity
    dsimp [original, logPowerRatio]
    rw [Real.log_div (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity),
      Real.log_rpow hx2, Real.log_rpow hx, Real.log_rpow hx1]
    ring
  · filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with x hx
    have hx0 : x ≠ 0 := ne_of_gt hx
    have hx1 : 0 < x + 1 := by positivity
    have hx2 : 0 < x + 2 := by positivity
    have hp1 : 0 < 1 + 1 / x := by positivity
    have hp2 : 0 < 1 + 2 / x := by positivity
    have hone : 1 + 1 / x = (x + 1) / x := by
      field_simp [hx0]
    have htwo : 1 + 2 / x = (x + 2) / x := by
      field_simp [hx0]
    dsimp [original, normalized]
    rw [Real.log_div (by positivity) (by positivity),
      Real.log_rpow hp2, Real.log_rpow hp1, htwo, hone,
      Real.log_div (by positivity) (by positivity),
      Real.log_div (by positivity) (by positivity)]
    ring

theorem gap1 (L : ℝ) :
    HasLimitAtPosInfinity original L ↔ HasLimitAtPosInfinity logPowerRatio L := by
  unfold HasLimitAtPosInfinity
  exact Filter.tendsto_congr' eventual_original_forms.1

/-- Source: `proof_gap/exercise_568/2.txt`. -/
theorem gap2 (L : ℝ) :
    HasLimitAtPosInfinity logPowerRatio L ↔ HasLimitAtPosInfinity normalized L := by
  unfold HasLimitAtPosInfinity
  exact Filter.tendsto_congr'
    ((eventual_original_forms.1).symm.trans eventual_original_forms.2)

/-- Source: `proof_gap/exercise_568/3.txt`. -/
theorem gap3 :
    HasLimitAtPosInfinity normalized (Real.log (Real.exp 2 / Real.exp 2)) := by
  unfold HasLimitAtPosInfinity
  have hzero (a : ℝ) :
      Filter.Tendsto (fun x : ℝ => a / x) Filter.atTop (nhds 0) := by
    simpa using
      (tendsto_const_nhds.div_atTop
        (Filter.tendsto_id :
          Filter.Tendsto (fun x : ℝ => x) Filter.atTop Filter.atTop))
  have hbase (a : ℝ) :
      Filter.Tendsto (fun x : ℝ => 1 + a / x)
        Filter.atTop (nhds 1) := by
    simpa using tendsto_const_nhds.add (hzero a)
  have hsmall (a : ℝ) (ha : a ≠ 0) :
      Filter.Tendsto (fun x : ℝ => a / x) Filter.atTop
        (nhdsWithin 0 ({0}ᶜ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨hzero a, ?_⟩
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with x hx
    simpa using div_ne_zero ha (ne_of_gt hx)
  have hlogSlope :
      Filter.Tendsto (fun t : ℝ => Real.log (1 + t) / t)
        (nhdsWithin 0 ({0}ᶜ)) (nhds 1) := by
    simpa [Real.log_one, div_eq_mul_inv, mul_comm] using
      (Real.hasDerivAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto_slope_zero
  have hscaled (a : ℝ) (ha : 0 < a) :
      Filter.Tendsto (fun x : ℝ => x * Real.log (1 + a / x))
        Filter.atTop (nhds a) := by
    have hratio :
        Filter.Tendsto
          (fun x : ℝ => Real.log (1 + a / x) / (a / x))
          Filter.atTop (nhds 1) := by
      simpa [Function.comp_def] using
        hlogSlope.comp (hsmall a (ne_of_gt ha))
    have hproduct :
        Filter.Tendsto
          (fun x : ℝ => a * (Real.log (1 + a / x) / (a / x)))
          Filter.atTop (nhds a) := by
      simpa using tendsto_const_nhds.mul hratio
    have heq :
        (fun x : ℝ => x * Real.log (1 + a / x)) =ᶠ[Filter.atTop]
          (fun x : ℝ => a * (Real.log (1 + a / x) / (a / x))) := by
      filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with x hx
      field_simp [ne_of_gt ha, ne_of_gt hx]
    exact (Filter.tendsto_congr' heq).mpr hproduct
  have hlogbase (a : ℝ) :
      Filter.Tendsto (fun x : ℝ => Real.log (1 + a / x))
        Filter.atTop (nhds 0) := by
    have h :=
      (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp
        (hbase a)
    simpa using h
  have hnum :
      Filter.Tendsto
        (fun x : ℝ => (x + 2) * Real.log (1 + 2 / x))
        Filter.atTop (nhds 2) := by
    simpa [add_mul] using
      (hscaled 2 (by norm_num)).add
        (tendsto_const_nhds.mul (hlogbase 2))
  have hden :
      Filter.Tendsto
        (fun x : ℝ => (2 * x + 2) * Real.log (1 + 1 / x))
        Filter.atTop (nhds 2) := by
    simpa [add_mul, mul_assoc] using
      (tendsto_const_nhds.mul (hscaled 1 (by norm_num))).add
        (tendsto_const_nhds.mul (hlogbase 1))
  have heq :
      normalized =ᶠ[Filter.atTop]
        (fun x : ℝ =>
          (x + 2) * Real.log (1 + 2 / x) -
            (2 * x + 2) * Real.log (1 + 1 / x)) := by
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with x hx
    have hp1 : 0 < 1 + 1 / x := by positivity
    have hp2 : 0 < 1 + 2 / x := by positivity
    dsimp [normalized]
    rw [Real.log_div (by positivity) (by positivity),
      Real.log_rpow hp2, Real.log_rpow hp1]
  have hz :
      Filter.Tendsto normalized Filter.atTop (nhds 0) := by
    apply (Filter.tendsto_congr' heq).mpr
    simpa using hnum.sub hden
  have hconst : Real.log (Real.exp 2 / Real.exp 2) = 0 := by
    rw [div_self (Real.exp_ne_zero 2), Real.log_one]
  rw [hconst]
  exact hz

/-- Source: `proof_gap/exercise_568/4.txt`. -/
theorem gap4 : Real.log (Real.exp 2 / Real.exp 2) = 0 := by
  rw [div_self (Real.exp_ne_zero 2), Real.log_one]

/-- Source: `proof_gap/exercise_568/5.txt`. -/
theorem gap5 : HasLimitAtPosInfinity logPowerRatio 0 := by
  have hn : HasLimitAtPosInfinity normalized 0 := by
    simpa [gap4] using gap3
  exact (gap2 0).mpr hn

end

end ProofGap.Exercise568
