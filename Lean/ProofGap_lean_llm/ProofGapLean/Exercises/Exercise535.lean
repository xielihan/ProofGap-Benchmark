import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise535

noncomputable section

def original (x : ℝ) : ℝ :=
  Real.log (2 + Real.exp (3 * x)) / Real.log (3 + Real.exp (2 * x))
def expanded (x : ℝ) : ℝ :=
  (3 * x + Real.log (2 * Real.exp (-3 * x) + 1)) /
    (2 * x + Real.log (3 * Real.exp (-2 * x) + 1))
def normalized (x : ℝ) : ℝ :=
  (3 + (1 / x) * Real.log (2 * Real.exp (-3 * x) + 1)) /
    (2 + (1 / x) * Real.log (3 * Real.exp (-2 * x) + 1))
def HasLimitAtPosInfinity (f : ℝ → ℝ) (L : ℝ) : Prop :=
  Filter.Tendsto f Filter.atTop (nhds L)

/-- Exercise 535, gap 1. -/
theorem gap1 (L : ℝ) :
    HasLimitAtPosInfinity original L ↔ HasLimitAtPosInfinity expanded L := by
  have hfunctions : original = expanded := by
    funext x
    unfold original expanded
    have hmul3 :
        Real.exp (3 * x) * Real.exp (-3 * x) = 1 := by
      calc
        Real.exp (3 * x) * Real.exp (-3 * x) =
            Real.exp (3 * x + -3 * x) := (Real.exp_add _ _).symm
        _ = 1 := by
          rw [show 3 * x + -3 * x = 0 by ring, Real.exp_zero]
    have hfactor3 :
        2 + Real.exp (3 * x) =
          Real.exp (3 * x) * (2 * Real.exp (-3 * x) + 1) := by
      calc
        2 + Real.exp (3 * x) =
            2 * (Real.exp (3 * x) * Real.exp (-3 * x)) +
              Real.exp (3 * x) := by
                rw [hmul3]
                ring
        _ = Real.exp (3 * x) * (2 * Real.exp (-3 * x) + 1) := by
              ring
    have hpos3 : 0 < 2 * Real.exp (-3 * x) + 1 := by
      have he := Real.exp_pos (-3 * x)
      nlinarith
    have hlog3 :
        Real.log (2 + Real.exp (3 * x)) =
          3 * x + Real.log (2 * Real.exp (-3 * x) + 1) := by
      calc
        Real.log (2 + Real.exp (3 * x)) =
            Real.log
              (Real.exp (3 * x) * (2 * Real.exp (-3 * x) + 1)) :=
                congrArg Real.log hfactor3
        _ = Real.log (Real.exp (3 * x)) +
              Real.log (2 * Real.exp (-3 * x) + 1) :=
                Real.log_mul (Real.exp_ne_zero _) (ne_of_gt hpos3)
        _ = 3 * x + Real.log (2 * Real.exp (-3 * x) + 1) := by
              rw [Real.log_exp]
    have hmul2 :
        Real.exp (2 * x) * Real.exp (-2 * x) = 1 := by
      calc
        Real.exp (2 * x) * Real.exp (-2 * x) =
            Real.exp (2 * x + -2 * x) := (Real.exp_add _ _).symm
        _ = 1 := by
          rw [show 2 * x + -2 * x = 0 by ring, Real.exp_zero]
    have hfactor2 :
        3 + Real.exp (2 * x) =
          Real.exp (2 * x) * (3 * Real.exp (-2 * x) + 1) := by
      calc
        3 + Real.exp (2 * x) =
            3 * (Real.exp (2 * x) * Real.exp (-2 * x)) +
              Real.exp (2 * x) := by
                rw [hmul2]
                ring
        _ = Real.exp (2 * x) * (3 * Real.exp (-2 * x) + 1) := by
              ring
    have hpos2 : 0 < 3 * Real.exp (-2 * x) + 1 := by
      have he := Real.exp_pos (-2 * x)
      nlinarith
    have hlog2 :
        Real.log (3 + Real.exp (2 * x)) =
          2 * x + Real.log (3 * Real.exp (-2 * x) + 1) := by
      calc
        Real.log (3 + Real.exp (2 * x)) =
            Real.log
              (Real.exp (2 * x) * (3 * Real.exp (-2 * x) + 1)) :=
                congrArg Real.log hfactor2
        _ = Real.log (Real.exp (2 * x)) +
              Real.log (3 * Real.exp (-2 * x) + 1) :=
                Real.log_mul (Real.exp_ne_zero _) (ne_of_gt hpos2)
        _ = 2 * x + Real.log (3 * Real.exp (-2 * x) + 1) := by
              rw [Real.log_exp]
    rw [hlog3, hlog2]
  rw [hfunctions]

/-- Exercise 535, gap 2. -/
theorem gap2 : HasLimitAtPosInfinity normalized (3 / 2) := by
  have hlin3 :
      Filter.Tendsto (fun x : ℝ => -3 * x) Filter.atTop Filter.atBot := by
    refine Filter.tendsto_atBot.2 ?_
    intro b
    filter_upwards [Filter.eventually_ge_atTop (-b / 3)] with x hx
    linarith
  have hlin2 :
      Filter.Tendsto (fun x : ℝ => -2 * x) Filter.atTop Filter.atBot := by
    refine Filter.tendsto_atBot.2 ?_
    intro b
    filter_upwards [Filter.eventually_ge_atTop (-b / 2)] with x hx
    linarith
  have hexp3 :
      Filter.Tendsto (fun x : ℝ => Real.exp (-3 * x))
        Filter.atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp hlin3
  have hexp2 :
      Filter.Tendsto (fun x : ℝ => Real.exp (-2 * x))
        Filter.atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp hlin2
  have htwo :
      Filter.Tendsto (fun _ : ℝ => (2 : ℝ)) Filter.atTop (nhds 2) :=
    tendsto_const_nhds
  have hthree :
      Filter.Tendsto (fun _ : ℝ => (3 : ℝ)) Filter.atTop (nhds 3) :=
    tendsto_const_nhds
  have hone :
      Filter.Tendsto (fun _ : ℝ => (1 : ℝ)) Filter.atTop (nhds 1) :=
    tendsto_const_nhds
  have harg3 :
      Filter.Tendsto
        (fun x : ℝ => 2 * Real.exp (-3 * x) + 1)
        Filter.atTop (nhds 1) := by
    simpa using (htwo.mul hexp3).add hone
  have harg2 :
      Filter.Tendsto
        (fun x : ℝ => 3 * Real.exp (-2 * x) + 1)
        Filter.atTop (nhds 1) := by
    simpa using (hthree.mul hexp2).add hone
  have hlog3 :
      Filter.Tendsto
        (fun x : ℝ => Real.log (2 * Real.exp (-3 * x) + 1))
        Filter.atTop (nhds 0) := by
    simpa [Function.comp_def] using
      ((Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp harg3)
  have hlog2 :
      Filter.Tendsto
        (fun x : ℝ => Real.log (3 * Real.exp (-2 * x) + 1))
        Filter.atTop (nhds 0) := by
    simpa [Function.comp_def] using
      ((Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp harg2)
  have hinv :
      Filter.Tendsto (fun x : ℝ => 1 / x) Filter.atTop (nhds 0) := by
    simpa [one_div] using
      (tendsto_inv_atTop_zero :
        Filter.Tendsto (fun x : ℝ => x⁻¹) Filter.atTop (nhds 0))
  have hprod3 :
      Filter.Tendsto
        (fun x : ℝ => (1 / x) * Real.log (2 * Real.exp (-3 * x) + 1))
        Filter.atTop (nhds 0) := by
    simpa using hinv.mul hlog3
  have hprod2 :
      Filter.Tendsto
        (fun x : ℝ => (1 / x) * Real.log (3 * Real.exp (-2 * x) + 1))
        Filter.atTop (nhds 0) := by
    simpa using hinv.mul hlog2
  have hnum :
      Filter.Tendsto
        (fun x : ℝ => 3 + (1 / x) * Real.log (2 * Real.exp (-3 * x) + 1))
        Filter.atTop (nhds 3) := by
    simpa using hthree.add hprod3
  have hden :
      Filter.Tendsto
        (fun x : ℝ => 2 + (1 / x) * Real.log (3 * Real.exp (-2 * x) + 1))
        Filter.atTop (nhds 2) := by
    simpa using htwo.add hprod2
  unfold HasLimitAtPosInfinity normalized
  exact hnum.div hden (by norm_num : (2 : ℝ) ≠ 0)

end

end ProofGap.Exercise535
