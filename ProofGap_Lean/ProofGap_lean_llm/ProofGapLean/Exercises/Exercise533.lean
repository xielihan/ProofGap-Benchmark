import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise533

noncomputable section

def original (x : ℝ) : ℝ :=
  Real.log (x ^ 2 - x + 1) / Real.log (x ^ 10 + x + 1)
def expanded (x : ℝ) : ℝ :=
  (2 * Real.log x + Real.log (1 - 1 / x + 1 / x ^ 2)) /
    (10 * Real.log x + Real.log (1 + 1 / x ^ 9 + 1 / x ^ 10))
def normalized (x : ℝ) : ℝ :=
  (2 + (1 / Real.log x) * Real.log (1 + 1 / x ^ 2 - 1 / x)) /
    (10 + (1 / Real.log x) * Real.log (1 + 1 / x ^ 9 + 1 / x ^ 10))
def HasLimitAtPosInfinity (f : ℝ → ℝ) (L : ℝ) : Prop :=
  Filter.Tendsto f Filter.atTop (nhds L)

/-- Exercise 533, gap 1. -/
theorem gap1 (L : ℝ) :
    HasLimitAtPosInfinity original L ↔ HasLimitAtPosInfinity expanded L := by
  unfold HasLimitAtPosInfinity
  have heq : original =ᶠ[Filter.atTop] expanded := by
    filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with x hx
    have hxpos : 0 < x := lt_trans (by norm_num) hx
    have hx0 : x ≠ 0 := ne_of_gt hxpos
    have hfac2 :
        x ^ 2 - x + 1 = x ^ 2 * (1 - 1 / x + 1 / x ^ 2) := by
      field_simp [hx0]
    have hquad : 0 < x ^ 2 - x + 1 := by
      nlinarith [sq_nonneg (x - (1 / 2 : ℝ))]
    have hinner2 : 1 - 1 / x + 1 / x ^ 2 ≠ 0 := by
      intro hz
      apply (ne_of_gt hquad)
      calc
        x ^ 2 - x + 1 = x ^ 2 * (1 - 1 / x + 1 / x ^ 2) := hfac2
        _ = 0 := by rw [hz, mul_zero]
    have hfac10 :
        x ^ 10 + x + 1 =
          x ^ 10 * (1 + 1 / x ^ 9 + 1 / x ^ 10) := by
      field_simp [hx0]
    have hfrac9 : 0 < 1 / x ^ 9 :=
      div_pos (by norm_num) (pow_pos hxpos 9)
    have hfrac10 : 0 < 1 / x ^ 10 :=
      div_pos (by norm_num) (pow_pos hxpos 10)
    have hinner10 : 1 + 1 / x ^ 9 + 1 / x ^ 10 ≠ 0 := by
      apply ne_of_gt
      nlinarith
    have hlog2 :
        Real.log (x ^ 2 - x + 1) =
          2 * Real.log x + Real.log (1 - 1 / x + 1 / x ^ 2) := by
      calc
        Real.log (x ^ 2 - x + 1) =
            Real.log (x ^ 2 * (1 - 1 / x + 1 / x ^ 2)) :=
          congrArg Real.log hfac2
        _ = Real.log (x ^ 2) + Real.log (1 - 1 / x + 1 / x ^ 2) :=
          Real.log_mul (pow_ne_zero 2 hx0) hinner2
        _ = 2 * Real.log x + Real.log (1 - 1 / x + 1 / x ^ 2) := by
          rw [Real.log_pow]
          norm_num
    have hlog10 :
        Real.log (x ^ 10 + x + 1) =
          10 * Real.log x + Real.log (1 + 1 / x ^ 9 + 1 / x ^ 10) := by
      calc
        Real.log (x ^ 10 + x + 1) =
            Real.log (x ^ 10 * (1 + 1 / x ^ 9 + 1 / x ^ 10)) :=
          congrArg Real.log hfac10
        _ = Real.log (x ^ 10) + Real.log (1 + 1 / x ^ 9 + 1 / x ^ 10) :=
          Real.log_mul (pow_ne_zero 10 hx0) hinner10
        _ = 10 * Real.log x + Real.log (1 + 1 / x ^ 9 + 1 / x ^ 10) := by
          rw [Real.log_pow]
          norm_num
    unfold original expanded
    rw [hlog2, hlog10]
  constructor
  · intro h
    exact h.congr' heq
  · intro h
    exact h.congr' heq.symm

/-- Exercise 533, gap 2. -/
theorem gap2 : HasLimitAtPosInfinity normalized (1 / 5) := by
  unfold HasLimitAtPosInfinity normalized
  have hinv :
      Filter.Tendsto (fun x : ℝ => 1 / x) Filter.atTop (nhds 0) := by
    simpa only [one_div] using
      (tendsto_inv_atTop_zero :
        Filter.Tendsto (fun x : ℝ => x⁻¹) Filter.atTop (nhds 0))
  have hone :
      Filter.Tendsto (fun _ : ℝ => (1 : ℝ)) Filter.atTop (nhds 1) :=
    tendsto_const_nhds
  have harg2 :
      Filter.Tendsto (fun x : ℝ => 1 + 1 / x ^ 2 - 1 / x)
        Filter.atTop (nhds 1) := by
    simpa [one_div, inv_pow] using (hone.add (hinv.pow 2)).sub hinv
  have harg10 :
      Filter.Tendsto (fun x : ℝ => 1 + 1 / x ^ 9 + 1 / x ^ 10)
        Filter.atTop (nhds 1) := by
    simpa [one_div, inv_pow] using
      (hone.add (hinv.pow 9)).add (hinv.pow 10)
  have hlog2 :
      Filter.Tendsto
        (fun x : ℝ => Real.log (1 + 1 / x ^ 2 - 1 / x))
        Filter.atTop (nhds 0) := by
    simpa using
      (Filter.Tendsto.comp
        (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)) harg2)
  have hlog10 :
      Filter.Tendsto
        (fun x : ℝ => Real.log (1 + 1 / x ^ 9 + 1 / x ^ 10))
        Filter.atTop (nhds 0) := by
    simpa using
      (Filter.Tendsto.comp
        (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)) harg10)
  have hinvlog :
      Filter.Tendsto (fun x : ℝ => 1 / Real.log x)
        Filter.atTop (nhds 0) := by
    simpa only [one_div, Function.comp_apply] using
      (Filter.Tendsto.comp
        (tendsto_inv_atTop_zero :
          Filter.Tendsto (fun y : ℝ => y⁻¹) Filter.atTop (nhds 0))
        Real.tendsto_log_atTop)
  have hsmall2 :
      Filter.Tendsto
        (fun x : ℝ =>
          (1 / Real.log x) * Real.log (1 + 1 / x ^ 2 - 1 / x))
        Filter.atTop (nhds 0) := by
    simpa using hinvlog.mul hlog2
  have hsmall10 :
      Filter.Tendsto
        (fun x : ℝ =>
          (1 / Real.log x) * Real.log (1 + 1 / x ^ 9 + 1 / x ^ 10))
        Filter.atTop (nhds 0) := by
    simpa using hinvlog.mul hlog10
  have htwo :
      Filter.Tendsto (fun _ : ℝ => (2 : ℝ)) Filter.atTop (nhds 2) :=
    tendsto_const_nhds
  have hten :
      Filter.Tendsto (fun _ : ℝ => (10 : ℝ)) Filter.atTop (nhds 10) :=
    tendsto_const_nhds
  have hnum :
      Filter.Tendsto
        (fun x : ℝ =>
          2 + (1 / Real.log x) * Real.log (1 + 1 / x ^ 2 - 1 / x))
        Filter.atTop (nhds 2) := by
    simpa using htwo.add hsmall2
  have hden :
      Filter.Tendsto
        (fun x : ℝ =>
          10 + (1 / Real.log x) * Real.log (1 + 1 / x ^ 9 + 1 / x ^ 10))
        Filter.atTop (nhds 10) := by
    simpa using hten.add hsmall10
  convert hnum.div hden (by norm_num : (10 : ℝ) ≠ 0) using 1 <;> norm_num

end

end ProofGap.Exercise533
