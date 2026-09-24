import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open scoped Interval

namespace ProofGap.Exercise2452

noncomputable section

def angle (r : ℝ) : ℝ := (r + 1 / r) / 2

def radialDerivative (r : ℝ) : ℝ := r / (r - angle r)

def polarSpeed (r : ℝ) : ℝ :=
  Real.sqrt (r ^ 2 + radialDerivative r ^ 2)

def substitutedIntegrand (r : ℝ) : ℝ :=
  (r ^ 3 + r) / (r ^ 2 - 1) * ((r ^ 2 - 1) / r ^ 2)

def arcLength : ℝ :=
  1 / 2 * ∫ r in (1 : ℝ)..3, substitutedIntegrand r

theorem gap1 (r : ℝ) (hr : 1 ≤ r) :
    r ^ 2 - 2 * r * angle r + 1 = 0 := by
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  unfold angle
  field_simp [hr0.ne']
  <;> ring

theorem gap2 (r : ℝ) (hr : 1 < r) :
    2 * r * radialDerivative r -
        2 * angle r * radialDerivative r - 2 * r = 0 := by
  have hr0 : 0 < r := lt_trans zero_lt_one hr
  have hden_eq : r - angle r = (r ^ 2 - 1) / (2 * r) := by
    unfold angle
    field_simp [hr0.ne']
    <;> ring
  have hnum : 0 < r ^ 2 - 1 := by
    nlinarith [sq_nonneg (r - 1)]
  have hden : 0 < r - angle r := by
    rw [hden_eq]
    exact div_pos hnum (mul_pos (by norm_num) hr0)
  unfold radialDerivative
  field_simp [hden.ne']
  <;> ring

theorem gap3 (r : ℝ) :
    radialDerivative r = r / (r - angle r) := by
  rfl

theorem gap4 (r : ℝ) (hr : 1 < r) :
    polarSpeed r = r * angle r / (r - angle r) := by
  have hr0 : 0 < r := lt_trans zero_lt_one hr
  have hden_eq : r - angle r = (r ^ 2 - 1) / (2 * r) := by
    unfold angle
    field_simp [hr0.ne']
    <;> ring
  have hnum : 0 < r ^ 2 - 1 := by
    nlinarith [sq_nonneg (r - 1)]
  have hden : 0 < r - angle r := by
    rw [hden_eq]
    exact div_pos hnum (mul_pos (by norm_num) hr0)
  have ha : 0 < angle r := by
    unfold angle
    have hinv : 0 < 1 / r := one_div_pos.mpr hr0
    nlinarith
  have hqnonneg : 0 ≤ r * angle r / (r - angle r) :=
    le_of_lt (div_pos (mul_pos hr0 ha) hden)
  have hquad := gap1 r (le_of_lt hr)
  have hmul :
      r ^ 2 * (r ^ 2 - 2 * r * angle r + 1) = 0 := by
    rw [hquad]
    ring
  have hsq :
      r ^ 2 + radialDerivative r ^ 2 =
        (r * angle r / (r - angle r)) ^ 2 := by
    unfold radialDerivative
    field_simp [hden.ne']
    nlinarith [hmul]
  unfold polarSpeed
  rw [hsq, Real.sqrt_sq_eq_abs, abs_of_nonneg hqnonneg]

theorem gap5 (r : ℝ) (hr : 1 < r) :
    r * angle r / (r - angle r) = (r ^ 3 + r) / (r ^ 2 - 1) := by
  have hr0 : 0 < r := lt_trans zero_lt_one hr
  have hden_eq : r - angle r = (r ^ 2 - 1) / (2 * r) := by
    unfold angle
    field_simp [hr0.ne']
    <;> ring
  have hrsq : 0 < r ^ 2 - 1 := by
    nlinarith [sq_nonneg (r - 1)]
  rw [hden_eq]
  unfold angle
  field_simp [hr0.ne', hrsq.ne']
  <;> ring

theorem gap6 (r : ℝ) (hr : 1 < r) :
    polarSpeed r = (r ^ 3 + r) / (r ^ 2 - 1) := by
  calc
    polarSpeed r = r * angle r / (r - angle r) := gap4 r hr
    _ = (r ^ 3 + r) / (r ^ 2 - 1) := gap5 r hr

theorem gap7 (r : ℝ) (hr : r ≠ 0) :
    deriv angle r = 1 / 2 * (1 - 1 / r ^ 2) := by
  unfold angle
  have h :=
    (((hasDerivAt_id r).add
      ((hasDerivAt_const r (1 : ℝ)).div (hasDerivAt_id r) hr)).div_const 2)
  convert h.deriv using 1 <;> simp <;> field_simp [hr] <;> ring

theorem gap8 (s : ℝ) (hs : s = arcLength) :
    s = 1 / 2 * ∫ r in (1 : ℝ)..3, substitutedIntegrand r := by
  simpa [arcLength] using hs

theorem gap9 :
    1 / 2 * (∫ r in (1 : ℝ)..3, substitutedIntegrand r) =
      1 / 2 * ∫ r in (1 : ℝ)..3, (r + 1 / r) := by
  apply congrArg (fun x : ℝ => 1 / 2 * x)
  apply intervalIntegral.integral_congr_ae
  refine Filter.Eventually.of_forall (fun r hr => ?_)
  norm_num [Set.uIoc] at hr
  have hr0 : 0 < r := lt_trans zero_lt_one hr.1
  have hrsq : 0 < r ^ 2 - 1 := by
    nlinarith [sq_nonneg (r - 1)]
  unfold substitutedIntegrand
  field_simp [hr0.ne', hrsq.ne']
  <;> ring

theorem gap10 :
    1 / 2 * (∫ r in (1 : ℝ)..3, (r + 1 / r)) =
      2 + 1 / 2 * Real.log 3 := by
  let F : ℝ → ℝ := fun x => x ^ 2 / 2 + Real.log x
  have hderiv : ∀ x ∈ Set.uIcc (1 : ℝ) 3,
      HasDerivAt F (x + 1 / x) x := by
    intro x hx
    norm_num [Set.uIcc] at hx
    have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx.1
    dsimp [F]
    convert ((((hasDerivAt_id x).pow 2).div_const 2).add
      (Real.hasDerivAt_log hxpos.ne')) using 1 <;>
      simp <;> field_simp [hxpos.ne'] <;> ring
  have hcont : ContinuousOn (fun x : ℝ => x + 1 / x)
      (Set.uIcc (1 : ℝ) 3) := by
    intro x hx
    norm_num [Set.uIcc] at hx
    have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx.1
    exact (continuousAt_id.add
      (continuousAt_const.div continuousAt_id hxpos.ne')).continuousWithinAt
  have hint : IntervalIntegrable (fun x : ℝ => x + 1 / x)
      MeasureTheory.volume (1 : ℝ) 3 :=
    hcont.intervalIntegrable
  have hi :
      (∫ x in (1 : ℝ)..3, (x + 1 / x)) = F 3 - F 1 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [hi]
  dsimp [F]
  rw [Real.log_one]
  ring

theorem gap11 (s : ℝ) (hs : s = arcLength) :
    s = 2 + 1 / 2 * Real.log 3 := by
  rw [hs, arcLength, gap9, gap10]

end

end ProofGap.Exercise2452
