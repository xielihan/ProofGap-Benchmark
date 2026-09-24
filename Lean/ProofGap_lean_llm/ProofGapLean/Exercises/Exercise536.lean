import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

namespace ProofGap.Exercise536

noncomputable section

def original (x : ℝ) : ℝ :=
  Real.log (1 + Real.sqrt x + Real.rpow x (1 / 3 : ℝ)) /
    Real.log (1 + Real.rpow x (1 / 3 : ℝ) + Real.rpow x (1 / 4 : ℝ))
def expanded (x : ℝ) : ℝ :=
  ((1 / 2 : ℝ) * Real.log x +
    Real.log (Real.rpow x (-1 / 2 : ℝ) + 1 + Real.rpow x (-1 / 6 : ℝ))) /
  ((1 / 3 : ℝ) * Real.log x +
    Real.log (Real.rpow x (-1 / 3 : ℝ) + 1 + Real.rpow x (-1 / 12 : ℝ)))
def normalized (x : ℝ) : ℝ :=
  ((1 / 2 : ℝ) + (1 / Real.log x) *
    Real.log (Real.rpow x (-1 / 2 : ℝ) + 1 + Real.rpow x (-1 / 6 : ℝ))) /
  ((1 / 3 : ℝ) + (1 / Real.log x) *
    Real.log (Real.rpow x (-1 / 3 : ℝ) + 1 + Real.rpow x (-1 / 12 : ℝ)))
def HasLimitAtPosInfinity (f : ℝ → ℝ) (L : ℝ) : Prop :=
  Filter.Tendsto f Filter.atTop (nhds L)

/-- Exercise 536, gap 1. -/
theorem gap1 (L : ℝ) :
    HasLimitAtPosInfinity original L ↔ HasLimitAtPosInfinity expanded L := by
  unfold HasLimitAtPosInfinity
  have hEq : original =ᶠ[Filter.atTop] expanded := by
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with x hx
    have hrpow_pos (a : ℝ) : 0 < Real.rpow x a :=
      Real.rpow_pos_of_pos hx a
    have hhalf_inv :
        Real.rpow x (1 / 2 : ℝ) * Real.rpow x (-1 / 2 : ℝ) = 1 := by
      calc
        Real.rpow x (1 / 2 : ℝ) * Real.rpow x (-1 / 2 : ℝ) =
            Real.rpow x ((1 / 2 : ℝ) + (-1 / 2 : ℝ)) :=
          (Real.rpow_add hx _ _).symm
        _ = 1 := by norm_num
    have hhalf_sixth :
        Real.rpow x (1 / 2 : ℝ) * Real.rpow x (-1 / 6 : ℝ) =
          Real.rpow x (1 / 3 : ℝ) := by
      calc
        Real.rpow x (1 / 2 : ℝ) * Real.rpow x (-1 / 6 : ℝ) =
            Real.rpow x ((1 / 2 : ℝ) + (-1 / 6 : ℝ)) :=
          (Real.rpow_add hx _ _).symm
        _ = Real.rpow x (1 / 3 : ℝ) := by norm_num
    have hthird_inv :
        Real.rpow x (1 / 3 : ℝ) * Real.rpow x (-1 / 3 : ℝ) = 1 := by
      calc
        Real.rpow x (1 / 3 : ℝ) * Real.rpow x (-1 / 3 : ℝ) =
            Real.rpow x ((1 / 3 : ℝ) + (-1 / 3 : ℝ)) :=
          (Real.rpow_add hx _ _).symm
        _ = 1 := by norm_num
    have hthird_twelfth :
        Real.rpow x (1 / 3 : ℝ) * Real.rpow x (-1 / 12 : ℝ) =
          Real.rpow x (1 / 4 : ℝ) := by
      calc
        Real.rpow x (1 / 3 : ℝ) * Real.rpow x (-1 / 12 : ℝ) =
            Real.rpow x ((1 / 3 : ℝ) + (-1 / 12 : ℝ)) :=
          (Real.rpow_add hx _ _).symm
        _ = Real.rpow x (1 / 4 : ℝ) := by norm_num
    have hnum_factor :
        1 + Real.sqrt x + Real.rpow x (1 / 3 : ℝ) =
          Real.rpow x (1 / 2 : ℝ) *
            (Real.rpow x (-1 / 2 : ℝ) + 1 +
              Real.rpow x (-1 / 6 : ℝ)) := by
      calc
        1 + Real.sqrt x + Real.rpow x (1 / 3 : ℝ) =
            1 + Real.rpow x (1 / 2 : ℝ) + Real.rpow x (1 / 3 : ℝ) := by
          rw [Real.sqrt_eq_rpow]
          norm_num
        _ = Real.rpow x (1 / 2 : ℝ) * Real.rpow x (-1 / 2 : ℝ) +
              Real.rpow x (1 / 2 : ℝ) +
              Real.rpow x (1 / 2 : ℝ) * Real.rpow x (-1 / 6 : ℝ) := by
          rw [hhalf_inv, hhalf_sixth]
        _ = Real.rpow x (1 / 2 : ℝ) *
              (Real.rpow x (-1 / 2 : ℝ) + 1 +
                Real.rpow x (-1 / 6 : ℝ)) := by ring
    have hden_factor :
        1 + Real.rpow x (1 / 3 : ℝ) + Real.rpow x (1 / 4 : ℝ) =
          Real.rpow x (1 / 3 : ℝ) *
            (Real.rpow x (-1 / 3 : ℝ) + 1 +
              Real.rpow x (-1 / 12 : ℝ)) := by
      calc
        1 + Real.rpow x (1 / 3 : ℝ) + Real.rpow x (1 / 4 : ℝ) =
            Real.rpow x (1 / 3 : ℝ) * Real.rpow x (-1 / 3 : ℝ) +
              Real.rpow x (1 / 3 : ℝ) +
              Real.rpow x (1 / 3 : ℝ) * Real.rpow x (-1 / 12 : ℝ) := by
          rw [hthird_inv, hthird_twelfth]
        _ = Real.rpow x (1 / 3 : ℝ) *
              (Real.rpow x (-1 / 3 : ℝ) + 1 +
                Real.rpow x (-1 / 12 : ℝ)) := by ring
    have hnum_bracket :
        0 < Real.rpow x (-1 / 2 : ℝ) + 1 +
          Real.rpow x (-1 / 6 : ℝ) :=
      add_pos (add_pos (hrpow_pos _) zero_lt_one) (hrpow_pos _)
    have hden_bracket :
        0 < Real.rpow x (-1 / 3 : ℝ) + 1 +
          Real.rpow x (-1 / 12 : ℝ) :=
      add_pos (add_pos (hrpow_pos _) zero_lt_one) (hrpow_pos _)
    have hlog_rpow (a : ℝ) :
        Real.log (Real.rpow x a) = a * Real.log x := by
      change Real.log (x ^ a) = a * Real.log x
      rw [Real.rpow_def_of_pos hx, Real.log_exp]
      ring
    have hnum_log :
        Real.log (1 + Real.sqrt x + Real.rpow x (1 / 3 : ℝ)) =
          (1 / 2 : ℝ) * Real.log x +
            Real.log (Real.rpow x (-1 / 2 : ℝ) + 1 +
              Real.rpow x (-1 / 6 : ℝ)) := by
      calc
        Real.log (1 + Real.sqrt x + Real.rpow x (1 / 3 : ℝ)) =
            Real.log (Real.rpow x (1 / 2 : ℝ) *
              (Real.rpow x (-1 / 2 : ℝ) + 1 +
                Real.rpow x (-1 / 6 : ℝ))) := by rw [hnum_factor]
        _ = Real.log (Real.rpow x (1 / 2 : ℝ)) +
              Real.log (Real.rpow x (-1 / 2 : ℝ) + 1 +
                Real.rpow x (-1 / 6 : ℝ)) := by
          rw [Real.log_mul (ne_of_gt (hrpow_pos _)) (ne_of_gt hnum_bracket)]
        _ = (1 / 2 : ℝ) * Real.log x +
              Real.log (Real.rpow x (-1 / 2 : ℝ) + 1 +
                Real.rpow x (-1 / 6 : ℝ)) := by
          rw [hlog_rpow]
    have hden_log :
        Real.log (1 + Real.rpow x (1 / 3 : ℝ) + Real.rpow x (1 / 4 : ℝ)) =
          (1 / 3 : ℝ) * Real.log x +
            Real.log (Real.rpow x (-1 / 3 : ℝ) + 1 +
              Real.rpow x (-1 / 12 : ℝ)) := by
      calc
        Real.log (1 + Real.rpow x (1 / 3 : ℝ) + Real.rpow x (1 / 4 : ℝ)) =
            Real.log (Real.rpow x (1 / 3 : ℝ) *
              (Real.rpow x (-1 / 3 : ℝ) + 1 +
                Real.rpow x (-1 / 12 : ℝ))) := by rw [hden_factor]
        _ = Real.log (Real.rpow x (1 / 3 : ℝ)) +
              Real.log (Real.rpow x (-1 / 3 : ℝ) + 1 +
                Real.rpow x (-1 / 12 : ℝ)) := by
          rw [Real.log_mul (ne_of_gt (hrpow_pos _)) (ne_of_gt hden_bracket)]
        _ = (1 / 3 : ℝ) * Real.log x +
              Real.log (Real.rpow x (-1 / 3 : ℝ) + 1 +
                Real.rpow x (-1 / 12 : ℝ)) := by
          rw [hlog_rpow]
    unfold original expanded
    rw [hnum_log, hden_log]
  constructor
  · intro h
    exact h.congr' hEq
  · intro h
    exact h.congr' hEq.symm

/-- Exercise 536, gap 2. -/
theorem gap2 : HasLimitAtPosInfinity normalized (3 / 2) := by
  unfold HasLimitAtPosInfinity
  have hscale_atBot (a : ℝ) (ha : 0 < a) :
      Filter.Tendsto (fun y : ℝ => -a * y)
        Filter.atTop Filter.atBot := by
    refine Filter.tendsto_atBot.2 ?_
    intro b
    filter_upwards [Filter.eventually_ge_atTop ((-b) / a)] with y hy
    calc
      -a * y ≤ -a * ((-b) / a) :=
        mul_le_mul_of_nonpos_left hy (neg_nonpos.mpr (le_of_lt ha))
      _ = b := by
        field_simp [ne_of_gt ha] <;> ring
  have hrpow_neg_tendsto (a : ℝ) (ha : 0 < a) :
      Filter.Tendsto (fun x : ℝ => Real.rpow x (-a))
        Filter.atTop (nhds 0) := by
    have harg :
        Filter.Tendsto (fun x : ℝ => -a * Real.log x)
          Filter.atTop Filter.atBot :=
      (hscale_atBot a ha).comp Real.tendsto_log_atTop
    have hexp :
        Filter.Tendsto (fun x : ℝ => Real.exp (-a * Real.log x))
          Filter.atTop (nhds 0) :=
      Real.tendsto_exp_atBot.comp harg
    apply hexp.congr'
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with x hx
    symm
    change x ^ (-a) = Real.exp (-a * Real.log x)
    calc
      x ^ (-a) = Real.exp (Real.log x * (-a)) :=
        Real.rpow_def_of_pos hx (-a)
      _ = Real.exp (-a * Real.log x) := by ring_nf
  have hp_half :
      Filter.Tendsto (fun x : ℝ => Real.rpow x (-1 / 2 : ℝ))
        Filter.atTop (nhds 0) := by
    simpa only [neg_div] using
      (hrpow_neg_tendsto (1 / 2 : ℝ) (by norm_num))
  have hp_sixth :
      Filter.Tendsto (fun x : ℝ => Real.rpow x (-1 / 6 : ℝ))
        Filter.atTop (nhds 0) := by
    simpa only [neg_div] using
      (hrpow_neg_tendsto (1 / 6 : ℝ) (by norm_num))
  have hp_third :
      Filter.Tendsto (fun x : ℝ => Real.rpow x (-1 / 3 : ℝ))
        Filter.atTop (nhds 0) := by
    simpa only [neg_div] using
      (hrpow_neg_tendsto (1 / 3 : ℝ) (by norm_num))
  have hp_twelfth :
      Filter.Tendsto (fun x : ℝ => Real.rpow x (-1 / 12 : ℝ))
        Filter.atTop (nhds 0) := by
    simpa only [neg_div] using
      (hrpow_neg_tendsto (1 / 12 : ℝ) (by norm_num))
  have hone :
      Filter.Tendsto (fun _ : ℝ => (1 : ℝ)) Filter.atTop (nhds 1) :=
    tendsto_const_nhds
  have hs_num :
      Filter.Tendsto
        (fun x : ℝ => Real.rpow x (-1 / 2 : ℝ) + 1 +
          Real.rpow x (-1 / 6 : ℝ)) Filter.atTop (nhds 1) := by
    simpa only [zero_add, add_zero] using (hp_half.add hone).add hp_sixth
  have hs_den :
      Filter.Tendsto
        (fun x : ℝ => Real.rpow x (-1 / 3 : ℝ) + 1 +
          Real.rpow x (-1 / 12 : ℝ)) Filter.atTop (nhds 1) := by
    simpa only [zero_add, add_zero] using (hp_third.add hone).add hp_twelfth
  have hlog_num :
      Filter.Tendsto
        (fun x : ℝ => Real.log (Real.rpow x (-1 / 2 : ℝ) + 1 +
          Real.rpow x (-1 / 6 : ℝ))) Filter.atTop (nhds 0) := by
    simpa using
      (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hs_num
  have hlog_den :
      Filter.Tendsto
        (fun x : ℝ => Real.log (Real.rpow x (-1 / 3 : ℝ) + 1 +
          Real.rpow x (-1 / 12 : ℝ))) Filter.atTop (nhds 0) := by
    simpa using
      (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hs_den
  have hinv_log :
      Filter.Tendsto (fun x : ℝ => 1 / Real.log x)
        Filter.atTop (nhds 0) := by
    simpa only [one_div] using
      ((tendsto_inv_atTop_zero :
          Filter.Tendsto (fun y : ℝ => y⁻¹) Filter.atTop (nhds 0)).comp
        Real.tendsto_log_atTop)
  have hsmall_num :
      Filter.Tendsto
        (fun x : ℝ => (1 / Real.log x) *
          Real.log (Real.rpow x (-1 / 2 : ℝ) + 1 +
            Real.rpow x (-1 / 6 : ℝ))) Filter.atTop (nhds 0) := by
    simpa using hinv_log.mul hlog_num
  have hsmall_den :
      Filter.Tendsto
        (fun x : ℝ => (1 / Real.log x) *
          Real.log (Real.rpow x (-1 / 3 : ℝ) + 1 +
            Real.rpow x (-1 / 12 : ℝ))) Filter.atTop (nhds 0) := by
    simpa using hinv_log.mul hlog_den
  have hhalf :
      Filter.Tendsto (fun _ : ℝ => (1 / 2 : ℝ))
        Filter.atTop (nhds (1 / 2 : ℝ)) :=
    tendsto_const_nhds
  have hthird :
      Filter.Tendsto (fun _ : ℝ => (1 / 3 : ℝ))
        Filter.atTop (nhds (1 / 3 : ℝ)) :=
    tendsto_const_nhds
  have hnum :
      Filter.Tendsto
        (fun x : ℝ => (1 / 2 : ℝ) + (1 / Real.log x) *
          Real.log (Real.rpow x (-1 / 2 : ℝ) + 1 +
            Real.rpow x (-1 / 6 : ℝ))) Filter.atTop (nhds (1 / 2 : ℝ)) := by
    simpa using hhalf.add hsmall_num
  have hden :
      Filter.Tendsto
        (fun x : ℝ => (1 / 3 : ℝ) + (1 / Real.log x) *
          Real.log (Real.rpow x (-1 / 3 : ℝ) + 1 +
            Real.rpow x (-1 / 12 : ℝ))) Filter.atTop (nhds (1 / 3 : ℝ)) := by
    simpa using hthird.add hsmall_den
  have hquot :
      Filter.Tendsto
        (fun x : ℝ =>
          ((1 / 2 : ℝ) + (1 / Real.log x) *
            Real.log (Real.rpow x (-1 / 2 : ℝ) + 1 +
              Real.rpow x (-1 / 6 : ℝ))) /
          ((1 / 3 : ℝ) + (1 / Real.log x) *
            Real.log (Real.rpow x (-1 / 3 : ℝ) + 1 +
              Real.rpow x (-1 / 12 : ℝ))))
        Filter.atTop (nhds (3 / 2 : ℝ)) := by
    convert hnum.div hden (by norm_num : (1 / 3 : ℝ) ≠ 0) using 1 <;> norm_num
  change Filter.Tendsto
    (fun x : ℝ =>
      ((1 / 2 : ℝ) + (1 / Real.log x) *
        Real.log (Real.rpow x (-1 / 2 : ℝ) + 1 +
          Real.rpow x (-1 / 6 : ℝ))) /
      ((1 / 3 : ℝ) + (1 / Real.log x) *
        Real.log (Real.rpow x (-1 / 3 : ℝ) + 1 +
          Real.rpow x (-1 / 12 : ℝ))))
    Filter.atTop (nhds (3 / 2 : ℝ))
  exact hquot

end

end ProofGap.Exercise536
