import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

namespace ProofGap.Exercise574

noncomputable section

def sec (x : ℝ) : ℝ := 1 / Real.cos x
def original (x : ℝ) : ℝ :=
  Real.rpow (2 - x) (sec (Real.pi * x / 2))
def exponentialForm (x : ℝ) : ℝ :=
  Real.rpow (1 + (1 - x))
    ((1 / (1 - x)) *
      (Real.pi * (x - 1) /
        (2 * Real.sin (Real.pi * (x - 1) / 2))) *
      (2 / Real.pi))
def HasLimitAtOne (f : ℝ → ℝ) (L : ℝ) : Prop :=
  Filter.Tendsto f (nhdsWithin 1 ({1} : Set ℝ)ᶜ) (nhds L)

/-- Exercise 574, gap 1. -/
private theorem tendsto_log_sub_div_cos :
    Filter.Tendsto
      (fun x : ℝ =>
        Real.log (2 - x) / Real.cos (Real.pi * x / 2))
      (nhdsWithin 1 ({1} : Set ℝ)ᶜ) (nhds (2 / Real.pi)) := by
  have hf :
      HasDerivAt (fun x : ℝ => Real.log (2 - x)) (-1) 1 := by
    convert
      (Real.hasDerivAt_log
          (by norm_num : (2 - (1 : ℝ)) ≠ 0)).comp 1
        ((hasDerivAt_const (x := (1 : ℝ)) (2 : ℝ)).sub
          (hasDerivAt_id (𝕜 := ℝ) 1)) using 1 <;>
      norm_num
  have hg :
      HasDerivAt
        (fun x : ℝ => Real.cos (Real.pi * x / 2))
        (-Real.pi / 2) 1 := by
    convert
      (Real.hasDerivAt_cos (Real.pi * (1 : ℝ) / 2)).comp 1
        (((hasDerivAt_const (x := (1 : ℝ)) Real.pi).mul
          (hasDerivAt_id (𝕜 := ℝ) 1)).div_const 2) using 1 <;>
      norm_num [Real.sin_pi_div_two] <;> ring
  have hquot :
      Filter.Tendsto
        (fun x : ℝ =>
          slope (fun y : ℝ => Real.log (2 - y)) 1 x /
            slope (fun y : ℝ =>
              Real.cos (Real.pi * y / 2)) 1 x)
        (nhdsWithin 1 ({1} : Set ℝ)ᶜ)
        (nhds ((-1 : ℝ) / (-Real.pi / 2))) :=
    hf.tendsto_slope.div hg.tendsto_slope
      (div_ne_zero
        (neg_ne_zero.mpr (ne_of_gt Real.pi_pos))
        (by norm_num))
  have hquot' :
      Filter.Tendsto
        (fun x : ℝ =>
          Real.log (2 - x) / Real.cos (Real.pi * x / 2))
        (nhdsWithin 1 ({1} : Set ℝ)ᶜ)
        (nhds ((-1 : ℝ) / (-Real.pi / 2))) := by
    apply hquot.congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx1 : x ≠ 1 := by simpa using hx
    have hxm : x - 1 ≠ 0 := sub_ne_zero.mpr hx1
    change
      ((x - 1)⁻¹ *
          (Real.log (2 - x) - Real.log (2 - 1))) /
          ((x - 1)⁻¹ *
            (Real.cos (Real.pi * x / 2) -
              Real.cos (Real.pi * (1 : ℝ) / 2))) =
        Real.log (2 - x) / Real.cos (Real.pi * x / 2)
    rw [show (2 : ℝ) - 1 = 1 by norm_num, Real.log_one]
    rw [show Real.pi * (1 : ℝ) / 2 = Real.pi / 2 by ring,
      Real.cos_pi_div_two]
    simp only [sub_zero]
    by_cases hc : Real.cos (Real.pi * x / 2) = 0
    · simp [hc]
    · field_simp [hxm, hc]
  have hconst :
      (-1 : ℝ) / (-Real.pi / 2) = 2 / Real.pi := by
    field_simp [ne_of_gt Real.pi_pos]
  simpa [hconst] using hquot'

private theorem near_one_interval :
    ∀ᶠ x in nhdsWithin 1 ({1} : Set ℝ)ᶜ, x ∈ Set.Ioo 0 2 := by
  apply Filter.Eventually.filter_mono
    (show nhdsWithin 1 ({1} : Set ℝ)ᶜ ≤ nhds 1 from inf_le_left)
  exact Ioo_mem_nhds (by norm_num) (by norm_num)

private theorem sine_shift_ne_zero_eventually :
    ∀ᶠ x in nhdsWithin 1 ({1} : Set ℝ)ᶜ,
      Real.sin (Real.pi * (x - 1) / 2) ≠ 0 := by
  filter_upwards [near_one_interval, self_mem_nhdsWithin] with x hx hxmem
  have hx1 : x ≠ 1 := by simpa using hxmem
  have hscale : 0 < Real.pi / 2 := by positivity
  have hlo_mul :
      (Real.pi / 2) * (-1 : ℝ) <
        (Real.pi / 2) * (x - 1) :=
    mul_lt_mul_of_pos_left (by linarith [hx.1]) hscale
  have hhi_mul :
      (Real.pi / 2) * (x - 1) <
        (Real.pi / 2) * (1 : ℝ) :=
    mul_lt_mul_of_pos_left (by linarith [hx.2]) hscale
  have hlo : -Real.pi < Real.pi * (x - 1) / 2 := by
    calc
      -Real.pi < -Real.pi / 2 := by linarith [Real.pi_pos]
      _ = (Real.pi / 2) * (-1 : ℝ) := by ring
      _ < (Real.pi / 2) * (x - 1) := hlo_mul
      _ = Real.pi * (x - 1) / 2 := by ring
  have hhi : Real.pi * (x - 1) / 2 < Real.pi := by
    calc
      Real.pi * (x - 1) / 2 = (Real.pi / 2) * (x - 1) := by ring
      _ < (Real.pi / 2) * (1 : ℝ) := hhi_mul
      _ = Real.pi / 2 := by ring
      _ < Real.pi := by linarith [Real.pi_pos]
  have harg :
      Real.pi * (x - 1) / 2 ≠ 0 := by
    exact div_ne_zero
      (mul_ne_zero (ne_of_gt Real.pi_pos) (sub_ne_zero.mpr hx1))
      (by norm_num)
  intro hsin
  exact harg ((Real.sin_eq_zero_iff_of_lt_of_lt hlo hhi).mp hsin)

private theorem exponential_eq_original_eventually :
    ∀ᶠ x in nhdsWithin 1 ({1} : Set ℝ)ᶜ,
      exponentialForm x = original x := by
  filter_upwards [sine_shift_ne_zero_eventually,
    self_mem_nhdsWithin] with x hsin hxmem
  have hx1 : x ≠ 1 := by simpa using hxmem
  have h1x : 1 - x ≠ 0 := sub_ne_zero.mpr hx1.symm
  have hcos :
      Real.cos (Real.pi * x / 2) =
        -Real.sin (Real.pi * (x - 1) / 2) := by
    rw [show Real.pi * x / 2 =
      Real.pi / 2 + Real.pi * (x - 1) / 2 by ring]
    rw [Real.cos_add, Real.cos_pi_div_two, Real.sin_pi_div_two]
    ring
  have hexponent :
      (1 / (1 - x)) *
          (Real.pi * (x - 1) /
            (2 * Real.sin (Real.pi * (x - 1) / 2))) *
          (2 / Real.pi) =
        sec (Real.pi * x / 2) := by
    unfold sec
    rw [hcos]
    field_simp [hsin, ne_of_gt Real.pi_pos, sub_ne_zero.mpr hx1, h1x]
    ring
  unfold exponentialForm original
  rw [show 1 + (1 - x) = 2 - x by ring]
  exact congrArg (fun e : ℝ => Real.rpow (2 - x) e) hexponent

theorem gap1 (L : ℝ) :
    HasLimitAtOne original L ↔ HasLimitAtOne exponentialForm L := by
  unfold HasLimitAtOne
  constructor
  · intro h
    exact h.congr'
      (exponential_eq_original_eventually.mono fun _ hx => hx.symm)
  · intro h
    exact h.congr' exponential_eq_original_eventually

/-- Exercise 574, gap 2. -/
theorem gap2 : HasLimitAtOne exponentialForm (Real.exp (2 / Real.pi)) := by
  unfold HasLimitAtOne
  have hpos :
      ∀ᶠ x in nhdsWithin 1 ({1} : Set ℝ)ᶜ, 0 < 2 - x := by
    exact near_one_interval.mono fun x hx => by linarith [hx.2]
  have hexp :
      Filter.Tendsto
        (fun x : ℝ =>
          Real.exp
            (Real.log (2 - x) / Real.cos (Real.pi * x / 2)))
        (nhdsWithin 1 ({1} : Set ℝ)ᶜ)
        (nhds (Real.exp (2 / Real.pi))) :=
    (Real.continuous_exp.tendsto (2 / Real.pi)).comp
      tendsto_log_sub_div_cos
  apply hexp.congr'
  filter_upwards [hpos, exponential_eq_original_eventually] with x hx hEq
  rw [hEq, original]
  have hrpow :
      Real.rpow (2 - x) (sec (Real.pi * x / 2)) =
        Real.exp
          (Real.log (2 - x) * sec (Real.pi * x / 2)) := by
    change
      (2 - x) ^ (sec (Real.pi * x / 2) : ℝ) =
        Real.exp
          (Real.log (2 - x) * sec (Real.pi * x / 2))
    exact Real.rpow_def_of_pos hx (sec (Real.pi * x / 2))
  rw [hrpow]
  simp [sec, div_eq_mul_inv]

/-- Exercise 574, gap 3. -/
theorem gap3 : HasLimitAtOne original (Real.exp (2 / Real.pi)) := by
  unfold HasLimitAtOne
  have hb : HasDerivAt (fun x : ℝ => 2 - x) (-1) 1 := by
    convert
      ((hasDerivAt_const (x := (1 : ℝ)) (2 : ℝ)).sub
        (hasDerivAt_id (𝕜 := ℝ) 1)) using 1 <;>
      norm_num
  have hbase :
      Filter.Tendsto (fun x : ℝ => 2 - x)
        (nhdsWithin 1 ({1} : Set ℝ)ᶜ)
        (nhds ((2 : ℝ) - 1)) := by
    exact hb.continuousAt.mono_left
      (show nhdsWithin (1 : ℝ) ({1} : Set ℝ)ᶜ ≤ nhds (1 : ℝ) from
        inf_le_left)
  have hpos :
      ∀ᶠ x in nhdsWithin 1 ({1} : Set ℝ)ᶜ, 0 < 2 - x :=
    hbase.eventually
      (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 2 - 1))
  have hexp :
      Filter.Tendsto
        (fun x : ℝ =>
          Real.exp
            (Real.log (2 - x) / Real.cos (Real.pi * x / 2)))
        (nhdsWithin 1 ({1} : Set ℝ)ᶜ)
        (nhds (Real.exp (2 / Real.pi))) := by
    exact
      (Real.continuous_exp.tendsto (2 / Real.pi)).comp
        tendsto_log_sub_div_cos
  apply hexp.congr'
  filter_upwards [hpos] with x hx
  rw [original]
  have hrpow :
      Real.rpow (2 - x) (sec (Real.pi * x / 2)) =
        Real.exp
          (Real.log (2 - x) * sec (Real.pi * x / 2)) := by
    change
      (2 - x) ^ (sec (Real.pi * x / 2) : ℝ) =
        Real.exp
          (Real.log (2 - x) * sec (Real.pi * x / 2))
    exact Real.rpow_def_of_pos hx (sec (Real.pi * x / 2))
  rw [hrpow]
  simp [sec, div_eq_mul_inv]

end

end ProofGap.Exercise574
