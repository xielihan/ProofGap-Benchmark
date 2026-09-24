import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise538

noncomputable section

def original (a b x : ℝ) : ℝ :=
  Real.log (Real.tan (Real.pi / 4 + a * x)) / Real.sin (b * x)
def logPower (a b x : ℝ) : ℝ :=
  Real.log (Real.rpow (Real.tan (Real.pi / 4 + a * x)) (1 / Real.sin (b * x)))
def tangentExpanded (a b x : ℝ) : ℝ :=
  Real.log (Real.rpow
    (1 + (Real.sin (Real.pi / 4 + a * x) -
      Real.cos (Real.pi / 4 + a * x)) / Real.cos (Real.pi / 4 + a * x))
    (1 / Real.sin (b * x)))
def exponentialForm (a b x : ℝ) : ℝ :=
  let q := Real.sqrt 2 * Real.sin (a * x) / Real.cos (Real.pi / 4 + a * x)
  Real.log (Real.rpow (1 + q)
    ((Real.cos (Real.pi / 4 + a * x) / (Real.sqrt 2 * Real.sin (a * x))) *
      (Real.sqrt 2 / Real.cos (Real.pi / 4 + a * x)) *
      (Real.sin (a * x) / Real.sin (b * x))))
def HasLimitAtZero (f : ℝ → ℝ) (L : ℝ) : Prop :=
  Filter.Tendsto f (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds L)

/-- Source: `proof_gap/exercise_538/1.txt`; require `b≠0`. -/
private theorem tangent_pos_eventually (a : ℝ) :
    ∀ᶠ x in nhdsWithin 0 ({0} : Set ℝ)ᶜ,
      0 < Real.tan (Real.pi / 4 + a * x) := by
  have hden : 0 < 4 * |a| + 1 := by positivity
  have hradius : 0 < Real.pi / (4 * |a| + 1) :=
    div_pos Real.pi_pos hden
  have hsmall_at :
      ∀ᶠ x in nhds 0,
        x ∈ Set.Ioo (-(Real.pi / (4 * |a| + 1)))
          (Real.pi / (4 * |a| + 1)) := by
    exact Ioo_mem_nhds (neg_lt_zero.mpr hradius) hradius
  have hsmall :
      ∀ᶠ x in nhdsWithin 0 ({0} : Set ℝ)ᶜ,
        x ∈ Set.Ioo (-(Real.pi / (4 * |a| + 1)))
          (Real.pi / (4 * |a| + 1)) := by
    apply Filter.Eventually.filter_mono
      (show nhdsWithin 0 ({0} : Set ℝ)ᶜ ≤ nhds 0 from inf_le_left)
    exact hsmall_at
  filter_upwards [hsmall] with x hx
  have hax : |a * x| < Real.pi / 4 := by
    rw [abs_mul]
    have ha_le : |a| ≤ (4 * |a| + 1) / 4 := by
      linarith
    have hx' : |x| < Real.pi / (4 * |a| + 1) := by
      rw [abs_lt]
      exact hx
    calc
      |a| * |x| ≤ ((4 * |a| + 1) / 4) * |x| :=
        mul_le_mul_of_nonneg_right ha_le (abs_nonneg x)
      _ < ((4 * |a| + 1) / 4) *
          (Real.pi / (4 * |a| + 1)) :=
        mul_lt_mul_of_pos_left hx' (by positivity)
      _ = Real.pi / 4 := by
        field_simp [ne_of_gt hden]
  have hang : 0 < Real.pi / 4 + a * x := by
    have hleft := (abs_lt.1 hax).1
    linarith
  have hang' : Real.pi / 4 + a * x < Real.pi / 2 := by
    have hright := (abs_lt.1 hax).2
    linarith
  exact Real.tan_pos_of_pos_of_lt_pi_div_two hang hang'

private theorem sine_ne_zero_eventually (a : ℝ) (ha : a ≠ 0) :
    ∀ᶠ x in nhdsWithin 0 ({0} : Set ℝ)ᶜ, Real.sin (a * x) ≠ 0 := by
  have ha_abs : 0 < |a| := abs_pos.mpr ha
  have hradius : 0 < Real.pi / |a| := div_pos Real.pi_pos ha_abs
  have hsmall_at :
      ∀ᶠ x in nhds 0, x ∈ Set.Ioo (-(Real.pi / |a|)) (Real.pi / |a|) := by
    exact Ioo_mem_nhds (neg_lt_zero.mpr hradius) hradius
  have hsmall :
      ∀ᶠ x in nhdsWithin 0 ({0} : Set ℝ)ᶜ,
        x ∈ Set.Ioo (-(Real.pi / |a|)) (Real.pi / |a|) := by
    exact Filter.Eventually.filter_mono
      (show nhdsWithin 0 ({0} : Set ℝ)ᶜ ≤ nhds 0 from inf_le_left)
      hsmall_at
  filter_upwards [hsmall, self_mem_nhdsWithin] with x hx hxmem
  have hx0 : x ≠ 0 := by simpa using hxmem
  have hax0 : a * x ≠ 0 := mul_ne_zero ha hx0
  have hxabs : |x| < Real.pi / |a| := by
    rw [abs_lt]
    exact hx
  have haxabs : |a * x| < Real.pi := by
    rw [abs_mul]
    calc
      |a| * |x| < |a| * (Real.pi / |a|) :=
        mul_lt_mul_of_pos_left hxabs ha_abs
      _ = Real.pi := by field_simp [ne_of_gt ha_abs]
  intro hsin
  exact hax0 ((Real.sin_eq_zero_iff_of_lt_of_lt
    (abs_lt.mp haxabs).1 (abs_lt.mp haxabs).2).mp hsin)

private theorem original_limit (a b : ℝ) (hb : b ≠ 0) :
    HasLimitAtZero (original a b) (2 * a / b) := by
  unfold HasLimitAtZero original
  have hangle :
      HasDerivAt (fun x : ℝ => Real.pi / 4 + a * x) a 0 := by
    simpa [id_eq, add_comm] using
      ((hasDerivAt_id (0 : ℝ)).const_mul a).add_const (Real.pi / 4)
  have hcos : Real.cos (Real.pi / 4) ≠ 0 := by
    rw [Real.cos_pi_div_four]
    positivity
  have hsqrtsec : ((Real.sqrt 2 / 2) ^ 2)⁻¹ = (2 : ℝ) := by
    rw [div_pow,
      Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    norm_num
  have hnum :
      HasDerivAt
        (fun x : ℝ => Real.log (Real.tan (Real.pi / 4 + a * x)))
        (2 * a) 0 := by
    have htan :=
      (Real.hasDerivAt_tan (by simpa using hcos)).comp (0 : ℝ) hangle
    have hlog := htan.log (by simp [Real.tan_pi_div_four])
    simpa [Function.comp_def, hsqrtsec, Real.tan_pi_div_four] using hlog
  have hden :
      HasDerivAt (fun x : ℝ => Real.sin (b * x)) b 0 := by
    have hlinear : HasDerivAt (fun x : ℝ => b * x) b 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_mul b
    simpa using (Real.hasDerivAt_sin (b * 0)).comp (0 : ℝ) hlinear
  have hquot :=
    hnum.tendsto_slope_zero.div hden.tendsto_slope_zero hb
  apply hquot.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : x ≠ 0 := by simpa using hx
  simp [Real.tan_pi_div_four, smul_eq_mul]
  field_simp [hx0]

theorem gap1 (a b : ℝ) (hb : b ≠ 0) (L : ℝ) :
    HasLimitAtZero (original a b) L ↔ HasLimitAtZero (logPower a b) L := by
  unfold HasLimitAtZero original logPower
  apply Filter.tendsto_congr'
  filter_upwards [tangent_pos_eventually a] with x htan
  have hlog :
      Real.log (Real.rpow (Real.tan (Real.pi / 4 + a * x))
        (1 / Real.sin (b * x))) =
        (1 / Real.sin (b * x)) *
          Real.log (Real.tan (Real.pi / 4 + a * x)) :=
    Real.log_rpow htan _
  rw [hlog]
  ring_nf

/-- Source: `proof_gap/exercise_538/2.txt`; require `b≠0`. -/
theorem gap2 (a b : ℝ) (hb : b ≠ 0) (L : ℝ) :
    HasLimitAtZero (logPower a b) L ↔ HasLimitAtZero (tangentExpanded a b) L := by
  unfold HasLimitAtZero logPower tangentExpanded
  apply Filter.tendsto_congr'
  filter_upwards [tangent_pos_eventually a] with x htan
  have hcos : Real.cos (Real.pi / 4 + a * x) ≠ 0 := by
    intro hzero
    have htan_zero : Real.tan (Real.pi / 4 + a * x) = 0 := by
      rw [Real.tan_eq_sin_div_cos, hzero]
      simp
    linarith
  have hbase :
      Real.tan (Real.pi / 4 + a * x) =
        1 + (Real.sin (Real.pi / 4 + a * x) -
          Real.cos (Real.pi / 4 + a * x)) /
            Real.cos (Real.pi / 4 + a * x) := by
    rw [Real.tan_eq_sin_div_cos, sub_div, div_self hcos]
    ring
  rw [hbase]

private theorem exponential_eq_logPower_eventually
    (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    ∀ᶠ x in nhdsWithin 0 ({0} : Set ℝ)ᶜ,
      exponentialForm a b x = logPower a b x := by
  filter_upwards [tangent_pos_eventually a,
    sine_ne_zero_eventually a ha, sine_ne_zero_eventually b hb] with
      x htan hsina hsinb
  have hcos : Real.cos (Real.pi / 4 + a * x) ≠ 0 := by
    intro hzero
    have htan_zero : Real.tan (Real.pi / 4 + a * x) = 0 := by
      rw [Real.tan_eq_sin_div_cos, hzero]
      simp
    linarith
  have hsqrt : Real.sqrt 2 ≠ 0 := by positivity
  have hdiff :
      Real.sin (Real.pi / 4 + a * x) -
          Real.cos (Real.pi / 4 + a * x) =
        Real.sqrt 2 * Real.sin (a * x) := by
    rw [Real.sin_add, Real.cos_add, Real.sin_pi_div_four,
      Real.cos_pi_div_four]
    ring
  have hbase :
      1 + Real.sqrt 2 * Real.sin (a * x) /
          Real.cos (Real.pi / 4 + a * x) =
        Real.tan (Real.pi / 4 + a * x) := by
    rw [Real.tan_eq_sin_div_cos, ← hdiff]
    rw [sub_div, div_self hcos]
    ring
  have hexponent :
      (Real.cos (Real.pi / 4 + a * x) /
          (Real.sqrt 2 * Real.sin (a * x))) *
          (Real.sqrt 2 / Real.cos (Real.pi / 4 + a * x)) *
          (Real.sin (a * x) / Real.sin (b * x)) =
        1 / Real.sin (b * x) := by
    let c := Real.cos (Real.pi / 4 + a * x)
    let r := Real.sqrt 2
    let s := Real.sin (a * x)
    let t := Real.sin (b * x)
    have hc : c ≠ 0 := by simpa [c] using hcos
    have hr : r ≠ 0 := by simpa [r] using hsqrt
    have hs : s ≠ 0 := by simpa [s] using hsina
    have ht : t ≠ 0 := by simpa [t] using hsinb
    change (c / (r * s)) * (r / c) * (s / t) = 1 / t
    field_simp [hc, hr, hs, ht]
  unfold exponentialForm logPower
  dsimp
  rw [hbase, hexponent]

private theorem exponential_limit
    (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    HasLimitAtZero (exponentialForm a b) (2 * a / b) := by
  have hlog :
      HasLimitAtZero (logPower a b) (2 * a / b) :=
    (gap1 a b hb (2 * a / b)).mp (original_limit a b hb)
  unfold HasLimitAtZero at hlog ⊢
  exact hlog.congr'
    ((exponential_eq_logPower_eventually a b ha hb).mono fun _ hx => hx.symm)

/-- Source: `proof_gap/exercise_538/3.txt`; the displayed substitution also divides by `a`. -/
theorem gap3 (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    HasLimitAtZero (exponentialForm a b)
      (Real.log (Real.exp (2 * a / b))) := by
  simpa [Real.log_exp] using exponential_limit a b ha hb

/-- Source: `proof_gap/exercise_538/4.txt`; require `b≠0`. -/
theorem gap4 (a b : ℝ) (hb : b ≠ 0) :
    Real.log (Real.exp (2 * a / b)) = 2 * a / b := by
  rw [Real.log_exp]

/-- Source: `proof_gap/exercise_538/5.txt`; retain both nonzero substitution parameters. -/
theorem gap5 (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    HasLimitAtZero (exponentialForm a b) (2 * a / b) := by
  exact exponential_limit a b ha hb

end

end ProofGap.Exercise538
