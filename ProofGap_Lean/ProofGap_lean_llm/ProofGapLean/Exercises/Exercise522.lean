import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise522

noncomputable section

def original (x : ℝ) : ℝ := Real.rpow (Real.tan x) (Real.tan (2 * x))
def doubleAngle (x : ℝ) : ℝ :=
  Real.rpow (Real.tan x) (2 * Real.tan x / (1 - Real.tan x ^ 2))
def exponentialForm (x : ℝ) : ℝ :=
  Real.rpow (1 + (Real.tan x - 1))
    ((1 / (Real.tan x - 1)) * (-2 * Real.tan x / (Real.tan x + 1)))
def HasLimitAt (f : ℝ → ℝ) (a L : ℝ) : Prop :=
  Filter.Tendsto f (nhdsWithin a ({a} : Set ℝ)ᶜ) (nhds L)

/-- Exercise 522, gap 1. -/
private theorem tendsto_tan_and_log_quotient :
    Filter.Tendsto Real.tan
        (nhdsWithin (Real.pi / 4) ({Real.pi / 4} : Set ℝ)ᶜ) (nhds 1) ∧
      Filter.Tendsto
        (fun x : ℝ => Real.log (Real.tan x) / (Real.tan x - 1))
        (nhdsWithin (Real.pi / 4) ({Real.pi / 4} : Set ℝ)ᶜ)
        (nhds 1) := by
  let d : ℝ := 1 / Real.cos (Real.pi / 4) ^ 2
  have hcos : Real.cos (Real.pi / 4) ≠ 0 := by
    rw [Real.cos_pi_div_four]
    positivity
  have hraw :
      HasDerivAt (fun x : ℝ => Real.sin x / Real.cos x)
        ((Real.cos (Real.pi / 4) * Real.cos (Real.pi / 4) -
            Real.sin (Real.pi / 4) * (-Real.sin (Real.pi / 4))) /
          Real.cos (Real.pi / 4) ^ 2)
        (Real.pi / 4) := by
    exact (Real.hasDerivAt_sin (Real.pi / 4)).div
      (Real.hasDerivAt_cos (Real.pi / 4)) hcos
  have htrig :
      Real.cos (Real.pi / 4) * Real.cos (Real.pi / 4) -
          Real.sin (Real.pi / 4) * (-Real.sin (Real.pi / 4)) = 1 := by
    nlinarith [Real.sin_sq_add_cos_sq (Real.pi / 4)]
  have hval :
      ((Real.cos (Real.pi / 4) * Real.cos (Real.pi / 4) -
            Real.sin (Real.pi / 4) * (-Real.sin (Real.pi / 4))) /
          Real.cos (Real.pi / 4) ^ 2) = d := by
    dsimp only [d]
    exact congrArg
      (fun z : ℝ => z / Real.cos (Real.pi / 4) ^ 2) htrig
  have htan_center : Real.tan (Real.pi / 4) = 1 :=
    Real.tan_pi_div_four
  have hlog_center : Real.log (Real.tan (Real.pi / 4)) = 0 := by
    rw [htan_center, Real.log_one]
  have htanEq : Real.tan = fun x : ℝ => Real.sin x / Real.cos x := by
    funext x
    exact Real.tan_eq_sin_div_cos x
  have htanD : HasDerivAt Real.tan d (Real.pi / 4) := by
    rw [htanEq]
    exact hval ▸ hraw
  have ht : Filter.Tendsto Real.tan
      (nhdsWithin (Real.pi / 4) ({Real.pi / 4} : Set ℝ)ᶜ)
      (nhds 1) := by
    have h := htanD.continuousAt
    simpa only [htan_center] using h.mono_left inf_le_left
  have hlogD : HasDerivAt Real.log 1 (Real.tan (Real.pi / 4)) := by
    simpa [htan_center] using
      (Real.hasDerivAt_log
        (show Real.tan (Real.pi / 4) ≠ 0 by
          rw [htan_center]
          norm_num))
  have hlogtanD :
      HasDerivAt (fun x : ℝ => Real.log (Real.tan x)) d
        (Real.pi / 4) := by
    simpa [Function.comp_def] using hlogD.comp (Real.pi / 4) htanD
  have hd : d ≠ 0 := by
    dsimp [d]
    exact div_ne_zero one_ne_zero (pow_ne_zero 2 hcos)
  have hnum : Filter.Tendsto
      (fun x : ℝ => Real.log (Real.tan x) / (x - Real.pi / 4))
      (nhdsWithin (Real.pi / 4) ({Real.pi / 4} : Set ℝ)ᶜ)
      (nhds d) := by
    refine hlogtanD.tendsto_slope.congr' (Filter.Eventually.of_forall ?_)
    intro x
    rw [slope, hlog_center]
    simp only [vsub_eq_sub, sub_zero, smul_eq_mul, div_eq_mul_inv]
    ring
  have hden : Filter.Tendsto
      (fun x : ℝ => (Real.tan x - 1) / (x - Real.pi / 4))
      (nhdsWithin (Real.pi / 4) ({Real.pi / 4} : Set ℝ)ᶜ)
      (nhds d) := by
    refine htanD.tendsto_slope.congr' (Filter.Eventually.of_forall ?_)
    intro x
    rw [slope, htan_center]
    simp only [vsub_eq_sub, smul_eq_mul, div_eq_mul_inv]
    ring
  have hratio : Filter.Tendsto
      (fun x : ℝ =>
        (Real.log (Real.tan x) / (x - Real.pi / 4)) /
          ((Real.tan x - 1) / (x - Real.pi / 4)))
      (nhdsWithin (Real.pi / 4) ({Real.pi / 4} : Set ℝ)ᶜ)
      (nhds 1) := by
    simpa [hd] using hnum.div hden hd
  have hquot : Filter.Tendsto
      (fun x : ℝ => Real.log (Real.tan x) / (Real.tan x - 1))
      (nhdsWithin (Real.pi / 4) ({Real.pi / 4} : Set ℝ)ᶜ)
      (nhds 1) := by
    refine hratio.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hxa : x ≠ Real.pi / 4 := by
      simpa using hx
    have hdiff : x - Real.pi / 4 ≠ 0 := sub_ne_zero.mpr hxa
    by_cases ht1 : Real.tan x - 1 = 0
    · have htval : Real.tan x = 1 := sub_eq_zero.mp ht1
      simp [htval]
    · have hcancel (a b c : ℝ) (hb : b ≠ 0) (hc : c ≠ 0) :
          (a / c) / (b / c) = a / b := by
        field_simp [hb, hc]
      exact hcancel (Real.log (Real.tan x)) (Real.tan x - 1)
        (x - Real.pi / 4) ht1 hdiff
  exact ⟨ht, hquot⟩

theorem gap1 (L : ℝ) :
    HasLimitAt original (Real.pi / 4) L ↔
      HasLimitAt doubleAngle (Real.pi / 4) L := by
  have hfun : original = doubleAngle := by
    funext x
    unfold original doubleAngle
    rw [Real.tan_two_mul]
  rw [hfun]

/-- Exercise 522, gap 2. -/
theorem gap2 (L : ℝ) :
    HasLimitAt original (Real.pi / 4) L ↔
      HasLimitAt exponentialForm (Real.pi / 4) L := by
  have hpoint (x : ℝ) : doubleAngle x = exponentialForm x := by
    unfold doubleAngle exponentialForm
    rw [show 1 + (Real.tan x - 1) = Real.tan x by ring]
    apply congrArg (Real.rpow (Real.tan x))
    set t : ℝ := Real.tan x
    by_cases ht1 : t = 1
    · simp [ht1]
    by_cases htm1 : t = -1
    · simp [htm1]
    have hsub : t - 1 ≠ 0 := sub_ne_zero.mpr ht1
    have hadd : t + 1 ≠ 0 := by
      intro h
      apply htm1
      linarith
    have hsq : 1 - t ^ 2 ≠ 0 := by
      intro h
      have hp : (1 - t) * (1 + t) = 0 := by
        nlinarith
      rcases mul_eq_zero.mp hp with hp | hp
      · apply ht1
        linarith
      · apply htm1
        linarith
    field_simp [hsub, hadd, hsq] <;> ring
  calc
    HasLimitAt original (Real.pi / 4) L ↔
        HasLimitAt doubleAngle (Real.pi / 4) L := gap1 L
    _ ↔ HasLimitAt exponentialForm (Real.pi / 4) L := by
      rw [show doubleAngle = exponentialForm from funext hpoint]

/-- Exercise 522, gap 3. -/
theorem gap3 : HasLimitAt exponentialForm (Real.pi / 4) (Real.exp (-1)) := by
  unfold HasLimitAt
  let l := nhdsWithin (Real.pi / 4) ({Real.pi / 4} : Set ℝ)ᶜ
  have ht : Filter.Tendsto Real.tan l (nhds 1) := by
    simpa [l] using tendsto_tan_and_log_quotient.1
  have hq : Filter.Tendsto
      (fun x : ℝ => Real.log (Real.tan x) / (Real.tan x - 1))
      l (nhds 1) := by
    simpa [l] using tendsto_tan_and_log_quotient.2
  have hn : Filter.Tendsto (fun x : ℝ => -2 * Real.tan x) l (nhds (-2)) := by
    simpa using (tendsto_const_nhds.mul ht :
      Filter.Tendsto (fun x : ℝ => (-2) * Real.tan x) l (nhds ((-2) * 1)))
  have hd : Filter.Tendsto (fun x : ℝ => Real.tan x + 1) l
      (nhds ((1 : ℝ) + 1)) :=
    ht.add tendsto_const_nhds
  have hc0 := hn.div hd (by norm_num : (1 + 1 : ℝ) ≠ 0)
  have hc : Filter.Tendsto
      (fun x : ℝ => -2 * Real.tan x / (Real.tan x + 1))
      l (nhds (-1)) := by
    convert hc0 using 1 <;> norm_num
  have hp : Filter.Tendsto
      (fun x : ℝ =>
        (Real.log (Real.tan x) / (Real.tan x - 1)) *
          (-2 * Real.tan x / (Real.tan x + 1)))
      l (nhds (-1)) := by
    simpa using hq.mul hc
  have hpos : ∀ᶠ x in l, 0 < Real.tan x := by
    simpa using (tendsto_order.1 ht).1 0 (by norm_num : (0 : ℝ) < 1)
  have he : Filter.Tendsto
      (fun x : ℝ => Real.exp
        ((Real.log (Real.tan x) / (Real.tan x - 1)) *
          (-2 * Real.tan x / (Real.tan x + 1))))
      l (nhds (Real.exp (-1))) := by
    exact (show Filter.Tendsto Real.exp (nhds (-1))
      (nhds (Real.exp (-1))) from Real.continuous_exp.continuousAt).comp hp
  refine he.congr' ?_
  filter_upwards [hpos] with x hx
  symm
  unfold exponentialForm
  rw [show 1 + (Real.tan x - 1) = Real.tan x by ring]
  let e : ℝ :=
    (1 / (Real.tan x - 1)) * (-2 * Real.tan x / (Real.tan x + 1))
  have hrpow :
      Real.rpow (Real.tan x) e =
        Real.exp (Real.log (Real.tan x) * e) :=
    Real.rpow_def_of_pos hx e
  calc
    Real.rpow (Real.tan x)
        ((1 / (Real.tan x - 1)) * (-2 * Real.tan x / (Real.tan x + 1))) =
        Real.exp
          (Real.log (Real.tan x) *
            ((1 / (Real.tan x - 1)) *
              (-2 * Real.tan x / (Real.tan x + 1)))) := by
          simpa [e] using hrpow
    _ = Real.exp
        (Real.log (Real.tan x) / (Real.tan x - 1) *
          (-2 * Real.tan x / (Real.tan x + 1))) := by
          congr 1
          ring

/-- Exercise 522, gap 4. -/
theorem gap4 : HasLimitAt original (Real.pi / 4) (Real.exp (-1)) := by
  exact (gap2 (Real.exp (-1))).mpr gap3

end

end ProofGap.Exercise522
