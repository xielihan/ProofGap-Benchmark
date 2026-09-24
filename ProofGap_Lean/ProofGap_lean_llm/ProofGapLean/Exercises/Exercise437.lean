import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

namespace ProofGap.Exercise437

noncomputable section

def original (x : ℝ) : ℝ :=
  (Real.sqrt (1 + 2 * x) - 3) / (Real.sqrt x - 2)
def rationalized (x : ℝ) : ℝ :=
  ((Real.sqrt (1 + 2 * x) - 3) * (Real.sqrt (1 + 2 * x) + 3) *
      (Real.sqrt x + 2)) /
    ((Real.sqrt x - 2) * (Real.sqrt x + 2) *
      (Real.sqrt (1 + 2 * x) + 3))
def factored (x : ℝ) : ℝ :=
  (2 * (x - 4) * (Real.sqrt x + 2)) /
    ((x - 4) * (Real.sqrt (1 + 2 * x) + 3))
def cancelled (x : ℝ) : ℝ :=
  2 * (Real.sqrt x + 2) / (Real.sqrt (1 + 2 * x) + 3)
def HasLimitAt (f : ℝ → ℝ) (a L : ℝ) : Prop :=
  Filter.Tendsto f (nhdsWithin a ({a} : Set ℝ)ᶜ) (nhds L)

/-- Exercise 437, gap 1. -/
private theorem hasLimitAtCongr {f g : ℝ → ℝ} {a L : ℝ}
    (hfg : f =ᶠ[nhdsWithin a ({a} : Set ℝ)ᶜ] g) :
    HasLimitAt f a L ↔ HasLimitAt g a L := by
  unfold HasLimitAt
  constructor
  · intro hf
    exact hf.congr' hfg
  · intro hg
    exact hg.congr' hfg.symm

private theorem eventuallyPositiveNearFour :
    ∀ᶠ x : ℝ in nhdsWithin (4 : ℝ) ({4} : Set ℝ)ᶜ, 0 < x := by
  apply Filter.Eventually.filter_mono
    (show nhdsWithin (4 : ℝ) ({4} : Set ℝ)ᶜ ≤ nhds 4 from inf_le_left)
  exact isOpen_Ioi.mem_nhds (by norm_num)

theorem gap1 : HasLimitAt original 4 (4 / 3) ↔
    HasLimitAt rationalized 4 (4 / 3) := by
  apply hasLimitAtCongr
  filter_upwards [eventuallyPositiveNearFour, self_mem_nhdsWithin] with x hxpos hxmem
  have hxne : x ≠ 4 := by
    simpa using hxmem
  have hsqrt_sq : (Real.sqrt x) ^ 2 = x :=
    Real.sq_sqrt (le_of_lt hxpos)
  have hminus : Real.sqrt x - 2 ≠ 0 := by
    intro h
    apply hxne
    nlinarith
  have hplus : Real.sqrt x + 2 ≠ 0 := by
    positivity
  have hother : Real.sqrt (1 + 2 * x) + 3 ≠ 0 := by
    positivity
  unfold original rationalized
  field_simp [hminus, hplus, hother]

/-- Exercise 437, gap 2. -/
theorem gap2 : HasLimitAt rationalized 4 (4 / 3) ↔
    HasLimitAt factored 4 (4 / 3) := by
  apply hasLimitAtCongr
  filter_upwards [eventuallyPositiveNearFour] with x hxpos
  have hx_sq : (Real.sqrt x) ^ 2 = x :=
    Real.sq_sqrt (le_of_lt hxpos)
  have harg : 0 ≤ 1 + 2 * x := by
    linarith
  have harg_sq : (Real.sqrt (1 + 2 * x)) ^ 2 = 1 + 2 * x :=
    Real.sq_sqrt harg
  have hnum :
      (Real.sqrt (1 + 2 * x) - 3) * (Real.sqrt (1 + 2 * x) + 3) =
        2 * (x - 4) := by
    nlinarith [harg_sq]
  have hden :
      (Real.sqrt x - 2) * (Real.sqrt x + 2) = x - 4 := by
    nlinarith [hx_sq]
  unfold rationalized factored
  rw [hnum, hden]

/-- Exercise 437, gap 3. -/
theorem gap3 : HasLimitAt factored 4 (4 / 3) ↔
    HasLimitAt cancelled 4 (4 / 3) := by
  apply hasLimitAtCongr
  filter_upwards [self_mem_nhdsWithin] with x hxmem
  have hxne : x ≠ 4 := by
    simpa using hxmem
  have hfactor : x - 4 ≠ 0 := sub_ne_zero.mpr hxne
  have hden : Real.sqrt (1 + 2 * x) + 3 ≠ 0 := by
    positivity
  unfold factored cancelled
  field_simp [hfactor, hden]

/-- Exercise 437, gap 4. -/
theorem gap4 : HasLimitAt cancelled 4 (4 / 3) := by
  unfold HasLimitAt
  have hc1 : ContinuousAt (fun x : ℝ => Real.sqrt x) 4 :=
    Real.continuous_sqrt.continuousAt
  have hcinner : ContinuousAt (fun x : ℝ => 1 + 2 * x) 4 :=
    continuousAt_const.add (continuousAt_const.mul continuousAt_id)
  have hc2 : ContinuousAt (fun x : ℝ => Real.sqrt (1 + 2 * x)) 4 :=
    Real.continuous_sqrt.continuousAt.comp hcinner
  have hcnum :
      ContinuousAt (fun x : ℝ => 2 * (Real.sqrt x + 2)) 4 :=
    continuousAt_const.mul (hc1.add continuousAt_const)
  have hcden :
      ContinuousAt (fun x : ℝ => Real.sqrt (1 + 2 * x) + 3) 4 :=
    hc2.add continuousAt_const
  have hsqrt4_sq : (Real.sqrt (4 : ℝ)) ^ 2 = 4 :=
    Real.sq_sqrt (by norm_num)
  have hsqrt4_nonneg : 0 ≤ Real.sqrt (4 : ℝ) :=
    Real.sqrt_nonneg 4
  have hsqrt4 : Real.sqrt (4 : ℝ) = 2 := by
    nlinarith [hsqrt4_sq, hsqrt4_nonneg]
  have hsqrt9_sq : (Real.sqrt (9 : ℝ)) ^ 2 = 9 :=
    Real.sq_sqrt (by norm_num)
  have hsqrt9_nonneg : 0 ≤ Real.sqrt (9 : ℝ) :=
    Real.sqrt_nonneg 9
  have hsqrt9 : Real.sqrt (9 : ℝ) = 3 := by
    nlinarith [hsqrt9_sq, hsqrt9_nonneg]
  have harg4 : (1 : ℝ) + 2 * 4 = 9 := by
    norm_num
  have hden : Real.sqrt (1 + 2 * (4 : ℝ)) + 3 ≠ 0 := by
    rw [harg4, hsqrt9]
    norm_num
  have hcont : ContinuousAt cancelled 4 := by
    unfold cancelled
    exact hcnum.div hcden hden
  have hcval : cancelled 4 = 4 / 3 := by
    unfold cancelled
    rw [harg4, hsqrt4, hsqrt9]
    norm_num
  rw [← hcval]
  exact hcont.tendsto.mono_left inf_le_left

/-- Exercise 437, gap 5. -/
theorem gap5 : HasLimitAt original 4 (4 / 3) := by
  exact gap1.mpr (gap2.mpr (gap3.mpr gap4))

end

end ProofGap.Exercise437
