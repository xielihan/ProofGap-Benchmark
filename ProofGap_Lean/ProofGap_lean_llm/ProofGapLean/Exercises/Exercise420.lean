import ProofGapLean.Prelude.Sequences
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise420

noncomputable section

def original (x : ℝ) : ℝ :=
  (x ^ 3 - 3 * x + 2) / (x ^ 4 - x ^ 3 - x + 1)
def factored (x : ℝ) : ℝ :=
  ((x - 1) ^ 2 * (x + 2)) / ((x - 1) ^ 2 * (x ^ 2 + x + 1))
def cancelled (x : ℝ) : ℝ := (x + 2) / (x ^ 2 + x + 1)
def HasLimitAt (f : ℝ → ℝ) (a L : ℝ) : Prop :=
  Filter.Tendsto f (nhdsWithin a ({a} : Set ℝ)ᶜ) (nhds L)

/-- Exercise 420, gap 1. -/
theorem gap1 : HasLimitAt original 1 1 ↔ HasLimitAt factored 1 1 := by
  have hfun : original = factored := by
    funext x
    unfold original factored
    have hnum :
        x ^ 3 - 3 * x + 2 = (x - 1) ^ 2 * (x + 2) := by
      ring
    have hden :
        x ^ 4 - x ^ 3 - x + 1 = (x - 1) ^ 2 * (x ^ 2 + x + 1) := by
      ring
    rw [hnum, hden]
  rw [hfun]

/-- Exercise 420, gap 2. -/
theorem gap2 : HasLimitAt factored 1 1 ↔ HasLimitAt cancelled 1 1 := by
  have hfg :
      factored =ᶠ[nhdsWithin (1 : ℝ) ({(1 : ℝ)} : Set ℝ)ᶜ] cancelled := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hxne : x ≠ 1 := by
      simpa using hx
    have hxm : x - 1 ≠ 0 := sub_ne_zero.mpr hxne
    have hqpos : 0 < x ^ 2 + x + 1 := by
      nlinarith [sq_nonneg (2 * x + 1)]
    have hq : x ^ 2 + x + 1 ≠ 0 := ne_of_gt hqpos
    unfold factored cancelled
    field_simp [hxm, hq]
  unfold HasLimitAt Filter.Tendsto
  rw [Filter.map_congr hfg]

/-- Exercise 420, gap 3. -/
theorem gap3 : HasLimitAt cancelled 1 1 := by
  unfold HasLimitAt
  have hnum : ContinuousAt (fun x : ℝ => x + 2) 1 :=
    continuousAt_id.add continuousAt_const
  have hden : ContinuousAt (fun x : ℝ => x ^ 2 + x + 1) 1 :=
    ((continuousAt_id.pow 2).add continuousAt_id).add continuousAt_const
  have hcont : ContinuousAt cancelled 1 := by
    unfold cancelled
    exact hnum.div hden (by norm_num)
  have hwithin :
      ContinuousWithinAt cancelled ({(1 : ℝ)} : Set ℝ)ᶜ 1 :=
    hcont.continuousWithinAt
  have hval : cancelled 1 = 1 := by
    norm_num [cancelled]
  simpa only [ContinuousWithinAt, hval] using hwithin

/-- Exercise 420, gap 4. -/
theorem gap4 : HasLimitAt original 1 1 := by
  exact gap1.mpr (gap2.mpr gap3)

end

end ProofGap.Exercise420
