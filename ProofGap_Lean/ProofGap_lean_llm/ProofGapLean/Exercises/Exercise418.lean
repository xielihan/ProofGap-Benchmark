import ProofGapLean.Prelude.Sequences
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise418

noncomputable section

def original (x : ℝ) : ℝ := (x ^ 2 - 5 * x + 6) / (x ^ 2 - 8 * x + 15)
def factored (x : ℝ) : ℝ := ((x - 3) * (x - 2)) / ((x - 3) * (x - 5))
def cancelled (x : ℝ) : ℝ := (x - 2) / (x - 5)
def HasLimitAt (f : ℝ → ℝ) (a L : ℝ) : Prop :=
  Filter.Tendsto f (nhdsWithin a ({a} : Set ℝ)ᶜ) (nhds L)

/-- Exercise 418, gap 1. -/
theorem gap1 : HasLimitAt original 3 (-1 / 2) ↔
    HasLimitAt factored 3 (-1 / 2) := by
  have h : original = factored := by
    funext x
    unfold original factored
    congr 1 <;> ring
  rw [h]

/-- Exercise 418, gap 2. -/
theorem gap2 : HasLimitAt factored 3 (-1 / 2) ↔
    HasLimitAt cancelled 3 (-1 / 2) := by
  unfold HasLimitAt
  have hfg : factored =ᶠ[nhdsWithin (3 : ℝ) ({3} : Set ℝ)ᶜ] cancelled := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx3 : x ≠ (3 : ℝ) := by
      simpa using hx
    simpa only [factored, cancelled] using
      (mul_div_mul_left (x - 2) (x - 5) (sub_ne_zero.mpr hx3))
  exact ⟨Filter.Tendsto.congr' hfg, Filter.Tendsto.congr' hfg.symm⟩

/-- Exercise 418, gap 3. -/
theorem gap3 : HasLimitAt cancelled 3 (-1 / 2) := by
  unfold HasLimitAt cancelled
  have hc : ContinuousAt (fun x : ℝ => (x - 2) / (x - 5)) 3 :=
    (continuousAt_id.sub continuousAt_const).div
      (continuousAt_id.sub continuousAt_const) (by norm_num)
  have ht := hc.tendsto.mono_left
    (show nhdsWithin (3 : ℝ) ({3} : Set ℝ)ᶜ ≤ nhds 3 from inf_le_left)
  convert ht using 1 <;> norm_num

/-- Exercise 418, gap 4. -/
theorem gap4 : HasLimitAt original 3 (-1 / 2) := by
  exact gap1.mpr (gap2.mpr gap3)

end

end ProofGap.Exercise418
