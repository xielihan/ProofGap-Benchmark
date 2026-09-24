import ProofGapLean.Prelude.Sequences
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise421

noncomputable section

def original (x : ℝ) : ℝ :=
  (x ^ 3 - 2 * x ^ 2 - 4 * x + 8) / (x ^ 4 - 8 * x ^ 2 + 16)
def factored (x : ℝ) : ℝ :=
  ((x - 2) ^ 2 * (x + 2)) / ((x - 2) ^ 2 * (x + 2) ^ 2)
def cancelled (x : ℝ) : ℝ := 1 / (x + 2)
def HasLimitAt (f : ℝ → ℝ) (a L : ℝ) : Prop :=
  Filter.Tendsto f (nhdsWithin a ({a} : Set ℝ)ᶜ) (nhds L)

/-- Source: `proof_gap/exercise_421/1.txt`. -/
theorem gap1 : HasLimitAt original 2 (1 / 4) ↔
    HasLimitAt factored 2 (1 / 4) := by
  have h : original = factored := by
    funext x
    unfold original factored
    congr 1 <;> ring
  rw [h]

/-- Source: `proof_gap/exercise_421/2.txt`. -/
theorem gap2 : HasLimitAt factored 2 (1 / 4) ↔
    HasLimitAt cancelled 2 (1 / 4) := by
  have h_event :
      factored =ᶠ[nhdsWithin (2 : ℝ) ({2} : Set ℝ)ᶜ] cancelled := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx2 : x ≠ 2 := by
      simpa using hx
    unfold factored cancelled
    by_cases hp : x + 2 = 0
    · simp [hp]
    · have hm : x - 2 ≠ 0 := sub_ne_zero.mpr hx2
      field_simp [hm, hp] <;> ring
  constructor
  · intro h
    exact h.congr' h_event
  · intro h
    exact h.congr' h_event.symm

/-- Source: `proof_gap/exercise_421/3.txt`. -/
theorem gap3 : HasLimitAt cancelled 2 (1 / 4) := by
  have hc1 : ContinuousAt (fun _ : ℝ => (1 : ℝ)) 2 :=
    continuousAt_const
  have hcx : ContinuousAt (fun x : ℝ => x + 2) 2 :=
    continuousAt_id.add continuousAt_const
  have hc : ContinuousAt (fun x : ℝ => 1 / (x + 2)) 2 :=
    hc1.div hcx (by norm_num)
  have ht := hc.tendsto.mono_left
    (show nhdsWithin (2 : ℝ) ({2} : Set ℝ)ᶜ ≤ nhds 2 from inf_le_left)
  unfold HasLimitAt cancelled
  convert ht using 1 <;> norm_num

/-- Source: `proof_gap/exercise_421/4.txt`. -/
theorem gap4 : HasLimitAt original 2 (1 / 4) := by
  exact gap1.mpr (gap2.mpr gap3)

end

end ProofGap.Exercise421
