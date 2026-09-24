import ProofGapLean.Prelude.Sequences
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

namespace ProofGap.Exercise412

noncomputable section

def original (x : ℝ) : ℝ :=
  ((1 + x) * (1 + 2 * x) * (1 + 3 * x) - 1) / x
def simplified (x : ℝ) : ℝ := 6 + 11 * x + 6 * x ^ 2
def HasLimitAt (f : ℝ → ℝ) (a L : ℝ) : Prop :=
  Filter.Tendsto f (nhdsWithin a ({a} : Set ℝ)ᶜ) (nhds L)

/-- Exercise 412, gap 1. -/
theorem gap1 : ∀ x : ℝ,
    (1 + x) * (1 + 2 * x) * (1 + 3 * x) =
      1 + 6 * x + 11 * x ^ 2 + 6 * x ^ 3 := by
  intro x
  ring

/-- Exercise 412, gap 2. -/
theorem gap2 : HasLimitAt original 0 6 ↔ HasLimitAt simplified 0 6 := by
  have hevent :
      original =ᶠ[nhdsWithin 0 ({0} : Set ℝ)ᶜ] simplified := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx0 : x ≠ 0 := by simpa using hx
    simp only [original, simplified]
    field_simp [hx0]
    ring
  exact Filter.tendsto_congr' hevent

/-- Exercise 412, gap 3. -/
theorem gap3 : HasLimitAt simplified 0 6 := by
  have hc : ContinuousAt simplified 0 := by
    change ContinuousAt (fun x : ℝ => 6 + 11 * x + 6 * x ^ 2) 0
    fun_prop
  have ht :
      Filter.Tendsto simplified (nhdsWithin 0 ({0} : Set ℝ)ᶜ)
        (nhds (simplified 0)) :=
    hc.tendsto.mono_left inf_le_left
  simpa [HasLimitAt, simplified] using ht

/-- Exercise 412, gap 4. -/
theorem gap4 : HasLimitAt original 0 6 := by
  exact gap2.mpr gap3

end

end ProofGap.Exercise412
