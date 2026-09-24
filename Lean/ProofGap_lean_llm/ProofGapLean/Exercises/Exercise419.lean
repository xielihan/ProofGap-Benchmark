import ProofGapLean.Prelude.Sequences
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise419

noncomputable section

def original (x : ℝ) : ℝ :=
  (x ^ 3 - 3 * x + 2) / (x ^ 4 - 4 * x + 3)
def factored (x : ℝ) : ℝ :=
  ((x - 1) ^ 2 * (x + 2)) / ((x - 1) ^ 2 * (x ^ 2 + 2 * x + 3))
def cancelled (x : ℝ) : ℝ := (x + 2) / (x ^ 2 + 2 * x + 3)
def HasLimitAt (f : ℝ → ℝ) (a L : ℝ) : Prop :=
  Filter.Tendsto f (nhdsWithin a ({a} : Set ℝ)ᶜ) (nhds L)

/-- Exercise 419, gap 1. -/
theorem gap1 : ∀ x : ℝ,
    x ^ 3 - 3 * x + 2 = (x - 1) ^ 2 * (x + 2) := by
  intro x
  ring

/-- Exercise 419, gap 2. -/
theorem gap2 : ∀ x : ℝ,
    x ^ 4 - 4 * x + 3 = (x - 1) ^ 2 * (x ^ 2 + 2 * x + 3) := by
  intro x
  ring

/-- Exercise 419, gap 3. -/
theorem gap3 : HasLimitAt original 1 (1 / 2) ↔
    HasLimitAt factored 1 (1 / 2) := by
  have hfun : original = factored := by
    funext x
    unfold original factored
    rw [gap1 x, gap2 x]
  rw [hfun]

/-- Exercise 419, gap 4. -/
theorem gap4 : HasLimitAt factored 1 (1 / 2) ↔
    HasLimitAt cancelled 1 (1 / 2) := by
  unfold HasLimitAt
  have heq : factored =ᶠ[nhdsWithin (1 : ℝ) ({1} : Set ℝ)ᶜ] cancelled := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx1 : x ≠ (1 : ℝ) := by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hx
    have hxm : (x - 1) ^ 2 ≠ 0 :=
      pow_ne_zero 2 (sub_ne_zero.mpr hx1)
    unfold factored cancelled
    exact mul_div_mul_left (x + 2) (x ^ 2 + 2 * x + 3) hxm
  constructor
  · intro h
    exact Filter.Tendsto.congr' heq h
  · intro h
    exact Filter.Tendsto.congr' heq.symm h

/-- Exercise 419, gap 5. -/
theorem gap5 : HasLimitAt cancelled 1 (3 / 6) := by
  have hcont : ContinuousAt cancelled 1 := by
    unfold cancelled
    apply ContinuousAt.div
    · exact continuousAt_id.add continuousAt_const
    · exact ((continuousAt_id.pow 2).add
        (continuousAt_const.mul continuousAt_id)).add continuousAt_const
    · norm_num
  have hval : cancelled 1 = (3 : ℝ) / 6 := by
    norm_num [cancelled]
  unfold HasLimitAt
  rw [← hval]
  exact hcont.mono_left inf_le_left

/-- Exercise 419, gap 6. -/
theorem gap6 : (3 : ℝ) / 6 = 1 / 2 := by
  norm_num

/-- Exercise 419, gap 7. -/
theorem gap7 : HasLimitAt original 1 (1 / 2) := by
  apply gap3.mpr
  apply gap4.mpr
  rw [← gap6]
  exact gap5

end

end ProofGap.Exercise419
