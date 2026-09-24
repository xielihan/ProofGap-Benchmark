import ProofGapLean.Prelude.Sequences
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise423

noncomputable section

def original (x : ℝ) : ℝ :=
  (x ^ 2 - x - 2) ^ 20 / (x ^ 3 - 12 * x + 16) ^ 10
def factored (x : ℝ) : ℝ :=
  ((x - 2) ^ 20 * (x + 1) ^ 20) /
    ((x - 2) ^ 20 * (x + 4) ^ 10)
def cancelled (x : ℝ) : ℝ := (x + 1) ^ 20 / (x + 4) ^ 10
def HasLimitAt (f : ℝ → ℝ) (a L : ℝ) : Prop :=
  Filter.Tendsto f (nhdsWithin a ({a} : Set ℝ)ᶜ) (nhds L)

/-- Exercise 423, gap 1. -/
theorem gap1 : HasLimitAt original 2 (((3 : ℝ) / 2) ^ 10) ↔
    HasLimitAt factored 2 (((3 : ℝ) / 2) ^ 10) := by
  have h : original = factored := by
    funext x
    unfold original factored
    congr 1 <;> ring
  rw [h]

/-- Exercise 423, gap 2. -/
theorem gap2 : HasLimitAt factored 2 (((3 : ℝ) / 2) ^ 10) ↔
    HasLimitAt cancelled 2 (((3 : ℝ) / 2) ^ 10) := by
  unfold HasLimitAt
  apply Filter.tendsto_congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx2 : x ≠ 2 := by
    simpa using hx
  have hpow : (x - 2) ^ 20 ≠ 0 :=
    pow_ne_zero _ (sub_ne_zero.mpr hx2)
  simpa [factored, cancelled] using
    (mul_div_mul_left ((x + 1) ^ 20) ((x + 4) ^ 10) hpow)

/-- Exercise 423, gap 3. -/
theorem gap3 : HasLimitAt cancelled 2 ((3 : ℝ) ^ 20 / 6 ^ 10) := by
  unfold HasLimitAt
  have hcont : ContinuousAt cancelled 2 := by
    unfold cancelled
    exact
      ((continuousAt_id.add
          (continuousAt_const : ContinuousAt (fun _ : ℝ => (1 : ℝ)) 2)).pow 20).div
        ((continuousAt_id.add
          (continuousAt_const : ContinuousAt (fun _ : ℝ => (4 : ℝ)) 2)).pow 10)
        (by norm_num)
  have ht : Filter.Tendsto cancelled
      (nhdsWithin 2 ({2} : Set ℝ)ᶜ) (nhds (cancelled 2)) :=
    hcont.tendsto.mono_left inf_le_left
  convert ht using 1 <;> norm_num [cancelled]

/-- Exercise 423, gap 4. -/
theorem gap4 : (3 : ℝ) ^ 20 / 6 ^ 10 = ((3 : ℝ) / 2) ^ 10 := by
  norm_num

/-- Exercise 423, gap 5. -/
theorem gap5 : HasLimitAt original 2 (((3 : ℝ) / 2) ^ 10) := by
  apply gap1.mpr
  apply gap2.mpr
  rw [← gap4]
  exact gap3

end

end ProofGap.Exercise423
