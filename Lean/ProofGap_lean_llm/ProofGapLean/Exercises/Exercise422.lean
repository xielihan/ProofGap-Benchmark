import ProofGapLean.Prelude.Sequences
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise422

noncomputable section

def original (x : ℝ) : ℝ := (x ^ 3 - 2 * x - 1) / (x ^ 5 - 2 * x - 1)
def factored (x : ℝ) : ℝ :=
  ((x + 1) * (x ^ 2 - x - 1)) /
    ((x + 1) * (x ^ 4 - x ^ 3 + x ^ 2 - x - 1))
def cancelled (x : ℝ) : ℝ :=
  (x ^ 2 - x - 1) / (x ^ 4 - x ^ 3 + x ^ 2 - x - 1)
def HasLimitAt (f : ℝ → ℝ) (a L : ℝ) : Prop :=
  Filter.Tendsto f (nhdsWithin a ({a} : Set ℝ)ᶜ) (nhds L)

/-- Source: `proof_gap/exercise_422/1.txt`. -/
theorem gap1 : HasLimitAt original (-1) (1 / 3) ↔
    HasLimitAt factored (-1) (1 / 3) := by
  have h : original = factored := by
    funext x
    unfold original factored
    congr 1 <;> ring
  rw [h]

/-- Source: `proof_gap/exercise_422/2.txt`. -/
theorem gap2 : HasLimitAt factored (-1) (1 / 3) ↔
    HasLimitAt cancelled (-1) (1 / 3) := by
  unfold HasLimitAt
  have heq :
      factored =ᶠ[nhdsWithin (-1) ({-1} : Set ℝ)ᶜ] cancelled := by
    refine Filter.Eventually.mono self_mem_nhdsWithin ?_
    intro x hx
    have hx' : x ≠ (-1 : ℝ) := by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hx
    have hx1 : x + 1 ≠ 0 := by
      intro h
      apply hx'
      linarith
    unfold factored cancelled
    exact mul_div_mul_left _ _ hx1
  change
    (Filter.map factored (nhdsWithin (-1) ({-1} : Set ℝ)ᶜ) ≤ nhds (1 / 3)) ↔
      Filter.map cancelled (nhdsWithin (-1) ({-1} : Set ℝ)ᶜ) ≤ nhds (1 / 3)
  rw [Filter.map_congr heq]

/-- Source: `proof_gap/exercise_422/3.txt`. -/
theorem gap3 : HasLimitAt cancelled (-1) (1 / 3) := by
  have hnum :
      ContinuousAt (fun x : ℝ => x ^ 2 - x - 1) (-1) :=
    ((continuousAt_id.pow 2).sub continuousAt_id).sub continuousAt_const
  have hden :
      ContinuousAt
        (fun x : ℝ => x ^ 4 - x ^ 3 + x ^ 2 - x - 1) (-1) :=
    ((((continuousAt_id.pow 4).sub (continuousAt_id.pow 3)).add
      (continuousAt_id.pow 2)).sub continuousAt_id).sub continuousAt_const
  have hc : ContinuousAt cancelled (-1) := by
    unfold cancelled
    exact hnum.div hden (by norm_num)
  have ht : Filter.Tendsto cancelled
      (nhdsWithin (-1) ({-1} : Set ℝ)ᶜ) (nhds (cancelled (-1))) :=
    hc.tendsto.mono_left inf_le_left
  have hvalue : cancelled (-1) = (1 / 3 : ℝ) := by
    norm_num [cancelled]
  rw [hvalue] at ht
  exact ht

/-- Source: `proof_gap/exercise_422/4.txt`. -/
theorem gap4 : HasLimitAt original (-1) (1 / 3) := by
  exact gap1.mpr (gap2.mpr gap3)

end

end ProofGap.Exercise422
