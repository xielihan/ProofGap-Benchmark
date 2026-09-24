import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise602

noncomputable section

def f (x : ℝ) : ℝ := Real.sqrt (max (Real.cos (1 / x)) 0)
def HasLimitAtZero (g : ℝ → ℝ) (L : ℝ) : Prop :=
  Filter.Tendsto g (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds L)

/-- Source: `proof_gap/exercise_602/1.txt`; use the nonnegative-part real extension of the partially defined radical. -/
theorem gap1 : ∃ M : ℝ, ∀ x : ℝ, |f x| ≤ M := by
  refine ⟨1, ?_⟩
  intro x
  change |Real.sqrt (max (Real.cos (1 / x)) 0)| ≤ 1
  rw [abs_of_nonneg (Real.sqrt_nonneg _)]
  have hnonneg : 0 ≤ max (Real.cos (1 / x)) 0 := le_max_right _ _
  have hle : max (Real.cos (1 / x)) 0 ≤ 1 :=
    max_le (Real.cos_le_one _) (by norm_num)
  have hsqrt := Real.sq_sqrt hnonneg
  have hsqrt_nonneg := Real.sqrt_nonneg (max (Real.cos (1 / x)) 0)
  nlinarith

/-- Source: `proof_gap/exercise_602/2.txt`; use the same total real extension. -/
theorem gap2 : HasLimitAtZero (fun x => x * f x) 0 := by
  unfold HasLimitAtZero
  rcases gap1 with ⟨M, hM⟩
  have hx : Filter.Tendsto (fun x : ℝ => x)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0) := by
    change Filter.map id (nhdsWithin 0 ({0} : Set ℝ)ᶜ) ≤ nhds 0
    rw [Filter.map_id]
    exact inf_le_left
  have habs : Filter.Tendsto (fun x : ℝ => |x|)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0) := by
    simpa using hx.abs
  have hconst : Filter.Tendsto (fun _ : ℝ => M)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds M) := tendsto_const_nhds
  have hupper : Filter.Tendsto (fun x : ℝ => M * |x|)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0) := by
    simpa using hconst.mul habs
  have hlower : Filter.Tendsto (fun x : ℝ => -(M * |x|))
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0) := by
    simpa using hupper.neg
  have hbound : ∀ x : ℝ, |x * f x| ≤ M * |x| := by
    intro x
    rw [abs_mul]
    calc
      |x| * |f x| ≤ |x| * M :=
        mul_le_mul_of_nonneg_left (hM x) (abs_nonneg x)
      _ = M * |x| := by rw [mul_comm]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hlower hupper
  · exact fun x => (abs_le.mp (hbound x)).1
  · exact fun x => (abs_le.mp (hbound x)).2

end

end ProofGap.Exercise602
