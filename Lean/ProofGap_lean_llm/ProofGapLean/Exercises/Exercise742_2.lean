import ProofGapLean.Prelude.Sequences
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise742_2

noncomputable section

def f (x : ℝ) : ℝ := if 0 ≤ x then 1 else -1
def g : ℝ → ℝ := f

theorem gap1 : ¬ ContinuousAt f 0 := by
  intro hcont
  rw [Metric.continuousAt_iff] at hcont
  obtain ⟨δ, hδpos, hδ⟩ := hcont 1 (by norm_num)
  have hneg : (-δ / 2 : ℝ) < 0 := by
    linarith
  have hdist : dist (-δ / 2 : ℝ) 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_neg hneg]
    linarith
  have hbad := hδ hdist
  have hnot : ¬ 0 ≤ (-δ / 2 : ℝ) := by
    linarith
  norm_num [f, hnot, Real.dist_eq] at hbad
theorem gap2 : ¬ ContinuousAt g 0 := by
  simpa [g] using gap1
theorem gap3 : ∀ x, f x * g x = 1 := by
  intro x
  unfold g f
  split <;> norm_num
theorem gap4 : Continuous (fun x => f x * g x) := by
  have hfun : (fun x : ℝ => f x * g x) = fun _ : ℝ => (1 : ℝ) := by
    funext x
    exact gap3 x
  rw [hfun]
  exact continuous_const

end
end ProofGap.Exercise742_2
