import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise744_1

noncomputable section

def f (x : ℝ) : ℝ := Real.sign x
def g (x : ℝ) : ℝ := 1 + x ^ 2

/-- Exercise 744_1, gap 1. -/
theorem gap1 : ∀ x, f (g x) = 1 := by
  intro x
  unfold f g
  exact Real.sign_of_pos (by nlinarith [sq_nonneg x])

/-- Exercise 744_1, gap 2. -/
theorem gap2 : Continuous (f ∘ g) := by
  have h : f ∘ g = fun _ : ℝ => (1 : ℝ) := by
    funext x
    exact gap1 x
  rw [h]
  exact continuous_const

/-- Exercise 744_1, gap 3. -/
theorem gap3 : ∀ x, g (f x) = if x = 0 then 1 else 2 := by
  intro x
  by_cases hx : x = 0
  · simp [hx, f, g]
  · rcases lt_or_gt_of_ne hx with hxneg | hxpos
    · simp [f, g, hx, Real.sign_of_neg hxneg]
      norm_num
    · simp [f, g, hx, Real.sign_of_pos hxpos]
      norm_num

/-- Exercise 744_1, gap 4. -/
theorem gap4 : ¬ ContinuousAt (g ∘ f) 0 := by
  intro h
  rw [Metric.continuousAt_iff] at h
  obtain ⟨δ, hδpos, hδ⟩ := h (1 / 2) (by norm_num)
  have hxpos : 0 < δ / 2 := by linarith
  have hdist : dist (δ / 2) 0 < δ := by
    have hhalf : δ / 2 < δ := by linarith
    rw [Real.dist_eq, sub_zero, abs_of_pos hxpos]
    exact hhalf
  have hclose := @hδ (δ / 2) hdist
  have hxne : δ / 2 ≠ 0 := ne_of_gt hxpos
  have haway : (g ∘ f) (δ / 2) = 2 := by
    simpa [Function.comp_def, hxne] using gap3 (δ / 2)
  have hzero : (g ∘ f) 0 = 1 := by
    simpa [Function.comp_def] using gap3 0
  rw [haway, hzero] at hclose
  norm_num [Real.dist_eq] at hclose

end

end ProofGap.Exercise744_1
