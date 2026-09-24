import ProofGapLean.Prelude.Sequences
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise741_2

noncomputable section

def f (x : ℝ) : ℝ := if 0 ≤ x then 1 else -1
def g (x : ℝ) : ℝ := if 0 ≤ x then -1 else 1

private theorem signStep_not_continuous (a b : ℝ) (hdist : dist b a = 2) :
    ¬ ContinuousAt (fun x : ℝ => if 0 ≤ x then a else b) 0 := by
  intro h
  rw [Metric.continuousAt_iff] at h
  obtain ⟨δ, hδ, hclose⟩ := h 1 zero_lt_one
  have hy_nonpos : -δ / 2 ≤ 0 := by
    linarith
  have hy : dist (-δ / 2 : ℝ) 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_nonpos hy_nonpos]
    linarith
  have hneg : ¬ 0 ≤ -δ / 2 := by
    linarith
  have hbad := @hclose (-δ / 2) hy
  simp [hneg] at hbad
  linarith

theorem gap1 : ¬ ContinuousAt f 0 := by
  simpa [f] using
    (signStep_not_continuous (1 : ℝ) (-1) (by norm_num [Real.dist_eq]))
theorem gap2 : ¬ ContinuousAt g 0 := by
  simpa [g] using
    (signStep_not_continuous (-1 : ℝ) 1 (by norm_num [Real.dist_eq]))
theorem gap3 : ∀ x, f x + g x = 0 := by
  intro x
  by_cases hx : 0 ≤ x <;> simp [f, g, hx]
theorem gap4 : Continuous (fun x => f x + g x) := by
  have h : (fun x : ℝ => f x + g x) = fun _ : ℝ => 0 := by
    funext x
    exact gap3 x
  rw [h]
  exact continuous_const

end
end ProofGap.Exercise741_2
