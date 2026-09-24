import ProofGapLean.Prelude.Sequences
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise742_1

noncomputable section

def g (x : ℝ) : ℝ := if 0 ≤ x then 1 else -1
def f (_x : ℝ) : ℝ := 0

/-- Source: `proof_gap/exercise_742_1/1.txt`. -/
theorem gap1 : Continuous f := by
  simpa [f] using (continuous_const : Continuous (fun _ : ℝ => (0 : ℝ)))

/-- Source: `proof_gap/exercise_742_1/2.txt`. -/
theorem gap2 : ¬ ContinuousAt g 0 := by
  intro h
  rw [Metric.continuousAt_iff] at h
  obtain ⟨δ, hδ, hcont⟩ := h 1 (by norm_num)
  have hy : -δ / 2 < 0 := by
    linarith
  have hdist : dist (-δ / 2) (0 : ℝ) < δ := by
    rw [Real.dist_eq]
    have hnonpos : -δ / 2 - 0 ≤ 0 := by
      linarith
    rw [abs_of_nonpos hnonpos]
    linarith
  have hout := hcont hdist
  norm_num [g, not_le.mpr hy, Real.dist_eq] at hout

/-- Source: `proof_gap/exercise_742_1/3.txt`. -/
theorem gap3 : ∀ x, f x * g x = 0 := by
  intro x
  simp [f]

/-- Source: `proof_gap/exercise_742_1/4.txt`. -/
theorem gap4 : Continuous (fun x => f x * g x) := by
  simpa [f] using (continuous_const : Continuous (fun _ : ℝ => (0 : ℝ)))

end

end ProofGap.Exercise742_1
