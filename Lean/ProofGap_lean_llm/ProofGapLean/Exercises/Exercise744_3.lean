import ProofGapLean.Prelude.Full

namespace ProofGap.Exercise744_3

noncomputable section

def signFn (x : ℝ) : ℝ := Real.sign x
def fractionalShift (x : ℝ) : ℝ := 1 + x - (⌊x⌋ : ℝ)

/-- Source: `proof_gap/exercise_744_3/1.txt`. -/
theorem gap1 : ∀ x, signFn (fractionalShift x) = 1 := by
  intro x
  unfold signFn
  apply Real.sign_of_pos
  unfold fractionalShift
  have hx : (⌊x⌋ : ℝ) ≤ x := Int.floor_le x
  linarith

/-- Source: `proof_gap/exercise_744_3/2.txt`. -/
theorem gap2 : Continuous (fun x => signFn (fractionalShift x)) := by
  have h : (fun x : ℝ => signFn (fractionalShift x)) = (fun _ : ℝ => 1) := by
    funext x
    exact gap1 x
  rw [h]
  exact continuous_const

/-- Source: `proof_gap/exercise_744_3/3.txt`. -/
theorem gap3 : ∀ x, fractionalShift (signFn x) = 1 := by
  intro x
  rcases lt_trichotomy x 0 with hx | hx | hx
  · simp only [fractionalShift, signFn, Real.sign_of_neg hx]
    norm_num
  · subst x
    simp [fractionalShift, signFn]
  · simp [fractionalShift, signFn, Real.sign_of_pos hx]

/-- Source: `proof_gap/exercise_744_3/4.txt`. -/
theorem gap4 : Continuous (fun x => fractionalShift (signFn x)) := by
  have h : (fun x : ℝ => fractionalShift (signFn x)) = (fun _ : ℝ => 1) := by
    funext x
    exact gap3 x
  rw [h]
  exact continuous_const

end

end ProofGap.Exercise744_3
