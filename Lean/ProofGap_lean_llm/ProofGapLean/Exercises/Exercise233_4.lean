import ProofGapLean.Prelude.Elementary

namespace ProofGap.Exercise233_4

noncomputable section

def f (x : ℝ) : ℝ := Real.sin x ^ 2

def IsLeastPositivePeriod (g : ℝ → ℝ) (T : ℝ) : Prop :=
  0 < T ∧ Function.Periodic g T ∧
    ∀ T', 0 < T' → Function.Periodic g T' → T ≤ T'

/-- Source: `proof_gap/exercise_233_4/1.txt`. -/
theorem gap1 : Function.Periodic f Real.pi := by
  intro x
  simp [f, Real.sin_add_pi]

/-- Source: `proof_gap/exercise_233_4/2.txt`; represent `min` by the least-positive-period predicate. -/
theorem gap2 : IsLeastPositivePeriod f Real.pi := by
  refine ⟨Real.pi_pos, gap1, ?_⟩
  intro T hT hperiodic
  by_contra hnot
  have hlt : T < Real.pi := lt_of_not_ge hnot
  have hsin_pos : 0 < Real.sin T :=
    Real.sin_pos_of_pos_of_lt_pi hT hlt
  have hsin_sq_zero : Real.sin T ^ 2 = 0 := by
    simpa [f] using hperiodic 0
  exact (ne_of_gt (pow_pos hsin_pos 2)) hsin_sq_zero

end

end ProofGap.Exercise233_4
