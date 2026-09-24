import ProofGapLean.Prelude.Discrete
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise763

noncomputable section

local instance : DecidablePred (fun x : ℝ => x ∈ Set.range ((↑) : ℚ → ℝ)) :=
  Classical.decPred _

def f (x : ℝ) : ℝ := if x ∈ Set.range ((↑) : ℚ → ℝ) then x else -x

theorem gap1 : ¬ Monotone f := by
  intro hmono
  have hsqrt_irr : Real.sqrt (2 : ℝ) ∉ Set.range ((↑) : ℚ → ℝ) := by
    exact irrational_sqrt_two
  have hone_rat : (1 : ℝ) ∈ Set.range ((↑) : ℚ → ℝ) := by
    exact ⟨1, by norm_num⟩
  have hsqrt_nonneg : 0 ≤ Real.sqrt (2 : ℝ) := Real.sqrt_nonneg _
  have hsqrt_sq : (Real.sqrt (2 : ℝ)) ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num)
  have hone_le_sqrt : (1 : ℝ) ≤ Real.sqrt 2 := by
    nlinarith
  have hbad : (1 : ℝ) ≤ -Real.sqrt 2 := by
    simpa [f, hone_rat, hsqrt_irr] using hmono hone_le_sqrt
  nlinarith
theorem gap2 : ¬ Antitone f := by
  intro hanti
  have hone_rat : (1 : ℝ) ∈ Set.range ((↑) : ℚ → ℝ) := by
    exact ⟨1, by norm_num⟩
  have htwo_rat : (2 : ℝ) ∈ Set.range ((↑) : ℚ → ℝ) := by
    exact ⟨2, by norm_num⟩
  have hbad : (2 : ℝ) ≤ 1 := by
    simpa [f, hone_rat, htwo_rat] using
      hanti (show (1 : ℝ) ≤ 2 by norm_num)
  norm_num at hbad
theorem gap3 : Function.LeftInverse f f ∧ Function.RightInverse f f := by
  have hinv : ∀ x : ℝ, f (f x) = x := by
    intro x
    by_cases hx : x ∈ Set.range ((↑) : ℚ → ℝ)
    · simp [f, hx]
    · have hneg : -x ∉ Set.range ((↑) : ℚ → ℝ) := by
        rintro ⟨q, hq⟩
        apply hx
        refine ⟨-q, ?_⟩
        simpa using congrArg Neg.neg hq
      simp [f, hx, hneg]
  exact ⟨hinv, hinv⟩

end
end ProofGap.Exercise763
