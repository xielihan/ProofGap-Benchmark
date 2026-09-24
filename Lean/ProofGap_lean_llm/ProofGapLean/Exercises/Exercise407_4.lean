import ProofGapLean.Prelude.Core

namespace ProofGap.Exercise407_4

noncomputable section

def ApproachesAboveAt (f : ℝ → ℝ) (a b : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x,
    0 < |x - a| → |x - a| < δ →
      0 < f x - b ∧ f x - b < ε

def f (x : ℝ) : ℝ := x ^ 2

/-- Source: `proof_gap/exercise_407_4/1.txt`; bind `y=f(x)` and stop shadowing `a,δ`. -/
theorem gap1 : ∀ ε > 0, ∃ δ > 0, ∀ x,
    0 < |x| → |x| < δ → 0 < f x ∧ f x < ε := by
  intro ε hε
  refine ⟨min 1 ε, lt_min zero_lt_one hε, ?_⟩
  intro x hx0 hxδ
  have hx1 : |x| < 1 := lt_of_lt_of_le hxδ (min_le_left 1 ε)
  have hxε : |x| < ε := lt_of_lt_of_le hxδ (min_le_right 1 ε)
  constructor
  · change 0 < x ^ 2
    simpa [pow_two] using (mul_self_pos.mpr (abs_pos.mp hx0))
  · calc
      f x = |x| ^ 2 := by rw [f, sq_abs]
      _ = |x| * |x| := pow_two _
      _ < |x| * 1 := mul_lt_mul_of_pos_left hx1 hx0
      _ = |x| := mul_one _
      _ < ε := hxε

/-- Source: `proof_gap/exercise_407_4/2.txt`; replace the false universal limit claim by its defining equivalence. -/
theorem gap2 (g : ℝ → ℝ) (a b : ℝ) :
    ApproachesAboveAt g a b ↔
      ∀ ε > 0, ∃ δ > 0, ∀ x,
        0 < |x - a| → |x - a| < δ →
          0 < g x - b ∧ g x - b < ε := by
  rfl

/-- Source: `proof_gap/exercise_407_4/3.txt`; restrict the strict inequality to the punctured neighborhood. -/
theorem gap3 : ∀ x : ℝ, x ≠ 0 → 0 < f x := by
  intro x hx
  change 0 < x ^ 2
  simpa [pow_two] using (mul_self_pos.mpr hx)

/-- Source: `proof_gap/exercise_407_4/4.txt`; define the previously free function. -/
theorem gap4 : ApproachesAboveAt f 0 0 := by
  simpa only [ApproachesAboveAt, sub_zero] using gap1

/-- Source: `proof_gap/exercise_407_4/5.txt`; exclude the limit point where equality holds. -/
theorem gap5 : ∀ x : ℝ, x ≠ 0 → 0 < f x := by
  exact gap3

end

end ProofGap.Exercise407_4
