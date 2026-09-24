import ProofGapLean.Prelude.Core

namespace ProofGap.Exercise407_1

noncomputable section

def ApproachesBelowAt (f : ℝ → ℝ) (a b : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x,
    0 < |x - a| → |x - a| < δ →
      0 < b - f x ∧ b - f x < ε

def f (x : ℝ) : ℝ := -x ^ 2

/-- Source: `proof_gap/exercise_407_1/1.txt`; bind `y` as `f(x)` and stop shadowing `a,δ`. -/
theorem gap1 : ∀ ε > 0, ∃ δ > 0, ∀ x,
    0 < |x| → |x| < δ → 0 < -f x ∧ -f x < ε := by
  intro ε hε
  refine ⟨min 1 ε, lt_min zero_lt_one hε, ?_⟩
  intro x hx0 hxδ
  simp only [f, neg_neg]
  constructor
  · exact sq_pos_of_ne_zero (abs_pos.mp hx0)
  · have hx1 : |x| < 1 := lt_of_lt_of_le hxδ (min_le_left 1 ε)
    have hxε : |x| < ε := lt_of_lt_of_le hxδ (min_le_right 1 ε)
    have hsquare : |x| ^ 2 < |x| := by
      calc
        |x| ^ 2 = |x| * |x| := pow_two _
        _ < |x| * 1 := mul_lt_mul_of_pos_left hx1 hx0
        _ = |x| := mul_one _
    simpa only [sq_abs] using lt_trans hsquare hxε

/-- Source: `proof_gap/exercise_407_1/2.txt`; replace the false universal limit claim by its defining equivalence. -/
theorem gap2 (g : ℝ → ℝ) (a b : ℝ) :
    ApproachesBelowAt g a b ↔
      ∀ ε > 0, ∃ δ > 0, ∀ x,
        0 < |x - a| → |x - a| < δ →
          0 < b - g x ∧ b - g x < ε := by
  rfl

/-- Source: `proof_gap/exercise_407_1/3.txt`; restrict the strict inequality to the punctured neighborhood. -/
theorem gap3 : ∀ x : ℝ, x ≠ 0 → f x < 0 := by
  intro x hx
  simpa only [f] using (neg_lt_zero.mpr (sq_pos_of_ne_zero hx))

/-- Source: `proof_gap/exercise_407_1/4.txt`; define the previously free function. -/
theorem gap4 : ApproachesBelowAt f 0 0 := by
  simpa only [ApproachesBelowAt, sub_zero, zero_sub] using gap1

/-- Source: `proof_gap/exercise_407_1/5.txt`; exclude the limit point where equality holds. -/
theorem gap5 : ∀ x : ℝ, x ≠ 0 → f x < 0 := by
  exact gap3

end

end ProofGap.Exercise407_1
