import ProofGapLean.Prelude.Elementary

/-!
# Exercise 28

Semantic formalization of `proof_gap/exercise_28/{1,...,6}.txt`.
-/

namespace ProofGap.Exercise28

def Original (x : ℝ) : Prop :=
  abs (|x + 1| - |x - 1|) < 1

/-- Source: `proof_gap/exercise_28/1.txt`. -/
theorem gap1 (x : ℝ) :
    Original x ↔ x ^ 2 + (1 / 2 : ℝ) < |x ^ 2 - 1| := by
  let d : ℝ := abs (|x + 1| - |x - 1|)
  have hid :
      d ^ 2 = 2 * x ^ 2 + 2 - 2 * abs (x ^ 2 - 1) := by
    dsimp [d]
    rw [sq_abs]
    calc
      (|x + 1| - |x - 1|) ^ 2 =
          |x + 1| ^ 2 - 2 * (|x + 1| * |x - 1|) + |x - 1| ^ 2 := by ring
      _ = (x + 1) ^ 2 - 2 * abs ((x + 1) * (x - 1)) + (x - 1) ^ 2 := by
        rw [sq_abs, sq_abs, abs_mul]
      _ = 2 * x ^ 2 + 2 - 2 * abs (x ^ 2 - 1) := by
        have hprod : (x + 1) * (x - 1) = x ^ 2 - 1 := by ring
        rw [hprod]
        ring
  change d < 1 ↔ x ^ 2 + (1 / 2 : ℝ) < |x ^ 2 - 1|
  constructor
  · intro hd
    have hd2 : d ^ 2 < (1 : ℝ) ^ 2 :=
      (sq_lt_sq₀ (by dsimp [d]; positivity) (by norm_num)).2 hd
    nlinarith
  · intro h
    apply (sq_lt_sq₀ (by dsimp [d]; positivity) (by norm_num)).1
    nlinarith

/-- Source: `proof_gap/exercise_28/2.txt`. -/
theorem gap2
    (x : ℝ)
    (h1 : Original x ↔ x ^ 2 + (1 / 2 : ℝ) < |x ^ 2 - 1|) :
    Original x ↔
      x ^ 2 - 1 > x ^ 2 + (1 / 2 : ℝ) ∨
      x ^ 2 - 1 < -(x ^ 2 + (1 / 2 : ℝ)) := by
  rw [h1]
  by_cases hnonneg : 0 ≤ x ^ 2 - 1
  · rw [abs_of_nonneg hnonneg]
    constructor
    · intro h
      exact Or.inl h
    · rintro (h | h)
      · exact h
      · nlinarith
  · rw [abs_of_neg (lt_of_not_ge hnonneg)]
    constructor
    · intro h
      right
      linarith
    · rintro (h | h)
      · nlinarith
      · linarith

/-- Source: `proof_gap/exercise_28/3.txt`; repaired to the impossible branch alone. -/
theorem gap3
    (x : ℝ)
    (h2 : Original x ↔
      x ^ 2 - 1 > x ^ 2 + (1 / 2 : ℝ) ∨
      x ^ 2 - 1 < -(x ^ 2 + (1 / 2 : ℝ))) :
    ¬ x ^ 2 - 1 > x ^ 2 + (1 / 2 : ℝ) := by
  linarith

/-- Source: `proof_gap/exercise_28/4.txt`. -/
theorem gap4
    (x : ℝ)
    (h2 : Original x ↔
      x ^ 2 - 1 > x ^ 2 + (1 / 2 : ℝ) ∨
      x ^ 2 - 1 < -(x ^ 2 + (1 / 2 : ℝ)))
    (h3 : ¬ x ^ 2 - 1 > x ^ 2 + (1 / 2 : ℝ)) :
    Original x ↔ x ^ 2 - 1 < -(x ^ 2 + (1 / 2 : ℝ)) := by
  rw [h2]
  simp only [h3, false_or]

/-- Source: `proof_gap/exercise_28/5.txt`. -/
theorem gap5
    (x : ℝ)
    (h4 : Original x ↔ x ^ 2 - 1 < -(x ^ 2 + (1 / 2 : ℝ))) :
    Original x ↔ x ^ 2 < (1 / 4 : ℝ) := by
  rw [h4]
  constructor <;> intro h <;> linarith

/-- Source: `proof_gap/exercise_28/6.txt`. -/
theorem gap6
    (x : ℝ)
    (h5 : Original x ↔ x ^ 2 < (1 / 4 : ℝ)) :
    x ∈ {y : ℝ | |y| < (1 / 2 : ℝ)} ↔ Original x := by
  change |x| < (1 / 2 : ℝ) ↔ Original x
  rw [h5]
  have hiff :=
    (sq_lt_sq₀ (abs_nonneg x) (by norm_num : (0 : ℝ) ≤ 1 / 2))
  norm_num [sq_abs] at hiff
  exact hiff.symm

end ProofGap.Exercise28
