import ProofGapLean.Prelude.Elementary

/-!
# Exercise 27

Semantic formalization of `proof_gap/exercise_27/{1,...,6}.txt`.
-/

namespace ProofGap.Exercise27

def Original (x : ℝ) : Prop :=
  |x + 2| - |x| > 1

/-- Source: `proof_gap/exercise_27/1.txt`; the omitted original inequality is explicit. -/
theorem gap1
    (x : ℝ)
    (h0 : Original x) :
    1 + |x| < |x + 2| := by
  unfold Original at h0
  linarith

/-- Source: `proof_gap/exercise_27/2.txt`. -/
theorem gap2
    (x : ℝ)
    (h1 : 1 + |x| < |x + 2|) :
    2 * |x| < 4 * x + 3 := by
  have hprod :
      0 < (|x + 2| - (1 + |x|)) * (|x + 2| + (1 + |x|)) :=
    mul_pos (sub_pos.mpr h1) (by positivity)
  nlinarith [sq_abs x, sq_abs (x + 2)]

/-- Source: `proof_gap/exercise_27/3.txt`. -/
theorem gap3
    (x : ℝ)
    (h2 : 2 * |x| < 4 * x + 3) :
    4 * x ^ 2 + 8 * x + 3 > 0 := by
  have hright : 0 < 4 * x + 3 :=
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (abs_nonneg x)).trans_lt h2
  have hprod :
      0 < (4 * x + 3 - 2 * |x|) * (4 * x + 3 + 2 * |x|) :=
    mul_pos (sub_pos.mpr h2) (by linarith [abs_nonneg x])
  nlinarith [sq_abs x]

/-- Source: `proof_gap/exercise_27/4.txt`. -/
theorem gap4
    (x : ℝ)
    (h3 : 4 * x ^ 2 + 8 * x + 3 > 0) :
    x > -(1 / 2 : ℝ) ∨ x < -(3 / 2 : ℝ) := by
  by_cases hx : x > -(1 / 2 : ℝ)
  · exact Or.inl hx
  · right
    by_contra hnot
    have hprod : (2 * x + 1) * (2 * x + 3) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
    nlinarith

/-- Source: `proof_gap/exercise_27/5.txt`. -/
theorem gap5
    (x : ℝ)
    (h1 : 1 + |x| < |x + 2|)
    (h4 : x > -(1 / 2 : ℝ) ∨ x < -(3 / 2 : ℝ)) :
    ¬ x < -(3 / 2 : ℝ) := by
  intro hx
  have hxneg : x < 0 := by linarith
  rw [abs_of_neg hxneg] at h1
  by_cases hx2 : 0 ≤ x + 2
  · rw [abs_of_nonneg hx2] at h1
    linarith
  · rw [abs_of_neg (lt_of_not_ge hx2)] at h1
    linarith

/-- Source: `proof_gap/exercise_27/6.txt`. -/
theorem gap6
    (x : ℝ)
    (h4 : x > -(1 / 2 : ℝ) ∨ x < -(3 / 2 : ℝ))
    (h5 : ¬ x < -(3 / 2 : ℝ)) :
    x ∈ {y : ℝ | y > -(1 / 2 : ℝ)} ↔ Original x := by
  have hxgt : x > -(1 / 2 : ℝ) := h4.resolve_right h5
  have horiginal : Original x := by
    unfold Original
    rw [abs_of_pos (by linarith : 0 < x + 2)]
    by_cases hx0 : 0 ≤ x
    · rw [abs_of_nonneg hx0]
      linarith
    · rw [abs_of_neg (lt_of_not_ge hx0)]
      linarith
  change x > -(1 / 2 : ℝ) ↔ Original x
  exact ⟨fun _ => horiginal, fun _ => hxgt⟩

end ProofGap.Exercise27
