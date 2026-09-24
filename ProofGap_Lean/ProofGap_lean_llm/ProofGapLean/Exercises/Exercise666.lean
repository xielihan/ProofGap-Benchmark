import ProofGapLean.Prelude.Sequences
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise666

noncomputable section

def f (x : ℝ) : ℝ := x ^ 2
def δ (ε : ℝ) : ℝ := min (ε / 11) 1

/-- Exercise 666, gap 1. -/
theorem gap1 (x ε : ℝ) (hε : 0 < ε)
    (h : |x - 5| * |x + 5| < ε) :
    |x ^ 2 - 25| < ε := by
  calc
    |x ^ 2 - 25| = |(x - 5) * (x + 5)| := by ring
    _ = |x - 5| * |x + 5| := by rw [abs_mul]
    _ < ε := h

/-- Exercise 666, gap 2. -/
theorem gap2 (x ε : ℝ) (hε : 0 < ε)
    (h : |x - 5| * |x + 5| < ε) :
    |x ^ 2 - 25| < ε := by
  exact gap1 x ε hε h

/-- Exercise 666, gap 3. -/
theorem gap3 (x ε : ℝ) (hε : 0 < ε) (h : |x - 5| < 1) :
    4 < x := by
  have hlower := (abs_lt.mp h).1
  linarith

/-- Exercise 666, gap 4. -/
theorem gap4 (x ε : ℝ) (hε : 0 < ε) (h : |x - 5| < 1) :
    x < 6 := by
  have hupper := (abs_lt.mp h).2
  linarith

/-- Exercise 666, gap 5. -/
theorem gap5 (x ε : ℝ) (hε : 0 < ε) (h : |x - 5| < 1) :
    (4 : ℝ) < 6 := by
  norm_num

/-- Exercise 666, gap 6. -/
theorem gap6 (x ε : ℝ) (hε : 0 < ε) (h : |x - 5| < 1) :
    9 < x + 5 := by
  linarith [gap3 x ε hε h]

/-- Exercise 666, gap 7. -/
theorem gap7 (x ε : ℝ) (hε : 0 < ε) (h : |x - 5| < 1) :
    x + 5 < 11 := by
  linarith [gap4 x ε hε h]

/-- Exercise 666, gap 8. -/
theorem gap8 (x ε : ℝ) (hε : 0 < ε) (h : |x - 5| < 1) :
    (9 : ℝ) < 11 := by
  norm_num

/-- Exercise 666, gap 9; add the local bound `|x-5|<1` needed to control `|x+5|`. -/
theorem gap9 (x ε : ℝ) (hε : 0 < ε)
    (hlocal : |x - 5| < 1) (hsmall : |x - 5| < ε / 11) :
    |x - 5| * |x + 5| < ε := by
  have hx5pos : 0 < x + 5 := by
    linarith [gap6 x ε hε hlocal]
  have hx5lt : x + 5 < 11 := gap7 x ε hε hlocal
  rw [abs_of_pos hx5pos]
  calc
    |x - 5| * (x + 5) < (ε / 11) * (x + 5) :=
      mul_lt_mul_of_pos_right hsmall hx5pos
    _ < (ε / 11) * 11 :=
      mul_lt_mul_of_pos_left hx5lt (div_pos hε (by norm_num))
    _ = ε := by ring

/-- Exercise 666, gap 10; add the same omitted local bound. -/
theorem gap10 (x ε : ℝ) (hε : 0 < ε)
    (hlocal : |x - 5| < 1) (hsmall : |x - 5| < ε / 11) :
    |x - 5| * |x + 5| < ε := by
  exact gap9 x ε hε hlocal hsmall

/-- Exercise 666, gap 11; remove shadowed quantifiers. -/
theorem gap11 (ε : ℝ) (hε : 0 < ε) :
    0 < δ ε ∧ ∀ x, |x - 5| < δ ε → |x ^ 2 - 25| < ε := by
  constructor
  · rw [δ]
    exact lt_min (div_pos hε (by norm_num)) (by norm_num)
  · intro x hx
    rw [δ] at hx
    have hlocal : |x - 5| < 1 :=
      lt_of_lt_of_le hx (min_le_right (ε / 11) 1)
    have hsmall : |x - 5| < ε / 11 :=
      lt_of_lt_of_le hx (min_le_left (ε / 11) 1)
    exact gap1 x ε hε (gap9 x ε hε hlocal hsmall)

/-- Exercise 666, gap 12; correct decimal rounding: `δ(1)=1/11`, not `0.09`. -/
theorem gap12 : δ 1 = (1 / 11 : ℝ) := by
  rw [δ, min_eq_left] <;> norm_num

/-- Exercise 666, gap 13; correct decimal rounding to the exact value. -/
theorem gap13 : δ (1 / 10) = (1 / 110 : ℝ) := by
  rw [δ, min_eq_left] <;> norm_num

/-- Exercise 666, gap 14; correct decimal rounding to the exact value. -/
theorem gap14 : δ (1 / 100) = (1 / 1100 : ℝ) := by
  rw [δ, min_eq_left] <;> norm_num

/-- Exercise 666, gap 15; correct decimal rounding to the exact value. -/
theorem gap15 : δ (1 / 1000) = (1 / 11000 : ℝ) := by
  rw [δ, min_eq_left] <;> norm_num

/-- Exercise 666, gap 16. -/
theorem gap16 (ε : ℝ) : δ ε = min (ε / 11) 1 := by
  rfl

/-- Exercise 666, gap 17. -/
theorem gap17 : ContinuousAt f 5 := by
  simpa [f] using
    (continuousAt_id.pow 2 : ContinuousAt (fun x : ℝ => x ^ 2) 5)

/-- Exercise 666, gap 18. -/
theorem gap18 : ContinuousAt f 5 := by
  exact gap17

end

end ProofGap.Exercise666
