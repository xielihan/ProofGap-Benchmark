import ProofGapLean.Prelude.Sequences
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise666

noncomputable section

def f (x : ℝ) : ℝ := x ^ 2
def δ (ε : ℝ) : ℝ := min (ε / 11) 1

/-- Source: `proof_gap/exercise_666/1.txt`. -/
theorem gap1 (x ε : ℝ) (hε : 0 < ε)
    (h : |x - 5| * |x + 5| < ε) :
    |x ^ 2 - 25| < ε := by
  calc
    |x ^ 2 - 25| = |(x - 5) * (x + 5)| := by ring
    _ = |x - 5| * |x + 5| := by rw [abs_mul]
    _ < ε := h

/-- Source: `proof_gap/exercise_666/2.txt`. -/
theorem gap2 (x ε : ℝ) (hε : 0 < ε)
    (h : |x - 5| * |x + 5| < ε) :
    |x ^ 2 - 25| < ε := by
  exact gap1 x ε hε h

/-- Source: `proof_gap/exercise_666/3.txt`. -/
theorem gap3 (x ε : ℝ) (hε : 0 < ε) (h : |x - 5| < 1) :
    4 < x := by
  have hlower := (abs_lt.mp h).1
  linarith

/-- Source: `proof_gap/exercise_666/4.txt`. -/
theorem gap4 (x ε : ℝ) (hε : 0 < ε) (h : |x - 5| < 1) :
    x < 6 := by
  have hupper := (abs_lt.mp h).2
  linarith

/-- Source: `proof_gap/exercise_666/5.txt`. -/
theorem gap5 (x ε : ℝ) (hε : 0 < ε) (h : |x - 5| < 1) :
    (4 : ℝ) < 6 := by
  norm_num

/-- Source: `proof_gap/exercise_666/6.txt`. -/
theorem gap6 (x ε : ℝ) (hε : 0 < ε) (h : |x - 5| < 1) :
    9 < x + 5 := by
  linarith [gap3 x ε hε h]

/-- Source: `proof_gap/exercise_666/7.txt`. -/
theorem gap7 (x ε : ℝ) (hε : 0 < ε) (h : |x - 5| < 1) :
    x + 5 < 11 := by
  linarith [gap4 x ε hε h]

/-- Source: `proof_gap/exercise_666/8.txt`. -/
theorem gap8 (x ε : ℝ) (hε : 0 < ε) (h : |x - 5| < 1) :
    (9 : ℝ) < 11 := by
  norm_num

/-- Source: `proof_gap/exercise_666/9.txt`; add the local bound `|x-5|<1` needed to control `|x+5|`. -/
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

/-- Source: `proof_gap/exercise_666/10.txt`; add the same omitted local bound. -/
theorem gap10 (x ε : ℝ) (hε : 0 < ε)
    (hlocal : |x - 5| < 1) (hsmall : |x - 5| < ε / 11) :
    |x - 5| * |x + 5| < ε := by
  exact gap9 x ε hε hlocal hsmall

/-- Source: `proof_gap/exercise_666/11.txt`; remove shadowed quantifiers. -/
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

/-- Source: `proof_gap/exercise_666/12.txt`; correct decimal rounding: `δ(1)=1/11`, not `0.09`. -/
theorem gap12 : δ 1 = (1 / 11 : ℝ) := by
  rw [δ, min_eq_left] <;> norm_num

/-- Source: `proof_gap/exercise_666/13.txt`; correct decimal rounding to the exact value. -/
theorem gap13 : δ (1 / 10) = (1 / 110 : ℝ) := by
  rw [δ, min_eq_left] <;> norm_num

/-- Source: `proof_gap/exercise_666/14.txt`; correct decimal rounding to the exact value. -/
theorem gap14 : δ (1 / 100) = (1 / 1100 : ℝ) := by
  rw [δ, min_eq_left] <;> norm_num

/-- Source: `proof_gap/exercise_666/15.txt`; correct decimal rounding to the exact value. -/
theorem gap15 : δ (1 / 1000) = (1 / 11000 : ℝ) := by
  rw [δ, min_eq_left] <;> norm_num

/-- Source: `proof_gap/exercise_666/16.txt`. -/
theorem gap16 (ε : ℝ) : δ ε = min (ε / 11) 1 := by
  rfl

/-- Source: `proof_gap/exercise_666/17.txt`. -/
theorem gap17 : ContinuousAt f 5 := by
  simpa [f] using
    (continuousAt_id.pow 2 : ContinuousAt (fun x : ℝ => x ^ 2) 5)

/-- Source: `proof_gap/exercise_666/18.txt`. -/
theorem gap18 : ContinuousAt f 5 := by
  exact gap17

end

end ProofGap.Exercise666
