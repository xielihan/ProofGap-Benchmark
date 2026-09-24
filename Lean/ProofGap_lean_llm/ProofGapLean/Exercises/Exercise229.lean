import ProofGapLean.Prelude.Elementary
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise229

noncomputable section

def y (x : ℝ) : ℝ :=
  (Real.exp x - Real.exp (-x)) / (Real.exp x + Real.exp (-x))
def arctanh (t : ℝ) : ℝ := (1 / 2) * Real.log ((1 + t) / (1 - t))

/-- Source: `proof_gap/exercise_229/1.txt`. -/
theorem gap1 : ∀ x,
    y x = (Real.exp x - Real.exp (-x)) / (Real.exp x + Real.exp (-x)) := by
  intro x
  rfl

/-- Source: `proof_gap/exercise_229/2.txt`. -/
theorem gap2 : ∀ x,
    (Real.exp x - Real.exp (-x)) / (Real.exp x + Real.exp (-x)) =
      ((Real.exp x) ^ 2 - 1) / ((Real.exp x) ^ 2 + 1) := by
  intro x
  rw [Real.exp_neg]
  have hx : Real.exp x ≠ 0 := Real.exp_ne_zero x
  have hsum : Real.exp x + (Real.exp x)⁻¹ ≠ 0 := by
    positivity
  have hsquare : (Real.exp x) ^ 2 + 1 ≠ 0 := by
    positivity
  field_simp [hx, hsum, hsquare]

/-- Source: `proof_gap/exercise_229/3.txt`. -/
theorem gap3 : ∀ x,
    y x = ((Real.exp x) ^ 2 - 1) / ((Real.exp x) ^ 2 + 1) := by
  intro x
  simpa [y] using gap2 x

/-- Source: `proof_gap/exercise_229/4.txt`. -/
theorem gap4 : ∀ x, Real.exp (2 * x) = (1 + y x) / (1 - y x) := by
  intro x
  rw [gap3 x]
  have hdpos : 0 < (Real.exp x) ^ 2 + 1 := by
    positivity
  have hd : (Real.exp x) ^ 2 + 1 ≠ 0 := ne_of_gt hdpos
  have hfrac : ((Real.exp x) ^ 2 - 1) / ((Real.exp x) ^ 2 + 1) < 1 := by
    apply (div_lt_one hdpos).2
    linarith
  have hout : 1 - ((Real.exp x) ^ 2 - 1) / ((Real.exp x) ^ 2 + 1) ≠ 0 := by
    exact ne_of_gt (sub_pos.mpr hfrac)
  rw [show (2 : ℝ) * x = x + x by ring, Real.exp_add]
  field_simp [hd, hout]
  <;> ring

/-- Source: `proof_gap/exercise_229/5.txt`. -/
theorem gap5 : ∀ x, 0 < (1 + y x) / (1 - y x) := by
  intro x
  rw [← gap4 x]
  exact Real.exp_pos _

/-- Source: `proof_gap/exercise_229/6.txt`. -/
theorem gap6 : ∀ x, -1 < y x := by
  intro x
  rw [y]
  have hx : 0 < Real.exp x := Real.exp_pos x
  have hnx : 0 < Real.exp (-x) := Real.exp_pos (-x)
  have hsum : 0 < Real.exp x + Real.exp (-x) := add_pos hx hnx
  apply (lt_div_iff₀ hsum).2
  linarith

/-- Source: `proof_gap/exercise_229/7.txt`. -/
theorem gap7 : ∀ x, y x < 1 := by
  intro x
  rw [y]
  have hx : 0 < Real.exp x := Real.exp_pos x
  have hnx : 0 < Real.exp (-x) := Real.exp_pos (-x)
  have hsum : 0 < Real.exp x + Real.exp (-x) := add_pos hx hnx
  apply (div_lt_iff₀ hsum).2
  linarith

/-- Source: `proof_gap/exercise_229/8.txt`. -/
theorem gap8 : (-1 : ℝ) < 1 := by
  norm_num

/-- Source: `proof_gap/exercise_229/9.txt`. -/
theorem gap9 : ∀ x, x = arctanh (y x) := by
  intro x
  rw [arctanh, ← gap4 x, Real.log_exp]
  ring

/-- Source: `proof_gap/exercise_229/10.txt`. -/
theorem gap10 : ∀ x,
    arctanh (y x) = (1 / 2) * Real.log ((1 + y x) / (1 - y x)) := by
  intro x
  rfl

/-- Source: `proof_gap/exercise_229/11.txt`. -/
theorem gap11 : ∀ x,
    x = (1 / 2) * Real.log ((1 + y x) / (1 - y x)) := by
  intro x
  calc
    x = arctanh (y x) := gap9 x
    _ = (1 / 2) * Real.log ((1 + y x) / (1 - y x)) := gap10 x

end

end ProofGap.Exercise229
