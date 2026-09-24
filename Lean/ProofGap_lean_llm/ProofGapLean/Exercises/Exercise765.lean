import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.Linarith

namespace ProofGap.Exercise765

noncomputable section

def f (x : ℝ) : ℝ := (1 + x ^ 2) * Real.sign x
def inv (y : ℝ) : ℝ :=
  if 1 ≤ y then Real.sqrt (y * Real.sign y - 1)
  else if y ≤ -1 then -Real.sqrt (y * Real.sign y - 1)
  else 0
def invDomain : Set ℝ := {y | 1 < |y| ∨ y = 0}

/-- Source: `proof_gap/exercise_765/1.txt`; restore the missing relation `y=f x`. -/
private theorem continuous_inv : Continuous inv := by
  have hinv :
      inv = fun y : ℝ => Real.sqrt (y - 1) - Real.sqrt (-y - 1) := by
    funext y
    by_cases hy : 1 ≤ y
    · have hypos : 0 < y := by linarith
      have hright : -y - 1 ≤ 0 := by linarith
      simp [inv, hy, Real.sign_of_pos hypos,
        Real.sqrt_eq_zero_of_nonpos hright]
    · by_cases hny : y ≤ -1
      · have hyneg : y < 0 := by linarith
        have hleft : y - 1 ≤ 0 := by linarith
        simp [inv, hy, hny, Real.sign_of_neg hyneg,
          Real.sqrt_eq_zero_of_nonpos hleft]
      · have hleft : y - 1 ≤ 0 := by linarith
        have hright : -y - 1 ≤ 0 := by linarith
        simp [inv, hy, hny, Real.sqrt_eq_zero_of_nonpos hleft,
          Real.sqrt_eq_zero_of_nonpos hright]
  rw [hinv]
  have hleft : Continuous (fun y : ℝ => Real.sqrt (y - 1)) :=
    Real.continuous_sqrt.comp (continuous_id.sub continuous_const)
  have hright : Continuous (fun y : ℝ => Real.sqrt (-y - 1)) :=
    Real.continuous_sqrt.comp (continuous_id.neg.sub continuous_const)
  exact hleft.sub hright

theorem gap1 (x y : ℝ) (hy : y = f x) :
    Real.sign y = Real.sign x := by
  rw [hy]
  have hpos : 0 < 1 + x ^ 2 :=
    add_pos_of_pos_of_nonneg zero_lt_one (sq_nonneg x)
  by_cases hx : x = 0
  · subst x
    simp [f]
  · by_cases hxpos : 0 < x
    · have hfx : 0 < f x := by
        simpa [f, Real.sign_of_pos hxpos] using hpos
      rw [Real.sign_of_pos hfx, Real.sign_of_pos hxpos]
    · have hxneg : x < 0 :=
        lt_of_le_of_ne (le_of_not_gt hxpos) hx
      have hfx : f x < 0 := by
        rw [f, Real.sign_of_neg hxneg]
        nlinarith [sq_nonneg x]
      rw [Real.sign_of_neg hfx, Real.sign_of_neg hxneg]

/-- Source: `proof_gap/exercise_765/2.txt`. -/
theorem gap2 (x : ℝ) :
    (Real.sign x) ^ 2 = if x = 0 then 0 else 1 := by
  by_cases hx : x = 0
  · subst x
    simp
  · rw [if_neg hx]
    by_cases hxpos : 0 < x
    · simp [Real.sign_of_pos hxpos]
    · have hxneg : x < 0 :=
        lt_of_le_of_ne (le_of_not_gt hxpos) hx
      simp [Real.sign_of_neg hxneg]

/-- Source: `proof_gap/exercise_765/3.txt`; restore `y=f x`. -/
theorem gap3 (x y : ℝ) (hy : y = f x) :
    y * Real.sign y = (1 + x ^ 2) * (Real.sign x) ^ 2 := by
  rw [gap1 x y hy, hy]
  simp [f, pow_two, mul_assoc]

/-- Source: `proof_gap/exercise_765/4.txt`. -/
theorem gap4 : Set.range f = invDomain := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    by_cases hx : x = 0
    · right
      simp [f, hx]
    · left
      by_cases hxpos : 0 < x
      · have hsq : 0 < x ^ 2 := sq_pos_of_pos hxpos
        have hfpos : 0 < f x := by
          simp [f, Real.sign_of_pos hxpos]
          nlinarith
        rw [abs_of_pos hfpos]
        simp [f, Real.sign_of_pos hxpos]
        linarith
      · have hxneg : x < 0 := lt_of_le_of_ne (le_of_not_gt hxpos) hx
        have hsq : 0 < x ^ 2 := sq_pos_of_neg hxneg
        have hfneg : f x < 0 := by
          rw [f, Real.sign_of_neg hxneg]
          nlinarith
        rw [abs_of_neg hfneg]
        simp [f, Real.sign_of_neg hxneg]
        linarith
  · intro hy
    rcases hy with hy | rfl
    · rcases le_total y 0 with hynonpos | hypos
      · have hylt : y < -1 := by
          rw [abs_of_nonpos hynonpos] at hy
          linarith
        let x := -Real.sqrt (-y - 1)
        have hrad : 0 < -y - 1 := by linarith
        have hxneg : x < 0 := by
          dsimp [x]
          exact neg_neg_of_pos (Real.sqrt_pos.2 hrad)
        refine ⟨x, ?_⟩
        rw [f, Real.sign_of_neg hxneg]
        dsimp [x]
        rw [neg_sq, Real.sq_sqrt hrad.le]
        ring
      · have hylt : 1 < y := by
          simpa [abs_of_nonneg hypos] using hy
        let x := Real.sqrt (y - 1)
        have hrad : 0 < y - 1 := by linarith
        have hxpos : 0 < x := Real.sqrt_pos.2 hrad
        refine ⟨x, ?_⟩
        rw [f, Real.sign_of_pos hxpos]
        dsimp [x]
        rw [Real.sq_sqrt hrad.le]
        ring
    · exact ⟨0, by simp [f]⟩

/-- Source: `proof_gap/exercise_765/5.txt`; bind `x` to the inverse value. -/
theorem gap5 (y : ℝ) (hy : y ∈ invDomain) :
    inv y =
      if 1 ≤ y then Real.sqrt (y * Real.sign y - 1)
      else if y ≤ -1 then -Real.sqrt (y * Real.sign y - 1)
      else 0 := by
  rfl

/-- Source: `proof_gap/exercise_765/6.txt`. -/
theorem gap6 : ContinuousOn inv invDomain := by
  exact continuous_inv.continuousOn

/-- Source: `proof_gap/exercise_765/7.txt`; use the total zero extension encoded above. -/
theorem gap7 : Continuous inv := by
  exact continuous_inv

end

end ProofGap.Exercise765
