import ProofGapLean.Prelude.Elementary
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3121

noncomputable section

def nodeX : ℕ → ℝ
  | 0 => -2
  | 1 => 0
  | 2 => 4
  | 3 => 5
  | _ => 0

def nodeY : ℕ → ℝ
  | 0 => 5
  | 1 => 1
  | 2 => -3
  | 3 => 1
  | _ => 0

def lagrangeCubic (z : ℝ) : ℝ :=
  ((z - nodeX 1) * (z - nodeX 2) * (z - nodeX 3)) /
      ((nodeX 0 - nodeX 1) * (nodeX 0 - nodeX 2) *
        (nodeX 0 - nodeX 3)) * nodeY 0 +
    ((z - nodeX 0) * (z - nodeX 2) * (z - nodeX 3)) /
      ((nodeX 1 - nodeX 0) * (nodeX 1 - nodeX 2) *
        (nodeX 1 - nodeX 3)) * nodeY 1 +
    ((z - nodeX 0) * (z - nodeX 1) * (z - nodeX 3)) /
      ((nodeX 2 - nodeX 0) * (nodeX 2 - nodeX 1) *
        (nodeX 2 - nodeX 3)) * nodeY 2 +
    ((z - nodeX 0) * (z - nodeX 1) * (z - nodeX 2)) /
      ((nodeX 3 - nodeX 0) * (nodeX 3 - nodeX 1) *
        (nodeX 3 - nodeX 2)) * nodeY 3

def P (z : ℝ) : ℝ :=
  lagrangeCubic z

def cubicModel (z : ℝ) : ℝ :=
  1 - (55 / 21 : ℝ) * z - (1 / 14 : ℝ) * z ^ 2 +
    (5 / 42 : ℝ) * z ^ 3

def Within (actual rounded tolerance : ℝ) : Prop :=
  |actual - rounded| ≤ tolerance

/-- Source: `proof_gap/exercise_3121/1.txt`. -/
theorem gap1 : nodeX 0 = -2 := by
  rfl

/-- Source: `proof_gap/exercise_3121/2.txt`. -/
theorem gap2 : nodeX 1 = 0 := by
  rfl

/-- Source: `proof_gap/exercise_3121/3.txt`. -/
theorem gap3 : nodeX 2 = 4 := by
  rfl

/-- Source: `proof_gap/exercise_3121/4.txt`. -/
theorem gap4 : nodeX 3 = 5 := by
  rfl

/-- Source: `proof_gap/exercise_3121/5.txt`. -/
theorem gap5 : nodeY 0 = 5 := by
  rfl

/-- Source: `proof_gap/exercise_3121/6.txt`. -/
theorem gap6 : nodeY 1 = 1 := by
  rfl

/-- Source: `proof_gap/exercise_3121/7.txt`. -/
theorem gap7 : nodeY 2 = -3 := by
  rfl

/-- Source: `proof_gap/exercise_3121/8.txt`. -/
theorem gap8 : nodeY 3 = 1 := by
  rfl

/-- Source: `proof_gap/exercise_3121/9.txt`; define `P` as the Lagrange interpolant. -/
theorem gap9 :
    ∀ z : ℝ,
      P z =
        ((z - nodeX 1) * (z - nodeX 2) * (z - nodeX 3)) /
            ((nodeX 0 - nodeX 1) * (nodeX 0 - nodeX 2) *
              (nodeX 0 - nodeX 3)) * nodeY 0 +
          ((z - nodeX 0) * (z - nodeX 2) * (z - nodeX 3)) /
            ((nodeX 1 - nodeX 0) * (nodeX 1 - nodeX 2) *
              (nodeX 1 - nodeX 3)) * nodeY 1 +
          ((z - nodeX 0) * (z - nodeX 1) * (z - nodeX 3)) /
            ((nodeX 2 - nodeX 0) * (nodeX 2 - nodeX 1) *
              (nodeX 2 - nodeX 3)) * nodeY 2 +
          ((z - nodeX 0) * (z - nodeX 1) * (z - nodeX 2)) /
            ((nodeX 3 - nodeX 0) * (nodeX 3 - nodeX 1) *
              (nodeX 3 - nodeX 2)) * nodeY 3 := by
  intro z
  rfl

/-- Source: `proof_gap/exercise_3121/10.txt`; expand the fixed interpolant. -/
theorem gap10 :
    ∀ z : ℝ, P z = cubicModel z := by
  intro z
  norm_num [P, lagrangeCubic, cubicModel, nodeX, nodeY] <;> ring

/-- Source: `proof_gap/exercise_3121/11.txt`. -/
theorem gap11 :
    P (-1) = 1 + (55 / 21 : ℝ) - (1 / 14 : ℝ) - (5 / 42 : ℝ) := by
  rw [gap10]
  norm_num [cubicModel]

/-- Source: `proof_gap/exercise_3121/12.txt`; two-decimal rounding has tolerance `0.005`. -/
theorem gap12 :
    Within
      (1 + (55 / 21 : ℝ) - (1 / 14 : ℝ) - (5 / 42 : ℝ))
      3.43 0.005 := by
  norm_num [Within, abs_of_nonpos]

/-- Source: `proof_gap/exercise_3121/13.txt`; quantify the displayed rounding. -/
theorem gap13 : Within (P (-1)) 3.43 0.005 := by
  rw [gap11]
  exact gap12

/-- Source: `proof_gap/exercise_3121/14.txt`. -/
theorem gap14 :
    P 1 = 1 - (55 / 21 : ℝ) - (1 / 14 : ℝ) + (5 / 42 : ℝ) := by
  rw [gap10]
  norm_num [cubicModel]

/-- Source: `proof_gap/exercise_3121/15.txt`; two-decimal rounding has tolerance `0.005`. -/
theorem gap15 :
    Within
      (1 - (55 / 21 : ℝ) - (1 / 14 : ℝ) + (5 / 42 : ℝ))
      (-1.57) 0.005 := by
  norm_num [Within, abs_of_nonpos]

/-- Source: `proof_gap/exercise_3121/16.txt`; quantify the displayed rounding. -/
theorem gap16 : Within (P 1) (-1.57) 0.005 := by
  rw [gap14]
  exact gap15

/-- Source: `proof_gap/exercise_3121/17.txt`. -/
theorem gap17 :
    P 6 = 1 - (110 / 7 : ℝ) - (18 / 7 : ℝ) + (180 / 7 : ℝ) := by
  rw [gap10]
  norm_num [cubicModel]

/-- Source: `proof_gap/exercise_3121/18.txt`; two-decimal rounding has tolerance `0.005`. -/
theorem gap18 :
    Within
      (1 - (110 / 7 : ℝ) - (18 / 7 : ℝ) + (180 / 7 : ℝ))
      8.43 0.005 := by
  norm_num [Within, abs_of_nonpos]

/-- Source: `proof_gap/exercise_3121/19.txt`; quantify the displayed rounding. -/
theorem gap19 : Within (P 6) 8.43 0.005 := by
  rw [gap17]
  exact gap18

end

end ProofGap.Exercise3121
