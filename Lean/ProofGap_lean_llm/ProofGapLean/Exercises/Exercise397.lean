import ProofGapLean.Prelude.Core
import Mathlib.Data.Real.Archimedean
import ProofGapLean.Prelude.Elementary
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise397

noncomputable section

def f (x : ℝ) : ℝ := x ^ 2
def imageOn (g : ℝ → ℝ) (s : Set ℝ) : Set ℝ :=
  {y | ∃ x ∈ s, y = g x}
def OscillationOn (g : ℝ → ℝ) (s : Set ℝ) : ℝ :=
  sSup (imageOn g s) - sInf (imageOn g s)

/-- Source: `proof_gap/exercise_397/1.txt`. -/
private theorem oscillationOn_sq_Ioo
    (a b : ℝ) (ha : 0 ≤ a) (hab : a < b) :
    OscillationOn f (Set.Ioo a b) = b ^ 2 - a ^ 2 := by
  have himage : imageOn f (Set.Ioo a b) = Set.Ioo (a ^ 2) (b ^ 2) := by
    ext y
    simp only [imageOn, f, Set.mem_setOf_eq, Set.mem_Ioo]
    constructor
    · rintro ⟨x, ⟨hax, hxb⟩, rfl⟩
      have hx0 : 0 ≤ x := by nlinarith
      constructor
      · have hsum : 0 < x + a := by nlinarith
        have hprod : 0 < (x - a) * (x + a) :=
          mul_pos (sub_pos.mpr hax) hsum
        nlinarith
      · have hsum : 0 < b + x := by nlinarith
        have hprod : 0 < (b - x) * (b + x) :=
          mul_pos (sub_pos.mpr hxb) hsum
        nlinarith
    · rintro ⟨hay, hyb⟩
      have hy0 : 0 ≤ y := by nlinarith [sq_nonneg a]
      have hsqrt0 : 0 ≤ Real.sqrt y := Real.sqrt_nonneg y
      have hsq : (Real.sqrt y) ^ 2 = y := Real.sq_sqrt hy0
      have hb0 : 0 ≤ b := by nlinarith
      refine ⟨Real.sqrt y, ⟨?_, ?_⟩, hsq.symm⟩
      · by_contra hnot
        have hsle : Real.sqrt y ≤ a := le_of_not_gt hnot
        have hprod : 0 ≤ (a - Real.sqrt y) * (a + Real.sqrt y) :=
          mul_nonneg (sub_nonneg.mpr hsle) (add_nonneg ha hsqrt0)
        nlinarith
      · by_contra hnot
        have hble : b ≤ Real.sqrt y := le_of_not_gt hnot
        have hprod : 0 ≤ (Real.sqrt y - b) * (Real.sqrt y + b) :=
          mul_nonneg (sub_nonneg.mpr hble) (add_nonneg hsqrt0 hb0)
        nlinarith
  have hsquares : a ^ 2 < b ^ 2 := by
    have hsum : 0 < b + a := by nlinarith
    have hprod : 0 < (b - a) * (b + a) :=
      mul_pos (sub_pos.mpr hab) hsum
    nlinarith
  unfold OscillationOn
  rw [himage, csSup_Ioo hsquares, csInf_Ioo hsquares]

theorem gap1 :
    ∃ M₀ m₀ : ℝ, OscillationOn f (Set.Ioo 1 3) = M₀ - m₀ := by
  refine ⟨sSup (imageOn f (Set.Ioo 1 3)),
    sInf (imageOn f (Set.Ioo 1 3)), ?_⟩
  rfl

/-- Source: `proof_gap/exercise_397/2.txt`. -/
theorem gap2 : ∃ m₀ : ℝ, m₀ = 1 := by
  exact ⟨1, rfl⟩

/-- Source: `proof_gap/exercise_397/3.txt`. -/
theorem gap3 : ∃ M₀ : ℝ, M₀ = 9 := by
  exact ⟨9, rfl⟩

/-- Source: `proof_gap/exercise_397/4.txt`. -/
theorem gap4 : OscillationOn f (Set.Ioo 1 3) = 8 := by
  calc
    OscillationOn f (Set.Ioo 1 3) = (3 : ℝ) ^ 2 - (1 : ℝ) ^ 2 :=
      oscillationOn_sq_Ioo 1 3 (by norm_num) (by norm_num)
    _ = 8 := by norm_num

/-- Source: `proof_gap/exercise_397/5.txt`. -/
theorem gap5 : ∃ m₀ : ℝ, m₀ = (1.9 : ℝ) ^ 2 := by
  exact ⟨(1.9 : ℝ) ^ 2, rfl⟩

/-- Source: `proof_gap/exercise_397/6.txt`. -/
theorem gap6 : ∃ M₀ : ℝ, M₀ = (2.1 : ℝ) ^ 2 := by
  exact ⟨(2.1 : ℝ) ^ 2, rfl⟩

/-- Source: `proof_gap/exercise_397/7.txt`. -/
theorem gap7 : OscillationOn f (Set.Ioo 1.9 2.1) =
    (2.1 : ℝ) ^ 2 - (1.9 : ℝ) ^ 2 := by
  exact oscillationOn_sq_Ioo (1.9 : ℝ) 2.1 (by norm_num) (by norm_num)

/-- Source: `proof_gap/exercise_397/8.txt`. -/
theorem gap8 : (2.1 : ℝ) ^ 2 - (1.9 : ℝ) ^ 2 = 0.8 := by
  norm_num

/-- Source: `proof_gap/exercise_397/9.txt`. -/
theorem gap9 : OscillationOn f (Set.Ioo 1.9 2.1) = 0.8 := by
  calc
    OscillationOn f (Set.Ioo 1.9 2.1) = (2.1 : ℝ) ^ 2 - (1.9 : ℝ) ^ 2 := gap7
    _ = 0.8 := gap8

/-- Source: `proof_gap/exercise_397/10.txt`. -/
theorem gap10 : OscillationOn f (Set.Ioo 1.99 2.01) =
    (2.01 : ℝ) ^ 2 - (1.99 : ℝ) ^ 2 := by
  exact oscillationOn_sq_Ioo (1.99 : ℝ) 2.01 (by norm_num) (by norm_num)

/-- Source: `proof_gap/exercise_397/11.txt`. -/
theorem gap11 : (2.01 : ℝ) ^ 2 - (1.99 : ℝ) ^ 2 = 0.08 := by
  norm_num

/-- Source: `proof_gap/exercise_397/12.txt`. -/
theorem gap12 : OscillationOn f (Set.Ioo 1.99 2.01) = 0.08 := by
  calc
    OscillationOn f (Set.Ioo 1.99 2.01) = (2.01 : ℝ) ^ 2 - (1.99 : ℝ) ^ 2 := gap10
    _ = 0.08 := gap11

/-- Source: `proof_gap/exercise_397/13.txt`. -/
theorem gap13 : OscillationOn f (Set.Ioo 1.999 2.001) =
    (2.001 : ℝ) ^ 2 - (1.999 : ℝ) ^ 2 := by
  exact oscillationOn_sq_Ioo (1.999 : ℝ) 2.001 (by norm_num) (by norm_num)

/-- Source: `proof_gap/exercise_397/14.txt`. -/
theorem gap14 : (2.001 : ℝ) ^ 2 - (1.999 : ℝ) ^ 2 = 0.008 := by
  norm_num

/-- Source: `proof_gap/exercise_397/15.txt`. -/
theorem gap15 : OscillationOn f (Set.Ioo 1.999 2.001) = 0.008 := by
  calc
    OscillationOn f (Set.Ioo 1.999 2.001) = (2.001 : ℝ) ^ 2 - (1.999 : ℝ) ^ 2 := gap13
    _ = 0.008 := gap14

end

end ProofGap.Exercise397
