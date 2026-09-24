import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise1456_1

noncomputable section

def f (x : ℝ) : ℝ := 3 * x - x ^ 3
def domain : Set ℝ := Set.Icc (-2) 2

theorem gap1 : IsMinOn f domain (-1) := by
  intro x hx
  change -2 ≤ x ∧ x ≤ 2 at hx
  have hprod : 0 ≤ (2 - x) * (x + 1) ^ 2 :=
    mul_nonneg (sub_nonneg.mpr hx.2) (sq_nonneg (x + 1))
  have hvalue : f (-1) = -2 := by
    norm_num [f]
  rw [hvalue]
  change -2 ≤ 3 * x - x ^ 3
  nlinarith [hprod]

theorem gap2 : IsMaxOn f domain 1 := by
  intro x hx
  change -2 ≤ x ∧ x ≤ 2 at hx
  have hxnonneg : 0 ≤ x + 2 := by
    linarith
  have hprod : 0 ≤ (x + 2) * (x - 1) ^ 2 :=
    mul_nonneg hxnonneg (sq_nonneg (x - 1))
  have hvalue : f 1 = 2 := by
    norm_num [f]
  rw [hvalue]
  change 3 * x - x ^ 3 ≤ 2
  nlinarith [hprod]

theorem gap3 : f (-1) = -2 := by
  norm_num [f]

theorem gap4 : f 1 = 2 := by
  norm_num [f]

theorem gap5 : f (-2) = 2 := by
  norm_num [f]

theorem gap6 : f 2 = -2 := by
  norm_num [f]

theorem gap7 (x : ℝ) (hx : |x| ≤ 2) : |3 * x - x ^ 3| ≤ 2 := by
  have hdom : x ∈ domain := by
    change -2 ≤ x ∧ x ≤ 2
    exact abs_le.mp hx
  have hmin : f (-1) ≤ f x := gap1 hdom
  have hmax : f x ≤ f 1 := gap2 hdom
  rw [gap3] at hmin
  rw [gap4] at hmax
  apply abs_le.mpr
  constructor
  · simpa [f] using hmin
  · simpa [f] using hmax

theorem gap8 (x : ℝ) (hx : |x| ≤ 2) : |3 * x - x ^ 3| ≤ 2 := by
  exact gap7 x hx

end
end ProofGap.Exercise1456_1
