import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

namespace ProofGap.Exercise958

noncomputable section

def y (x : ℝ) : ℝ :=
  Real.arcsin (Real.sin (x ^ 2)) + Real.arccos (Real.cos (x ^ 2))

def expandedDerivative (x : ℝ) : ℝ :=
  2 * x * Real.cos (x ^ 2) /
      Real.sqrt (1 - Real.sin (x ^ 2) ^ 2) +
    2 * x * Real.sin (x ^ 2) /
      Real.sqrt (1 - Real.cos (x ^ 2) ^ 2)

def finalDerivative (x : ℝ) : ℝ :=
  2 * x * (Real.sign (Real.cos (x ^ 2)) +
    Real.sign (Real.sin (x ^ 2)))

theorem gap1 (x : ℝ) (hcos : Real.cos (x ^ 2) ≠ 0)
    (hsin : Real.sin (x ^ 2) ≠ 0) :
    HasDerivAt y (expandedDerivative x) x := by
  have hcos_sq_pos : 0 < Real.cos (x ^ 2) ^ 2 :=
    sq_pos_of_ne_zero hcos
  have hsin_sq_pos : 0 < Real.sin (x ^ 2) ^ 2 :=
    sq_pos_of_ne_zero hsin
  have hsin_mem : Real.sin (x ^ 2) ∈ Set.Ioo (-1) 1 := by
    constructor <;>
      nlinarith [Real.sin_sq_add_cos_sq (x ^ 2),
        sq_nonneg (Real.sin (x ^ 2) - 1),
        sq_nonneg (Real.sin (x ^ 2) + 1)]
  have hcos_mem : Real.cos (x ^ 2) ∈ Set.Ioo (-1) 1 := by
    constructor <;>
      nlinarith [Real.sin_sq_add_cos_sq (x ^ 2),
        sq_nonneg (Real.cos (x ^ 2) - 1),
        sq_nonneg (Real.cos (x ^ 2) + 1)]
  have hsin_ne_neg_one : Real.sin (x ^ 2) ≠ -1 := ne_of_gt hsin_mem.1
  have hsin_ne_one : Real.sin (x ^ 2) ≠ 1 := ne_of_lt hsin_mem.2
  have hcos_ne_neg_one : Real.cos (x ^ 2) ≠ -1 := ne_of_gt hcos_mem.1
  have hcos_ne_one : Real.cos (x ^ 2) ≠ 1 := ne_of_lt hcos_mem.2
  have hid : HasDerivAt (fun z : ℝ => z) 1 x := hasDerivAt_id x
  have hsquare : HasDerivAt (fun z : ℝ => z ^ 2) (2 * x) x := by
    simpa [pow_two, two_mul] using hid.mul hid
  have harcsin_raw :=
    (Real.hasDerivAt_arcsin
      (x := Real.sin (x ^ 2)) hsin_ne_neg_one hsin_ne_one).comp x hsquare.sin
  have harcsin :
      HasDerivAt (fun z : ℝ => Real.arcsin (Real.sin (z ^ 2)))
        (2 * x * Real.cos (x ^ 2) /
          Real.sqrt (1 - Real.sin (x ^ 2) ^ 2)) x := by
    convert harcsin_raw using 1 <;> ring
  have harccos_raw :=
    (Real.hasDerivAt_arccos
      (x := Real.cos (x ^ 2)) hcos_ne_neg_one hcos_ne_one).comp x hsquare.cos
  have harccos :
      HasDerivAt (fun z : ℝ => Real.arccos (Real.cos (z ^ 2)))
        (2 * x * Real.sin (x ^ 2) /
          Real.sqrt (1 - Real.cos (x ^ 2) ^ 2)) x := by
    convert harccos_raw using 1 <;> ring
  simpa only [y, expandedDerivative] using harcsin.add harccos

theorem gap2 (x : ℝ) (hcos : Real.cos (x ^ 2) ≠ 0)
    (hsin : Real.sin (x ^ 2) ≠ 0) :
    expandedDerivative x = finalDerivative x := by
  have hcos_identity :
      1 - Real.sin (x ^ 2) ^ 2 = Real.cos (x ^ 2) ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq (x ^ 2)]
  have hsin_identity :
      1 - Real.cos (x ^ 2) ^ 2 = Real.sin (x ^ 2) ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq (x ^ 2)]
  unfold expandedDerivative finalDerivative
  rw [hcos_identity, hsin_identity,
    Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs]
  rcases lt_or_gt_of_ne hcos with hcneg | hcpos
  · rcases lt_or_gt_of_ne hsin with hsneg | hspos
    · rw [abs_of_neg hcneg, abs_of_neg hsneg,
        Real.sign_of_neg hcneg, Real.sign_of_neg hsneg]
      field_simp [hcos, hsin]
    · rw [abs_of_neg hcneg, abs_of_pos hspos,
        Real.sign_of_neg hcneg, Real.sign_of_pos hspos]
      field_simp [hcos, hsin]
  · rcases lt_or_gt_of_ne hsin with hsneg | hspos
    · rw [abs_of_pos hcpos, abs_of_neg hsneg,
        Real.sign_of_pos hcpos, Real.sign_of_neg hsneg]
      field_simp [hcos, hsin]
    · rw [abs_of_pos hcpos, abs_of_pos hspos,
        Real.sign_of_pos hcpos, Real.sign_of_pos hspos]
      field_simp [hcos, hsin]

theorem gap3 (x : ℝ) (hcos : Real.cos (x ^ 2) ≠ 0)
    (hsin : Real.sin (x ^ 2) ≠ 0) :
    HasDerivAt y (finalDerivative x) x := by
  rw [← gap2 x hcos hsin]
  exact gap1 x hcos hsin

end

end ProofGap.Exercise958
