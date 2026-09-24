import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

namespace ProofGap.Exercise953

noncomputable section

def denominator (α x : ℝ) : ℝ :=
  1 - Real.cos α * Real.cos x

def argument (α x : ℝ) : ℝ :=
  Real.sin α * Real.sin x / denominator α x

def y (α x : ℝ) : ℝ := Real.arcsin (argument α x)

def expandedDerivative (α x : ℝ) : ℝ :=
  1 / Real.sqrt (1 - argument α x ^ 2) *
    ((Real.sin α * Real.cos x * denominator α x -
        Real.sin α * Real.cos α * Real.sin x ^ 2) /
      denominator α x ^ 2)

def absoluteValueForm (α x : ℝ) : ℝ :=
  denominator α x / Real.sqrt ((Real.cos x - Real.cos α) ^ 2) *
    (Real.sin α * (Real.cos x - Real.cos α) /
      denominator α x ^ 2)

def finalDerivative (α x : ℝ) : ℝ :=
  Real.sin α * Real.sign (Real.cos x - Real.cos α) /
    denominator α x

private theorem denominator_strictly_positive (α x : ℝ)
    (hden : denominator α x ≠ 0) : 0 < denominator α x := by
  have h₁ :
      0 ≤ (1 - Real.cos α) * (1 + Real.cos x) :=
    mul_nonneg (sub_nonneg.mpr (Real.cos_le_one α))
      (by nlinarith [Real.neg_one_le_cos x])
  have h₂ :
      0 ≤ (1 + Real.cos α) * (1 - Real.cos x) :=
    mul_nonneg (by nlinarith [Real.neg_one_le_cos α])
      (sub_nonneg.mpr (Real.cos_le_one x))
  have hprod : Real.cos α * Real.cos x ≤ 1 := by
    nlinarith [h₁, h₂]
  have hnonneg : 0 ≤ denominator α x := by
    unfold denominator
    exact sub_nonneg.mpr hprod
  exact lt_of_le_of_ne hnonneg (Ne.symm hden)

private theorem one_sub_argument_sq_identity (α x : ℝ)
    (hden : denominator α x ≠ 0) :
    1 - argument α x ^ 2 =
      (Real.cos x - Real.cos α) ^ 2 / denominator α x ^ 2 := by
  have hsα : Real.sin α ^ 2 = 1 - Real.cos α ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq α]
  have hsx : Real.sin x ^ 2 = 1 - Real.cos x ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq x]
  have hpoly :
      denominator α x ^ 2 - (Real.sin α * Real.sin x) ^ 2 =
        (Real.cos x - Real.cos α) ^ 2 := by
    rw [mul_pow, hsα, hsx]
    unfold denominator
    ring
  calc
    1 - argument α x ^ 2 =
        (denominator α x ^ 2 - (Real.sin α * Real.sin x) ^ 2) /
          denominator α x ^ 2 := by
      rw [argument, div_pow]
      field_simp [hden]
    _ = (Real.cos x - Real.cos α) ^ 2 /
          denominator α x ^ 2 := by rw [hpoly]

private theorem argument_in_open_unit_interval (α x : ℝ)
    (hden : denominator α x ≠ 0)
    (hdiff : Real.cos x - Real.cos α ≠ 0) :
    argument α x ∈ Set.Ioo (-1 : ℝ) 1 := by
  have hpositive : 0 < 1 - argument α x ^ 2 := by
    rw [one_sub_argument_sq_identity α x hden]
    exact div_pos (sq_pos_of_ne_zero hdiff) (sq_pos_of_ne_zero hden)
  constructor <;> nlinarith [sq_nonneg (argument α x)]

private theorem sqrt_one_sub_argument_sq (α x : ℝ)
    (hden : denominator α x ≠ 0) :
    Real.sqrt (1 - argument α x ^ 2) =
      Real.sqrt ((Real.cos x - Real.cos α) ^ 2) / denominator α x := by
  have hdpos := denominator_strictly_positive α x hden
  rw [one_sub_argument_sq_identity α x hden]
  calc
    Real.sqrt ((Real.cos x - Real.cos α) ^ 2 /
        denominator α x ^ 2) =
        Real.sqrt (((Real.cos x - Real.cos α) / denominator α x) ^ 2) := by
      rw [div_pow]
    _ = |(Real.cos x - Real.cos α) / denominator α x| :=
      Real.sqrt_sq_eq_abs _
    _ = |Real.cos x - Real.cos α| / |denominator α x| := by
      rw [abs_div]
    _ = Real.sqrt ((Real.cos x - Real.cos α) ^ 2) /
        denominator α x := by
      rw [Real.sqrt_sq_eq_abs, abs_of_pos hdpos]

private theorem derivative_numerator_identity (α x : ℝ) :
    Real.sin α * Real.cos x * denominator α x -
        Real.sin α * Real.cos α * Real.sin x ^ 2 =
      Real.sin α * (Real.cos x - Real.cos α) := by
  have hsx : Real.sin x ^ 2 = 1 - Real.cos x ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq x]
  rw [hsx]
  unfold denominator
  ring

theorem gap1 (α x : ℝ) (hden : denominator α x ≠ 0)
    (hdiff : Real.cos x - Real.cos α ≠ 0) :
    HasDerivAt (y α) (expandedDerivative α x) x := by
  have hnum :
      HasDerivAt (fun z : ℝ => Real.sin α * Real.sin z)
        (Real.sin α * Real.cos x) x := by
    simpa using (Real.hasDerivAt_sin x).const_mul (Real.sin α)
  have hden' :
      HasDerivAt (denominator α) (Real.cos α * Real.sin x) x := by
    simpa [denominator] using
      ((Real.hasDerivAt_cos x).const_mul (Real.cos α)).const_sub 1
  have harg :
      HasDerivAt (argument α)
        ((Real.sin α * Real.cos x * denominator α x -
            Real.sin α * Real.cos α * Real.sin x ^ 2) /
          denominator α x ^ 2) x := by
    unfold argument
    convert hnum.div hden' hden using 1
    ring
  have hi := argument_in_open_unit_interval α x hden hdiff
  have harcsin :
      HasDerivAt Real.arcsin
        (1 / Real.sqrt (1 - argument α x ^ 2)) (argument α x) := by
    apply Real.hasDerivAt_arcsin <;> nlinarith [hi.1, hi.2]
  have hy' := harcsin.comp x harg
  simpa [y, expandedDerivative, div_eq_mul_inv, mul_comm] using hy'

theorem gap2 (α x : ℝ) (hden : denominator α x ≠ 0)
    (hdiff : Real.cos x - Real.cos α ≠ 0) :
    expandedDerivative α x = absoluteValueForm α x := by
  have hsqrt_ne :
      Real.sqrt ((Real.cos x - Real.cos α) ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (sq_pos_of_ne_zero hdiff))
  unfold expandedDerivative absoluteValueForm
  rw [sqrt_one_sub_argument_sq α x hden,
    derivative_numerator_identity α x]
  field_simp [hden, hsqrt_ne]

theorem gap3 (α x : ℝ) (hden : denominator α x ≠ 0)
    (hdiff : Real.cos x - Real.cos α ≠ 0) :
    absoluteValueForm α x = finalDerivative α x := by
  unfold absoluteValueForm finalDerivative
  rw [Real.sqrt_sq_eq_abs]
  rcases lt_or_gt_of_ne hdiff with hneg | hpos
  · rw [abs_of_neg hneg, Real.sign_of_neg hneg]
    field_simp [hden, hdiff]
  · rw [abs_of_pos hpos, Real.sign_of_pos hpos]
    field_simp [hden, hdiff]

theorem gap4 (α x : ℝ) (hden : denominator α x ≠ 0)
    (hdiff : Real.cos x - Real.cos α ≠ 0) :
    HasDerivAt (y α) (finalDerivative α x) x := by
  have h := gap1 α x hden hdiff
  rw [gap2 α x hden hdiff, gap3 α x hden hdiff] at h
  exact h

end

end ProofGap.Exercise953
