import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul

namespace ProofGap.Exercise4028

noncomputable section

open scoped Interval

def parameterVolume (a : ℝ) : ℝ :=
  2 *
    ∫ u in (1 : ℝ)..2,
      ∫ v in (1 / 2 : ℝ)..2,
        a ^ 2 * (u / v + u * v) * (a ^ 2 / (2 * v))

theorem gap1 (a : ℝ) :
    parameterVolume a =
      2 *
        ∫ u in (1 : ℝ)..2,
          ∫ v in (1 / 2 : ℝ)..2,
            a ^ 2 * (u / v + u * v) * (a ^ 2 / (2 * v)) := by
  rfl

theorem gap2 (a : ℝ) :
    parameterVolume a =
      a ^ 4 *
        (∫ u in (1 : ℝ)..2, u) *
          ∫ v in (1 / 2 : ℝ)..2, 1 + 1 / v ^ 2 := by
  unfold parameterVolume
  have hinner (u : ℝ) :
      (∫ v in (1 / 2 : ℝ)..2,
          a ^ 2 * (u / v + u * v) * (a ^ 2 / (2 * v))) =
        (a ^ 4 * u / 2) *
          ∫ v in (1 / 2 : ℝ)..2, 1 + 1 / v ^ 2 := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro v hv
    have hvpos : 0 < v := by
      have hvlow := hv.1
      norm_num [Set.uIcc] at hvlow
      linarith
    have hvne : v ≠ 0 := ne_of_gt hvpos
    field_simp [hvne] <;> ring
  calc
    2 *
          ∫ u in (1 : ℝ)..2,
            ∫ v in (1 / 2 : ℝ)..2,
              a ^ 2 * (u / v + u * v) * (a ^ 2 / (2 * v)) =
        2 *
          ∫ u in (1 : ℝ)..2,
            (a ^ 4 * u / 2) *
              (∫ v in (1 / 2 : ℝ)..2, 1 + 1 / v ^ 2) := by
      apply congrArg (fun z : ℝ => 2 * z)
      apply intervalIntegral.integral_congr
      intro u hu
      exact hinner u
    _ =
        2 *
          ∫ u in (1 : ℝ)..2,
            ((a ^ 4 / 2) *
                (∫ v in (1 / 2 : ℝ)..2, 1 + 1 / v ^ 2)) * u := by
      apply congrArg (fun z : ℝ => 2 * z)
      apply intervalIntegral.integral_congr
      intro u hu
      ring
    _ =
        2 *
          (((a ^ 4 / 2) *
              (∫ v in (1 / 2 : ℝ)..2, 1 + 1 / v ^ 2)) *
            ∫ u in (1 : ℝ)..2, u) := by
      rw [intervalIntegral.integral_const_mul]
    _ =
        a ^ 4 *
          (∫ u in (1 : ℝ)..2, u) *
            ∫ v in (1 / 2 : ℝ)..2, 1 + 1 / v ^ 2 := by
      ring

theorem gap3 (a : ℝ) :
    a ^ 4 *
        (∫ u in (1 : ℝ)..2, u) *
          (∫ v in (1 / 2 : ℝ)..2, 1 + 1 / v ^ 2) =
      9 / 2 * a ^ 4 := by
  have hu_deriv :
      ∀ x ∈ Set.uIcc (1 : ℝ) 2,
        HasDerivAt (fun y : ℝ => y ^ 2 * (1 / 2 : ℝ)) x x := by
    intro x hx
    convert
      ((hasDerivAt_id x).mul (hasDerivAt_id x)).const_mul (1 / 2 : ℝ)
      using 1 <;>
      simp [pow_two] <;>
      ring
  have hu : (∫ u in (1 : ℝ)..2, u) = 3 / 2 := by
    calc
      (∫ u in (1 : ℝ)..2, u) =
          2 ^ 2 * (1 / 2 : ℝ) - 1 ^ 2 * (1 / 2 : ℝ) := by
        exact intervalIntegral.integral_eq_sub_of_hasDerivAt
          hu_deriv continuousOn_id.intervalIntegrable
      _ = 3 / 2 := by norm_num
  have hne :
      ∀ x ∈ Set.uIcc (1 / 2 : ℝ) 2, x ≠ 0 := by
    intro x hx
    have hxlow := hx.1
    norm_num [Set.uIcc] at hxlow
    linarith
  have hcont_integrand :
      ContinuousOn (fun x : ℝ => 1 + 1 / x ^ 2)
        (Set.uIcc (1 / 2 : ℝ) 2) := by
    exact continuousOn_const.add
      (continuousOn_const.div (continuousOn_id.pow 2)
        (fun x hx => pow_ne_zero 2 (hne x hx)))
  have hderiv :
      ∀ x ∈ Set.uIcc (1 / 2 : ℝ) 2,
        HasDerivAt (fun y : ℝ => y - 1 / y) (1 + 1 / x ^ 2) x := by
    intro x hx
    have hxpos : 0 < x := by
      have hxlow := hx.1
      norm_num [Set.uIcc] at hxlow
      linarith
    have hxne : x ≠ 0 := ne_of_gt hxpos
    convert
      (hasDerivAt_id x).sub
        ((hasDerivAt_const (x := x) (c := (1 : ℝ))).div
          (hasDerivAt_id x) hxne) using 1 <;>
      simp only [id_eq] <;>
      field_simp [hxne] <;> ring
  have hv :
      (∫ v in (1 / 2 : ℝ)..2, 1 + 1 / v ^ 2) = 3 := by
    calc
      (∫ v in (1 / 2 : ℝ)..2, 1 + 1 / v ^ 2) =
          (2 - 1 / 2) - ((1 / 2 : ℝ) - 1 / (1 / 2 : ℝ)) := by
        exact intervalIntegral.integral_eq_sub_of_hasDerivAt
          hderiv hcont_integrand.intervalIntegrable
      _ = 3 := by norm_num
  rw [hu, hv]
  ring

theorem gap4 (a : ℝ) :
    parameterVolume a = 9 / 2 * a ^ 4 := by
  calc
    parameterVolume a =
        a ^ 4 *
          (∫ u in (1 : ℝ)..2, u) *
            ∫ v in (1 / 2 : ℝ)..2, 1 + 1 / v ^ 2 := gap2 a
    _ = 9 / 2 * a ^ 4 := gap3 a

end

end ProofGap.Exercise4028
