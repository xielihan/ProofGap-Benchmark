import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3971

noncomputable section

open MeasureTheory
open scoped Interval

def square : Set (ℝ × ℝ) :=
  Set.Icc (0 : ℝ) Real.pi ×ˢ Set.Icc (0 : ℝ) Real.pi

def cosineAbsIntegral : ℝ :=
  ∫ p in square, |Real.cos (p.1 + p.2)|

def splitExpression : ℝ :=
  (∫ x in (0 : ℝ)..Real.pi / 2,
      (∫ y in (0 : ℝ)..Real.pi / 2 - x, Real.cos (x + y)) -
        ∫ y in Real.pi / 2 - x..Real.pi, Real.cos (x + y)) +
    ∫ x in Real.pi / 2..Real.pi,
      -(∫ y in (0 : ℝ)..3 * Real.pi / 2 - x, Real.cos (x + y)) +
        ∫ y in 3 * Real.pi / 2 - x..Real.pi, Real.cos (x + y)

private theorem integral_cos_add (x a b : ℝ) :
    (∫ y in a..b, Real.cos (x + y)) =
      Real.sin (x + b) - Real.sin (x + a) := by
  rw [intervalIntegral.integral_comp_add_left]
  simp

private theorem sin_three_pi_div_two :
    Real.sin (3 * Real.pi / 2) = -1 := by
  calc
    Real.sin (3 * Real.pi / 2) =
        Real.sin (Real.pi / 2 + Real.pi) := by
      congr 1
      ring
    _ = -Real.sin (Real.pi / 2) := Real.sin_add_pi _
    _ = -1 := by rw [Real.sin_pi_div_two]

private theorem first_split_eq_two (x : ℝ) :
    (∫ y in (0 : ℝ)..Real.pi / 2 - x, Real.cos (x + y)) -
        ∫ y in Real.pi / 2 - x..Real.pi, Real.cos (x + y) =
      2 := by
  rw [integral_cos_add, integral_cos_add]
  have hcut : x + (Real.pi / 2 - x) = Real.pi / 2 := by ring
  rw [hcut, Real.sin_pi_div_two, Real.sin_add_pi]
  ring_nf

private theorem second_split_eq_two (x : ℝ) :
    -(∫ y in (0 : ℝ)..3 * Real.pi / 2 - x, Real.cos (x + y)) +
        ∫ y in 3 * Real.pi / 2 - x..Real.pi, Real.cos (x + y) =
      2 := by
  rw [integral_cos_add, integral_cos_add]
  have hcut : x + (3 * Real.pi / 2 - x) = 3 * Real.pi / 2 := by ring
  rw [hcut, sin_three_pi_div_two, Real.sin_add_pi]
  ring_nf

private theorem abs_integral_eq_first_split (x : ℝ)
    (hx0 : 0 ≤ x) (hxhalf : x ≤ Real.pi / 2) :
    (∫ y in (0 : ℝ)..Real.pi, |Real.cos (x + y)|) =
      (∫ y in (0 : ℝ)..Real.pi / 2 - x, Real.cos (x + y)) -
        ∫ y in Real.pi / 2 - x..Real.pi, Real.cos (x + y) := by
  have hcut0 : 0 ≤ Real.pi / 2 - x := by linarith
  have hcutpi : Real.pi / 2 - x ≤ Real.pi := by
    linarith [Real.pi_pos]
  have hcont : Continuous (fun y : ℝ => |Real.cos (x + y)|) :=
    (Real.continuous_cos.comp (continuous_const.add continuous_id)).abs
  have hleft :
      (∫ y in (0 : ℝ)..Real.pi / 2 - x, |Real.cos (x + y)|) =
        ∫ y in (0 : ℝ)..Real.pi / 2 - x, Real.cos (x + y) := by
    apply intervalIntegral.integral_congr
    intro y hy
    rw [Set.uIcc_of_le hcut0] at hy
    rcases hy with ⟨hy0, hycut⟩
    have hcos : 0 ≤ Real.cos (x + y) :=
      Real.cos_nonneg_of_mem_Icc
        ⟨by linarith [Real.pi_pos], by linarith⟩
    change |Real.cos (x + y)| = Real.cos (x + y)
    exact abs_of_nonneg hcos
  have hright :
      (∫ y in Real.pi / 2 - x..Real.pi, |Real.cos (x + y)|) =
        -(∫ y in Real.pi / 2 - x..Real.pi, Real.cos (x + y)) := by
    calc
      (∫ y in Real.pi / 2 - x..Real.pi, |Real.cos (x + y)|) =
          ∫ y in Real.pi / 2 - x..Real.pi, -Real.cos (x + y) := by
        apply intervalIntegral.integral_congr
        intro y hy
        rw [Set.uIcc_of_le hcutpi] at hy
        rcases hy with ⟨hycut, hypi⟩
        have hcos : Real.cos (x + y) ≤ 0 :=
          Real.cos_nonpos_of_pi_div_two_le_of_le
            (by linarith) (by linarith)
        change |Real.cos (x + y)| = -Real.cos (x + y)
        exact abs_of_nonpos hcos
      _ = -(∫ y in Real.pi / 2 - x..Real.pi, Real.cos (x + y)) := by
        rw [intervalIntegral.integral_neg]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hcont.intervalIntegrable 0 (Real.pi / 2 - x))
    (hcont.intervalIntegrable (Real.pi / 2 - x) Real.pi)]
  rw [hleft, hright]
  ring

private theorem abs_integral_eq_second_split (x : ℝ)
    (hxhalf : Real.pi / 2 ≤ x) (hxpi : x ≤ Real.pi) :
    (∫ y in (0 : ℝ)..Real.pi, |Real.cos (x + y)|) =
      -(∫ y in (0 : ℝ)..3 * Real.pi / 2 - x, Real.cos (x + y)) +
        ∫ y in 3 * Real.pi / 2 - x..Real.pi, Real.cos (x + y) := by
  have hcut0 : 0 ≤ 3 * Real.pi / 2 - x := by
    linarith [Real.pi_pos]
  have hcutpi : 3 * Real.pi / 2 - x ≤ Real.pi := by linarith
  have hcont : Continuous (fun y : ℝ => |Real.cos (x + y)|) :=
    (Real.continuous_cos.comp (continuous_const.add continuous_id)).abs
  have hleft :
      (∫ y in (0 : ℝ)..3 * Real.pi / 2 - x, |Real.cos (x + y)|) =
        -(∫ y in (0 : ℝ)..3 * Real.pi / 2 - x, Real.cos (x + y)) := by
    calc
      (∫ y in (0 : ℝ)..3 * Real.pi / 2 - x, |Real.cos (x + y)|) =
          ∫ y in (0 : ℝ)..3 * Real.pi / 2 - x, -Real.cos (x + y) := by
        apply intervalIntegral.integral_congr
        intro y hy
        rw [Set.uIcc_of_le hcut0] at hy
        rcases hy with ⟨hy0, hycut⟩
        have hcos : Real.cos (x + y) ≤ 0 :=
          Real.cos_nonpos_of_pi_div_two_le_of_le
            (by linarith) (by linarith)
        change |Real.cos (x + y)| = -Real.cos (x + y)
        exact abs_of_nonpos hcos
      _ = -(∫ y in (0 : ℝ)..3 * Real.pi / 2 - x, Real.cos (x + y)) := by
        rw [intervalIntegral.integral_neg]
  have hright :
      (∫ y in 3 * Real.pi / 2 - x..Real.pi, |Real.cos (x + y)|) =
        ∫ y in 3 * Real.pi / 2 - x..Real.pi, Real.cos (x + y) := by
    apply intervalIntegral.integral_congr
    intro y hy
    rw [Set.uIcc_of_le hcutpi] at hy
    rcases hy with ⟨hycut, hypi⟩
    have hreflect :
        0 ≤ Real.cos (2 * Real.pi - (x + y)) := by
      apply Real.cos_nonneg_of_mem_Icc
      constructor <;> linarith [Real.pi_pos]
    have hcos : 0 ≤ Real.cos (x + y) := by
      simpa only [Real.cos_two_pi_sub] using hreflect
    change |Real.cos (x + y)| = Real.cos (x + y)
    exact abs_of_nonneg hcos
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hcont.intervalIntegrable 0 (3 * Real.pi / 2 - x))
    (hcont.intervalIntegrable (3 * Real.pi / 2 - x) Real.pi)]
  rw [hleft, hright]

private theorem inner_abs_eq_two (x : ℝ)
    (hx : x ∈ Set.Icc (0 : ℝ) Real.pi) :
    (∫ y in (0 : ℝ)..Real.pi, |Real.cos (x + y)|) = 2 := by
  by_cases hxhalf : x ≤ Real.pi / 2
  · exact
      (abs_integral_eq_first_split x hx.1 hxhalf).trans
        (first_split_eq_two x)
  · have hxhalf' : Real.pi / 2 ≤ x := le_of_lt (lt_of_not_ge hxhalf)
    exact
      (abs_integral_eq_second_split x hxhalf' hx.2).trans
        (second_split_eq_two x)

private theorem first_outer_eq_const :
    (∫ x in (0 : ℝ)..Real.pi / 2,
      (∫ y in (0 : ℝ)..Real.pi / 2 - x, Real.cos (x + y)) -
        ∫ y in Real.pi / 2 - x..Real.pi, Real.cos (x + y)) =
      ∫ x in (0 : ℝ)..Real.pi / 2, (2 : ℝ) := by
  apply intervalIntegral.integral_congr
  intro x hx
  exact first_split_eq_two x

private theorem second_outer_eq_const :
    (∫ x in Real.pi / 2..Real.pi,
      -(∫ y in (0 : ℝ)..3 * Real.pi / 2 - x, Real.cos (x + y)) +
        ∫ y in 3 * Real.pi / 2 - x..Real.pi, Real.cos (x + y)) =
      ∫ x in Real.pi / 2..Real.pi, (2 : ℝ) := by
  apply intervalIntegral.integral_congr
  intro x hx
  exact second_split_eq_two x

theorem gap1 :
    cosineAbsIntegral =
      ∫ x in (0 : ℝ)..Real.pi,
        ∫ y in (0 : ℝ)..Real.pi, |Real.cos (x + y)| := by
  let f : ℝ × ℝ → ℝ := fun p => |Real.cos (p.1 + p.2)|
  have hfcont : Continuous f := by
    exact (Real.continuous_cos.comp (continuous_fst.add continuous_snd)).abs
  have hfintOn :
      IntegrableOn f
        (Set.Icc (0 : ℝ) Real.pi ×ˢ Set.Icc (0 : ℝ) Real.pi) :=
    hfcont.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have hfint :
      Integrable f
        ((MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) Real.pi)).prod
          (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) Real.pi))) := by
    rw [Measure.prod_restrict]
    exact hfintOn
  unfold cosineAbsIntegral square
  change (∫ p in Set.Icc (0 : ℝ) Real.pi ×ˢ Set.Icc (0 : ℝ) Real.pi, f p) = _
  calc
    (∫ p in Set.Icc (0 : ℝ) Real.pi ×ˢ Set.Icc (0 : ℝ) Real.pi, f p) =
        ∫ x in Set.Icc (0 : ℝ) Real.pi,
          ∫ y in Set.Icc (0 : ℝ) Real.pi, |Real.cos (x + y)| := by
      rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
      exact MeasureTheory.integral_prod _ hfint
    _ = ∫ x in Set.Icc (0 : ℝ) Real.pi,
          ∫ y in Set.Ioc (0 : ℝ) Real.pi, |Real.cos (x + y)| := by
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Icc
      intro x hx
      exact MeasureTheory.integral_Icc_eq_integral_Ioc
    _ = ∫ x in Set.Ioc (0 : ℝ) Real.pi,
          ∫ y in Set.Ioc (0 : ℝ) Real.pi, |Real.cos (x + y)| := by
      exact MeasureTheory.integral_Icc_eq_integral_Ioc
    _ = ∫ x in (0 : ℝ)..Real.pi,
          ∫ y in (0 : ℝ)..Real.pi, |Real.cos (x + y)| := by
      rw [intervalIntegral.integral_of_le Real.pi_pos.le]
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
      intro x hx
      change
        (∫ y in Set.Ioc (0 : ℝ) Real.pi, |Real.cos (x + y)|) =
          ∫ y in (0 : ℝ)..Real.pi, |Real.cos (x + y)|
      rw [intervalIntegral.integral_of_le Real.pi_pos.le]

private theorem cosine_eq_constant_splits :
    cosineAbsIntegral =
      (∫ x in (0 : ℝ)..Real.pi / 2, (2 : ℝ)) +
        ∫ x in Real.pi / 2..Real.pi, (2 : ℝ) := by
  rw [gap1]
  calc
    (∫ x in (0 : ℝ)..Real.pi,
        ∫ y in (0 : ℝ)..Real.pi, |Real.cos (x + y)|) =
        ∫ x in (0 : ℝ)..Real.pi, (2 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le Real.pi_pos.le] at hx
      change (∫ y in (0 : ℝ)..Real.pi, |Real.cos (x + y)|) = 2
      exact inner_abs_eq_two x hx
    _ = (∫ x in (0 : ℝ)..Real.pi / 2, (2 : ℝ)) +
          ∫ x in Real.pi / 2..Real.pi, (2 : ℝ) := by
      simp
      ring

theorem gap2 :
    cosineAbsIntegral = splitExpression := by
  calc
    cosineAbsIntegral =
        (∫ x in (0 : ℝ)..Real.pi / 2, (2 : ℝ)) +
          ∫ x in Real.pi / 2..Real.pi, (2 : ℝ) :=
      cosine_eq_constant_splits
    _ = splitExpression := by
      unfold splitExpression
      rw [first_outer_eq_const, second_outer_eq_const]

theorem gap3 :
    cosineAbsIntegral =
      (∫ x in (0 : ℝ)..Real.pi / 2, (2 : ℝ)) +
        ∫ x in Real.pi / 2..Real.pi, (2 : ℝ) := by
  exact cosine_eq_constant_splits

theorem gap4 :
    (∫ x in (0 : ℝ)..Real.pi / 2, (2 : ℝ)) +
        (∫ x in Real.pi / 2..Real.pi, (2 : ℝ)) =
      2 * Real.pi := by
  simp
  ring

theorem gap5 :
    cosineAbsIntegral = 2 * Real.pi := by
  exact gap3.trans gap4

end

end ProofGap.Exercise3971
