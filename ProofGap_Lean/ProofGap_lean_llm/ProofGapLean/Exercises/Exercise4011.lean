import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4011

noncomputable section

open MeasureTheory
open scoped Interval

def baseRegion : Set (ℝ × ℝ) :=
  {p | 0 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ Real.pi}

def volume : ℝ :=
  ∫ p in baseRegion, Real.sin (Real.pi * p.2 / (2 * p.1))

private theorem ae_real_ne_zero :
    ∀ᵐ x : ℝ ∂(MeasureTheory.volume : Measure ℝ), x ≠ 0 := by
  rw [ae_iff]
  simpa using (measure_singleton (0 : ℝ))

private theorem integral_sin_mul (c b : ℝ) (hc : c ≠ 0) :
    (∫ y in (0 : ℝ)..b, Real.sin (c * y)) =
      (1 - Real.cos (c * b)) / c := by
  have hderiv : ∀ y : ℝ,
      HasDerivAt (fun z : ℝ => -Real.cos (c * z) / c)
        (Real.sin (c * y)) y := by
    intro y
    simpa [hc] using
      ((((Real.hasDerivAt_cos (c * y)).comp y
        ((hasDerivAt_const y c).mul (hasDerivAt_id y))).neg).div_const c)
  have hint :
      IntervalIntegrable (fun y : ℝ => Real.sin (c * y))
        MeasureTheory.volume 0 b :=
    (Real.continuous_sin.comp
      (continuous_const.mul continuous_id)).intervalIntegrable 0 b
  calc
    (∫ y in (0 : ℝ)..b, Real.sin (c * y)) =
        -Real.cos (c * b) / c - (-Real.cos (c * 0) / c) := by
      exact intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun y _ => hderiv y) hint
    _ = (1 - Real.cos (c * b)) / c := by
      simp
      ring

private theorem inner_integral (x : ℝ) :
    (∫ y in (0 : ℝ)..x,
      Real.sin (Real.pi * y / (2 * x))) =
      2 / Real.pi * x := by
  by_cases hx : x = 0
  · subst x
    simp
  · have hc : Real.pi / (2 * x) ≠ 0 :=
      div_ne_zero Real.pi_ne_zero (mul_ne_zero (by norm_num) hx)
    have hformula :
        (∫ y in (0 : ℝ)..x,
          Real.sin (Real.pi * y / (2 * x))) =
          (1 - Real.cos ((Real.pi / (2 * x)) * x)) /
            (Real.pi / (2 * x)) := by
      simpa only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
        integral_sin_mul (Real.pi / (2 * x)) x hc
    calc
      (∫ y in (0 : ℝ)..x,
          Real.sin (Real.pi * y / (2 * x))) =
          (1 - Real.cos ((Real.pi / (2 * x)) * x)) /
            (Real.pi / (2 * x)) :=
        hformula
      _ = 2 / Real.pi * x := by
        rw [show (Real.pi / (2 * x)) * x = Real.pi / 2 by
          field_simp [hx]
          <;> ring]
        rw [Real.cos_pi_div_two]
        field_simp [Real.pi_ne_zero, hx]
        <;> ring

theorem gap1 :
    volume =
      ∫ x in (0 : ℝ)..Real.pi,
        ∫ y in (0 : ℝ)..x,
          Real.sin (Real.pi * y / (2 * x)) := by
  have hclosed : IsClosed baseRegion := by
    change IsClosed
      ({p : ℝ × ℝ | 0 ≤ p.2} ∩
        ({p : ℝ × ℝ | p.2 ≤ p.1} ∩
          {p : ℝ × ℝ | p.1 ≤ Real.pi}))
    exact
      (isClosed_le continuous_const continuous_snd).inter
        ((isClosed_le continuous_snd continuous_fst).inter
          (isClosed_le continuous_fst continuous_const))
  have hsub :
      baseRegion ⊆
        Set.Icc (0 : ℝ) Real.pi ×ˢ Set.Icc (0 : ℝ) Real.pi := by
    intro p hp
    change 0 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ Real.pi at hp
    exact
      ⟨⟨hp.1.trans hp.2.1, hp.2.2⟩,
        ⟨hp.1, hp.2.1.trans hp.2.2⟩⟩
  have hcompact : IsCompact baseRegion :=
    (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset hclosed hsub
  have hmeasurable :
      Measurable
        (fun p : ℝ × ℝ =>
          Real.sin (Real.pi * p.2 / (2 * p.1))) :=
    ((measurable_const.mul measurable_snd).div
      (measurable_const.mul measurable_fst)).sin
  have hintegrableOn :
      IntegrableOn
        (fun p : ℝ × ℝ =>
          Real.sin (Real.pi * p.2 / (2 * p.1)))
        baseRegion
        ((MeasureTheory.volume : Measure ℝ).prod MeasureTheory.volume) := by
    refine Measure.integrableOn_of_bounded (M := 1)
      hcompact.measure_ne_top hmeasurable.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun p => by
      simpa only [Real.norm_eq_abs] using
        Real.abs_sin_le_one (Real.pi * p.2 / (2 * p.1))
  have hintegrable :
      Integrable
        (baseRegion.indicator
          (fun p : ℝ × ℝ =>
            Real.sin (Real.pi * p.2 / (2 * p.1))))
        ((MeasureTheory.volume : Measure ℝ).prod MeasureTheory.volume) :=
    (integrable_indicator_iff hclosed.measurableSet).2 hintegrableOn
  change
    (∫ p in baseRegion,
      Real.sin (Real.pi * p.2 / (2 * p.1))) = _
  calc
    (∫ p in baseRegion,
        Real.sin (Real.pi * p.2 / (2 * p.1))) =
        ∫ p : ℝ × ℝ,
          baseRegion.indicator
            (fun q : ℝ × ℝ =>
              Real.sin (Real.pi * q.2 / (2 * q.1))) p := by
      rw [integral_indicator hclosed.measurableSet]
    _ = ∫ x : ℝ, ∫ y : ℝ,
        baseRegion.indicator
          (fun q : ℝ × ℝ =>
            Real.sin (Real.pi * q.2 / (2 * q.1))) (x, y) := by
      exact integral_prod _ hintegrable
    _ = ∫ x in (0 : ℝ)..Real.pi,
        ∫ y in (0 : ℝ)..x,
          Real.sin (Real.pi * y / (2 * x)) := by
      rw [intervalIntegral.integral_of_le Real.pi_nonneg]
      rw [← integral_indicator measurableSet_Ioc]
      apply integral_congr_ae
      filter_upwards [ae_real_ne_zero] with x hx0
      by_cases hx : x ∈ Set.Ioc (0 : ℝ) Real.pi
      · rw [Set.indicator_of_mem hx]
        rw [intervalIntegral.integral_of_le hx.1.le]
        rw [← integral_indicator measurableSet_Ioc]
        apply integral_congr_ae
        filter_upwards [ae_real_ne_zero] with y hy0
        have hmem :
            (x, y) ∈ baseRegion ↔ y ∈ Set.Ioc (0 : ℝ) x := by
          constructor
          · intro h
            change 0 ≤ y ∧ y ≤ x ∧ x ≤ Real.pi at h
            exact ⟨lt_of_le_of_ne h.1 (Ne.symm hy0), h.2.1⟩
          · intro h
            change 0 ≤ y ∧ y ≤ x ∧ x ≤ Real.pi
            exact ⟨h.1.le, h.2, hx.2⟩
        by_cases h : (x, y) ∈ baseRegion
        · simp only [Set.indicator_of_mem h,
            Set.indicator_of_mem (hmem.mp h)]
        · have hi : y ∉ Set.Ioc (0 : ℝ) x :=
            fun hi => h (hmem.mpr hi)
          simp [h, hi]
      · have hempty : ∀ y : ℝ, (x, y) ∉ baseRegion := by
          intro y h
          apply hx
          change 0 ≤ y ∧ y ≤ x ∧ x ≤ Real.pi at h
          exact
            ⟨lt_of_le_of_ne (h.1.trans h.2.1) (Ne.symm hx0),
              h.2.2⟩
        have hzero :
            (fun y : ℝ =>
              baseRegion.indicator
                (fun q : ℝ × ℝ =>
                  Real.sin (Real.pi * q.2 / (2 * q.1)))
                (x, y)) = 0 := by
          funext y
          simp [hempty y]
        simp [hx, hzero]

theorem gap2 :
    (∫ x in (0 : ℝ)..Real.pi,
        ∫ y in (0 : ℝ)..x,
          Real.sin (Real.pi * y / (2 * x))) =
      2 / Real.pi * ∫ x in (0 : ℝ)..Real.pi, x := by
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro x hx
  exact inner_integral x

theorem gap3 :
    2 / Real.pi * (∫ x in (0 : ℝ)..Real.pi, x) =
      Real.pi := by
  rw [integral_id]
  field_simp [Real.pi_ne_zero]
  ring

theorem gap4 :
    volume = Real.pi := by
  rw [gap1, gap2, gap3]

end

end ProofGap.Exercise4011
