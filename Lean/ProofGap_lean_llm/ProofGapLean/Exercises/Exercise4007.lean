import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4007

noncomputable section

open MeasureTheory
open scoped Interval

def baseRegion : Set (ℝ × ℝ) :=
  {p | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ 1}

def volume : ℝ :=
  ∫ p in baseRegion, 1 + p.1 + p.2

private theorem ae_real_ne_zero :
    ∀ᵐ x : ℝ ∂(MeasureTheory.volume : Measure ℝ), x ≠ 0 := by
  rw [ae_iff]
  simpa using (measure_singleton (0 : ℝ))

theorem gap1 :
    volume =
      ∫ x in (0 : ℝ)..1,
        ∫ y in (0 : ℝ)..1 - x, 1 + x + y := by
  have hclosed : IsClosed baseRegion := by
    change IsClosed
      ({p : ℝ × ℝ | 0 ≤ p.1} ∩
        ({p : ℝ × ℝ | 0 ≤ p.2} ∩ {p : ℝ × ℝ | p.1 + p.2 ≤ 1}))
    exact
      (isClosed_le continuous_const continuous_fst).inter
        ((isClosed_le continuous_const continuous_snd).inter
          (isClosed_le (continuous_fst.add continuous_snd) continuous_const))
  have hsub : baseRegion ⊆ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 := by
    intro p hp
    change 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ 1 at hp
    exact ⟨⟨hp.1, by linarith [hp.2.1, hp.2.2]⟩,
      ⟨hp.2.1, by linarith [hp.1, hp.2.2]⟩⟩
  have hcompact : IsCompact baseRegion :=
    (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset hclosed hsub
  have hcontinuous : Continuous (fun p : ℝ × ℝ => 1 + p.1 + p.2) :=
    (continuous_const.add continuous_fst).add continuous_snd
  have hintegrable :
      Integrable
        (baseRegion.indicator (fun p : ℝ × ℝ => 1 + p.1 + p.2))
        ((MeasureTheory.volume : Measure ℝ).prod MeasureTheory.volume) := by
    refine (integrable_indicator_iff hclosed.measurableSet).2 ?_
    exact hcontinuous.continuousOn.integrableOn_compact hcompact
  change (∫ p in baseRegion, 1 + p.1 + p.2) = _
  calc
    (∫ p in baseRegion, 1 + p.1 + p.2) =
        ∫ p : ℝ × ℝ,
          baseRegion.indicator (fun q : ℝ × ℝ => 1 + q.1 + q.2) p := by
      rw [integral_indicator hclosed.measurableSet]
    _ = ∫ x : ℝ, ∫ y : ℝ,
          baseRegion.indicator (fun q : ℝ × ℝ => 1 + q.1 + q.2) (x, y) := by
      exact integral_prod _ hintegrable
    _ = ∫ x in (0 : ℝ)..1,
          ∫ y in (0 : ℝ)..1 - x, 1 + x + y := by
      rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      rw [← integral_indicator measurableSet_Ioc]
      apply integral_congr_ae
      filter_upwards [ae_real_ne_zero] with x hx0
      by_cases hx : x ∈ Set.Ioc (0 : ℝ) 1
      · rw [Set.indicator_of_mem hx]
        rw [intervalIntegral.integral_of_le (sub_nonneg.mpr hx.2)]
        rw [← integral_indicator measurableSet_Ioc]
        apply integral_congr_ae
        filter_upwards [ae_real_ne_zero] with y hy0
        have hmem :
            (x, y) ∈ baseRegion ↔ y ∈ Set.Ioc (0 : ℝ) (1 - x) := by
          constructor
          · intro h
            change 0 ≤ x ∧ 0 ≤ y ∧ x + y ≤ 1 at h
            exact ⟨lt_of_le_of_ne h.2.1 (Ne.symm hy0), by linarith [h.2.2]⟩
          · intro h
            change 0 ≤ x ∧ 0 ≤ y ∧ x + y ≤ 1
            exact ⟨le_of_lt hx.1, le_of_lt h.1, by linarith [h.2]⟩
        by_cases h : (x, y) ∈ baseRegion
        · simp only [Set.indicator_of_mem h, Set.indicator_of_mem (hmem.mp h)]
        · have hi : y ∉ Set.Ioc (0 : ℝ) (1 - x) :=
            fun hi => h (hmem.mpr hi)
          simp [h, hi]
      · have hempty : ∀ y : ℝ, (x, y) ∉ baseRegion := by
          intro y h
          apply hx
          change 0 ≤ x ∧ 0 ≤ y ∧ x + y ≤ 1 at h
          exact ⟨lt_of_le_of_ne h.1 (Ne.symm hx0), by linarith [h.2.1, h.2.2]⟩
        have hzero :
            (fun y : ℝ =>
              baseRegion.indicator (fun q : ℝ × ℝ => 1 + q.1 + q.2) (x, y)) =
              0 := by
          funext y
          simp [hempty y]
        simp [hx, hzero]

theorem gap2 :
    (∫ x in (0 : ℝ)..1,
        ∫ y in (0 : ℝ)..1 - x, 1 + x + y) =
      ∫ x in (0 : ℝ)..1, 3 / 2 - x - x ^ 2 / 2 := by
  apply intervalIntegral.integral_congr
  intro x hx
  have hderiv : ∀ y : ℝ,
      HasDerivAt
        (fun z : ℝ => (1 + x) * z + (1 / 2 : ℝ) * z ^ 2)
        (1 + x + y) y := by
    intro y
    convert
      ((hasDerivAt_const y (1 + x)).mul (hasDerivAt_id y)).add
        ((hasDerivAt_const y (1 / 2 : ℝ)).mul ((hasDerivAt_id y).pow 2)) using 1 <;>
      simp only [id] <;>
      ring
  have hinterval :
      IntervalIntegrable (fun y : ℝ => 1 + x + y)
        MeasureTheory.volume 0 (1 - x) := by
    have hcont : Continuous (fun y : ℝ => 1 + x + y) :=
      continuous_const.add continuous_id
    exact hcont.intervalIntegrable 0 (1 - x)
  calc
    (∫ y in (0 : ℝ)..1 - x, 1 + x + y) =
        ((1 + x) * (1 - x) + (1 / 2 : ℝ) * (1 - x) ^ 2) -
          ((1 + x) * 0 + (1 / 2 : ℝ) * 0 ^ 2) := by
      exact intervalIntegral.integral_eq_sub_of_hasDerivAt
        (f := fun z : ℝ => (1 + x) * z + (1 / 2 : ℝ) * z ^ 2)
        (f' := fun y : ℝ => 1 + x + y)
        (fun y _ => hderiv y) hinterval
    _ = 3 / 2 - x - x ^ 2 / 2 := by
      ring

theorem gap3 :
    (∫ x in (0 : ℝ)..1, 3 / 2 - x - x ^ 2 / 2) =
      5 / 6 := by
  have hderiv : ∀ x : ℝ,
      HasDerivAt
        (fun z : ℝ =>
          (3 / 2 : ℝ) * z - (1 / 2 : ℝ) * z ^ 2 - (1 / 6 : ℝ) * z ^ 3)
        (3 / 2 - x - x ^ 2 / 2) x := by
    intro x
    convert
      (((hasDerivAt_const x (3 / 2 : ℝ)).mul (hasDerivAt_id x)).sub
        ((hasDerivAt_const x (1 / 2 : ℝ)).mul ((hasDerivAt_id x).pow 2))).sub
        ((hasDerivAt_const x (1 / 6 : ℝ)).mul ((hasDerivAt_id x).pow 3)) using 1 <;>
      simp only [id] <;>
      ring
  have hinterval :
      IntervalIntegrable (fun x : ℝ => 3 / 2 - x - x ^ 2 / 2)
        MeasureTheory.volume 0 1 := by
    have hcont : Continuous (fun x : ℝ => 3 / 2 - x - x ^ 2 / 2) := by
      fun_prop
    exact hcont.intervalIntegrable 0 1
  calc
    (∫ x in (0 : ℝ)..1, 3 / 2 - x - x ^ 2 / 2) =
        ((3 / 2 : ℝ) * 1 - (1 / 2 : ℝ) * 1 ^ 2 - (1 / 6 : ℝ) * 1 ^ 3) -
          ((3 / 2 : ℝ) * 0 - (1 / 2 : ℝ) * 0 ^ 2 - (1 / 6 : ℝ) * 0 ^ 3) := by
      exact intervalIntegral.integral_eq_sub_of_hasDerivAt
        (f := fun z : ℝ =>
          (3 / 2 : ℝ) * z - (1 / 2 : ℝ) * z ^ 2 - (1 / 6 : ℝ) * z ^ 3)
        (f' := fun x : ℝ => 3 / 2 - x - x ^ 2 / 2)
        (fun x _ => hderiv x) hinterval
    _ = 5 / 6 := by
      norm_num

theorem gap4 :
    volume = 5 / 6 := by
  rw [gap1, gap2, gap3]

end

end ProofGap.Exercise4007
