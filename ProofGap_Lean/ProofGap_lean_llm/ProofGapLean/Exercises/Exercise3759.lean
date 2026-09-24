import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

namespace ProofGap.Exercise3759

noncomputable section

open MeasureTheory
open scoped Interval

def shiftedKernel (α x : ℝ) : ℝ :=
  1 / ((x + α) ^ 2 + 1)

def majorant (x : ℝ) : ℝ :=
  1 / (1 + x ^ 2)

theorem gap1 (x α : ℝ) :
    0 < shiftedKernel α x := by
  unfold shiftedKernel
  positivity

theorem gap2 (x α : ℝ) (hx : 0 ≤ x) (hα : 0 ≤ α) :
    shiftedKernel α x ≤ majorant x := by
  have hsq : x ^ 2 ≤ (x + α) ^ 2 := by
    nlinarith [sq_nonneg α, mul_nonneg hx hα]
  unfold shiftedKernel majorant
  apply one_div_le_one_div_of_le (by positivity)
  nlinarith

theorem gap3 (x : ℝ) :
    0 < majorant x := by
  unfold majorant
  positivity

theorem gap4 :
    (∫ x in Set.Ioi (0 : ℝ), majorant x) = Real.pi / 2 := by
  simpa [majorant, one_div] using
    (integral_Ioi_inv_one_add_sq (i := (0 : ℝ)))

theorem gap5 (ε : ℝ) (hε : 0 < ε) :
    ∃ A₀ : ℝ, 0 < A₀ ∧
      ∀ A A₁ α : ℝ, A₀ < A → A < A₁ → 0 ≤ α →
        |∫ x in A..A₁, shiftedKernel α x| < ε := by
  have hmajorant : Integrable majorant := by
    exact integrable_inv_one_add_sq.congr
      (Filter.Eventually.of_forall fun x => by
        unfold majorant
        rw [one_div])
  have hatan :
      Filter.Tendsto Real.arctan Filter.atTop (nhds (Real.pi / 2)) :=
    tendsto_nhds_of_tendsto_nhdsWithin Real.tendsto_arctan_atTop
  have hdiff :
      Filter.Tendsto (fun A : ℝ => Real.pi / 2 - Real.arctan A)
        Filter.atTop (nhds 0) := by
    have hconst :
        Filter.Tendsto (fun _ : ℝ => Real.pi / 2) Filter.atTop
          (nhds (Real.pi / 2)) :=
      tendsto_const_nhds
    simpa only [sub_self] using hconst.sub hatan
  have htail :
      Filter.Tendsto (fun A : ℝ => ∫ x in Set.Ioi A, majorant x)
        Filter.atTop (nhds 0) := by
    simpa [majorant, one_div] using hdiff
  have hev :
      ∀ᶠ A : ℝ in Filter.atTop,
        (∫ x in Set.Ioi A, majorant x) < ε :=
    htail.eventually (Iio_mem_nhds hε)
  rcases (Filter.eventually_atTop.1 hev) with ⟨B, hB⟩
  let A₀ := max B 1
  have hA₀pos : 0 < A₀ := by
    exact lt_of_lt_of_le zero_lt_one (le_max_right B 1)
  refine ⟨A₀, hA₀pos, ?_⟩
  intro A A₁ α hA hAA₁ hα
  have hpoint :
      ∀ᵐ t : ℝ ∂volume, t ∈ Set.Ioc A A₁ →
        ‖shiftedKernel α t‖ ≤ majorant t :=
    Filter.Eventually.of_forall fun t ht => by
      rw [Real.norm_eq_abs, abs_of_pos (gap1 t α)]
      apply gap2 t α
      · exact le_of_lt (hA₀pos.trans (hA.trans ht.1))
      · exact hα
  have hinterval :
      |∫ x in A..A₁, shiftedKernel α x| ≤
        ∫ x in A..A₁, majorant x := by
    simpa only [Real.norm_eq_abs] using
      (intervalIntegral.norm_integral_le_of_norm_le
        hAA₁.le hpoint hmajorant.intervalIntegrable)
  have hsubset :
      ∫ x in A..A₁, majorant x ≤
        ∫ x in Set.Ioi A, majorant x := by
    rw [intervalIntegral.integral_of_le hAA₁.le]
    exact MeasureTheory.setIntegral_mono_set
      hmajorant.integrableOn
      (Filter.Eventually.of_forall fun t => (gap3 t).le)
      (Filter.Eventually.of_forall fun t ht => ht.1)
  have hB_le_A : B ≤ A :=
    (le_max_left B 1).trans hA.le
  exact hinterval.trans_lt (hsubset.trans_lt (hB A hB_le_A))

theorem gap6 (ε : ℝ) (hε : 0 < ε) :
    ∃ A₀ : ℝ, 0 < A₀ ∧
      ∀ A A₁ α : ℝ, A₀ < A → A < A₁ → 0 ≤ α →
        |∫ x in A..A₁, shiftedKernel α x| < ε := by
  exact gap5 ε hε

end

end ProofGap.Exercise3759
