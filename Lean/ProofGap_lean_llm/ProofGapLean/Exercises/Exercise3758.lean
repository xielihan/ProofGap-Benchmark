import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

namespace ProofGap.Exercise3758

noncomputable section

open MeasureTheory

def integrand (α x : ℝ) : ℝ :=
  Real.cos (α * x) / (1 + x ^ 2)

def majorant (x : ℝ) : ℝ :=
  1 / (1 + x ^ 2)

theorem gap1 (α x : ℝ) :
    |integrand α x| ≤ majorant x := by
  have hden : 0 < 1 + x ^ 2 := by positivity
  rw [integrand, majorant, abs_div, abs_of_pos hden]
  exact (div_le_div_iff_of_pos_right hden).2 (Real.abs_cos_le_one (α * x))

theorem gap2 :
    (∫ x : ℝ, majorant x) = Real.pi := by
  simpa [majorant, one_div] using integral_univ_inv_one_add_sq

theorem gap3 (ε : ℝ) (hε : 0 < ε) :
    ∃ A₀ : ℝ, ∀ A α : ℝ, A₀ < A →
      |∫ x in Set.Ioi A, integrand α x| < ε := by
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
  rcases (Filter.eventually_atTop.1 hev) with ⟨A₀, hA₀⟩
  refine ⟨A₀, fun A α hA => ?_⟩
  have hbound :
      |∫ x in Set.Ioi A, integrand α x| ≤
        ∫ x in Set.Ioi A, majorant x := by
    simpa only [Real.norm_eq_abs] using
      (norm_integral_le_of_norm_le
        (f := integrand α) (g := majorant)
        (μ := volume.restrict (Set.Ioi A))
        hmajorant.integrableOn
        (Filter.Eventually.of_forall fun x => gap1 α x))
  exact hbound.trans_lt (hA₀ A hA.le)

theorem gap4 (ε : ℝ) (hε : 0 < ε) :
    ∃ A₀ : ℝ, ∀ A α : ℝ, A₀ < A →
      |∫ x in Set.Ioi A, integrand α x| < ε := by
  exact gap3 ε hε

end

end ProofGap.Exercise3758
