import ProofGapLean.Prelude.Analysis
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

namespace ProofGap.Exercise2336
noncomputable section

open Filter MeasureTheory
open scoped Interval

def integrand (x : ℝ) : ℝ := 1 / (1 + x ^ 2)

def HasTwoSidedImproperValue (L : ℝ) : Prop :=
  ∃ l r : ℝ,
    Tendsto (fun a => ∫ x in a..0, integrand x) atBot (nhds l) ∧
    Tendsto (fun b => ∫ x in (0 : ℝ)..b, integrand x) atTop (nhds r) ∧
    l + r = L

theorem gap1 : HasTwoSidedImproperValue Real.pi := by
  have hbot : Tendsto Real.arctan atBot (nhds (-(Real.pi / 2))) :=
    (tendsto_nhdsWithin_iff.mp Real.tendsto_arctan_atBot).1
  have htop : Tendsto Real.arctan atTop (nhds (Real.pi / 2)) :=
    (tendsto_nhdsWithin_iff.mp Real.tendsto_arctan_atTop).1
  refine ⟨Real.pi / 2, Real.pi / 2, ?_, ?_, by ring⟩
  · simpa [integrand, one_div, integral_inv_one_add_sq] using hbot.neg
  · simpa [integrand, one_div, integral_inv_one_add_sq] using htop

theorem gap2 : (∫ x : ℝ, integrand x) = Real.pi := by
  unfold integrand
  simpa [one_div] using integral_univ_inv_one_add_sq

end
end ProofGap.Exercise2336
