import ProofGapLean.Prelude.Analysis
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Orthogonality

namespace ProofGap.Exercise2337
noncomputable section

open Filter
open scoped Interval

def integrand (x : ℝ) : ℝ := 1 / Real.sqrt (1 - x ^ 2)

def HasSplitImproperValue (L : ℝ) : Prop :=
  ∃ l r : ℝ,
    Tendsto (fun ε => ∫ x in (-1 + ε)..0, integrand x)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds l) ∧
    Tendsto (fun ε => ∫ x in (0 : ℝ)..(1 - ε), integrand x)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds r) ∧
    l + r = L

def HasEndpointExpressionValue (L : ℝ) : Prop :=
  ∃ l r : ℝ,
    Tendsto (fun ε : ℝ => -Real.arcsin (-1 + ε))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds l) ∧
    Tendsto (fun ε : ℝ => Real.arcsin (1 - ε))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds r) ∧
    l + r = L

private theorem endpoint_integral_eventually_left :
    (fun ε : ℝ => ∫ x in (-1 + ε)..0, integrand x) =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
      (fun ε : ℝ => -Real.arcsin (-1 + ε)) := by
  have hintAll : IntervalIntegrable integrand MeasureTheory.volume (-1) 1 := by
    unfold integrand
    simpa [one_div] using
      Polynomial.Chebyshev.intervalIntegrable_sqrt_one_sub_sq_inv
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
  have hle : -1 + ε ≤ 0 := by linarith [hε.2]
  have hint : IntervalIntegrable integrand MeasureTheory.volume (-1 + ε) 0 := by
    apply hintAll.mono_set
    rw [Set.uIcc_of_le hle, Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    intro x hx
    constructor <;> linarith [hx.1, hx.2, hε.1]
  have hcalc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (f := Real.arcsin) (f' := integrand) hle Real.continuous_arcsin.continuousOn
    (fun x hx => by
      simpa [integrand] using Real.hasDerivAt_arcsin
        (by linarith [hx.1, hε.1]) (by linarith [hx.2])) hint
  simpa using hcalc

private theorem endpoint_integral_eventually_right :
    (fun ε : ℝ => ∫ x in (0 : ℝ)..(1 - ε), integrand x) =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
      (fun ε : ℝ => Real.arcsin (1 - ε)) := by
  have hintAll : IntervalIntegrable integrand MeasureTheory.volume (-1) 1 := by
    unfold integrand
    simpa [one_div] using
      Polynomial.Chebyshev.intervalIntegrable_sqrt_one_sub_sq_inv
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
  have hle : 0 ≤ 1 - ε := by linarith [hε.2]
  have hint : IntervalIntegrable integrand MeasureTheory.volume 0 (1 - ε) := by
    apply hintAll.mono_set
    rw [Set.uIcc_of_le hle, Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    intro x hx
    constructor <;> linarith [hx.1, hx.2, hε.1]
  have hcalc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (f := Real.arcsin) (f' := integrand) hle Real.continuous_arcsin.continuousOn
    (fun x hx => by
      simpa [integrand] using Real.hasDerivAt_arcsin
        (by linarith [hx.1]) (by linarith [hx.2, hε.1])) hint
  simpa using hcalc

theorem gap1 :
    HasSplitImproperValue Real.pi ↔ HasEndpointExpressionValue Real.pi := by
  constructor
  · rintro ⟨l, r, hl, hr, hadd⟩
    exact ⟨l, r, hl.congr' endpoint_integral_eventually_left,
      hr.congr' endpoint_integral_eventually_right, hadd⟩
  · rintro ⟨l, r, hl, hr, hadd⟩
    exact ⟨l, r, hl.congr' endpoint_integral_eventually_left.symm,
      hr.congr' endpoint_integral_eventually_right.symm, hadd⟩

theorem gap2 : HasEndpointExpressionValue Real.pi := by
  have hid : Tendsto (fun ε : ℝ => ε) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have hleftArg : Tendsto (fun ε : ℝ => -1 + ε)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (-1)) := by
    simpa using tendsto_const_nhds.add hid
  have hrightArg : Tendsto (fun ε : ℝ => 1 - ε)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    simpa using tendsto_const_nhds.sub hid
  refine ⟨Real.pi / 2, Real.pi / 2, ?_, ?_, by ring⟩
  · simpa using (Real.continuousAt_arcsin.tendsto.comp hleftArg).neg
  · simpa using Real.continuousAt_arcsin.tendsto.comp hrightArg

theorem gap3 : HasSplitImproperValue Real.pi := by
  exact gap1.mpr gap2

theorem gap4 :
    (∫ x in (-1 : ℝ)..1, integrand x) = Real.pi := by
  have hint : IntervalIntegrable integrand MeasureTheory.volume (-1) 1 := by
    unfold integrand
    simpa [one_div] using
      Polynomial.Chebyshev.intervalIntegrable_sqrt_one_sub_sq_inv
  have hcalc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (f := Real.arcsin) (f' := integrand) (by norm_num : (-1 : ℝ) ≤ 1)
    Real.continuous_arcsin.continuousOn
    (fun x hx => by
      simpa [integrand] using Real.hasDerivAt_arcsin
        (by linarith [hx.1]) (by linarith [hx.2])) hint
  simpa using hcalc

end
end ProofGap.Exercise2337
