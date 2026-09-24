import ProofGapLean.Prelude.Analysis
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods

namespace ProofGap.Exercise2390_1
noncomputable section

open Filter Set
open scoped Interval

def pvTrunc (ε : ℝ) : ℝ :=
  (∫ x in (-1 : ℝ)..(-ε), 1 / x) + ∫ x in ε..1, 1 / x

theorem gap1 (ε : ℝ) (hε : ε ∈ Ioc 0 1) :
    pvTrunc ε =
      (Real.log ε - Real.log 1) + (Real.log 1 - Real.log ε) := by
  unfold pvTrunc
  have hcont_left :
      ContinuousOn (fun x : ℝ => 1 / x) (uIcc (-1) (-ε)) := by
    apply ContinuousOn.div continuousOn_const continuousOn_id
    intro x hx
    have hx' : x ∈ Icc (-1) (-ε) := by
      simpa only [uIcc_of_le (neg_le_neg hε.2)] using hx
    exact ne_of_lt (lt_of_le_of_lt hx'.2 (neg_lt_zero.mpr hε.1))
  have hdiff_left :
      ∀ x ∈ uIcc (-1 : ℝ) (-ε), DifferentiableAt ℝ Real.log x := by
    intro x hx
    have hx' : x ∈ Icc (-1) (-ε) := by
      simpa only [uIcc_of_le (neg_le_neg hε.2)] using hx
    have hx0 : x ≠ 0 :=
      ne_of_lt (lt_of_le_of_lt hx'.2 (neg_lt_zero.mpr hε.1))
    exact (Real.hasDerivAt_log hx0).differentiableAt
  have hderiv_left :
      ∀ x ∈ uIcc (-1 : ℝ) (-ε), deriv Real.log x = 1 / x := by
    intro x hx
    have hx' : x ∈ Icc (-1) (-ε) := by
      simpa only [uIcc_of_le (neg_le_neg hε.2)] using hx
    have hx0 : x ≠ 0 :=
      ne_of_lt (lt_of_le_of_lt hx'.2 (neg_lt_zero.mpr hε.1))
    simpa only [one_div] using (Real.hasDerivAt_log hx0).deriv
  have hcont_deriv_left :
      ContinuousOn (deriv Real.log) (uIcc (-1 : ℝ) (-ε)) :=
    hcont_left.congr fun x hx => hderiv_left x hx
  have hleft :
      (∫ x in (-1 : ℝ)..(-ε), 1 / x) =
        Real.log (-ε) - Real.log (-1) := by
    calc
      (∫ x in (-1 : ℝ)..(-ε), 1 / x) =
          ∫ x in (-1 : ℝ)..(-ε), deriv Real.log x := by
            apply intervalIntegral.integral_congr
            intro x hx
            exact (hderiv_left x hx).symm
      _ = Real.log (-ε) - Real.log (-1) :=
        intervalIntegral.integral_deriv_eq_sub hdiff_left
          hcont_deriv_left.intervalIntegrable
  have hcont_right :
      ContinuousOn (fun x : ℝ => 1 / x) (uIcc ε 1) := by
    apply ContinuousOn.div continuousOn_const continuousOn_id
    intro x hx
    have hx' : x ∈ Icc ε 1 := by
      simpa only [uIcc_of_le hε.2] using hx
    exact ne_of_gt (lt_of_lt_of_le hε.1 hx'.1)
  have hdiff_right :
      ∀ x ∈ uIcc ε 1, DifferentiableAt ℝ Real.log x := by
    intro x hx
    have hx' : x ∈ Icc ε 1 := by
      simpa only [uIcc_of_le hε.2] using hx
    have hx0 : x ≠ 0 := ne_of_gt (lt_of_lt_of_le hε.1 hx'.1)
    exact (Real.hasDerivAt_log hx0).differentiableAt
  have hderiv_right :
      ∀ x ∈ uIcc ε 1, deriv Real.log x = 1 / x := by
    intro x hx
    have hx' : x ∈ Icc ε 1 := by
      simpa only [uIcc_of_le hε.2] using hx
    have hx0 : x ≠ 0 := ne_of_gt (lt_of_lt_of_le hε.1 hx'.1)
    simpa only [one_div] using (Real.hasDerivAt_log hx0).deriv
  have hcont_deriv_right :
      ContinuousOn (deriv Real.log) (uIcc ε 1) :=
    hcont_right.congr fun x hx => hderiv_right x hx
  have hright :
      (∫ x in ε..1, 1 / x) = Real.log 1 - Real.log ε := by
    calc
      (∫ x in ε..1, 1 / x) = ∫ x in ε..1, deriv Real.log x := by
        apply intervalIntegral.integral_congr
        intro x hx
        exact (hderiv_right x hx).symm
      _ = Real.log 1 - Real.log ε :=
        intervalIntegral.integral_deriv_eq_sub hdiff_right
          hcont_deriv_right.intervalIntegrable
  simpa only [hleft, hright, Real.log_neg_eq_log]

theorem gap2 (ε : ℝ) (hε : 0 < ε) :
    (Real.log ε - Real.log 1) + (Real.log 1 - Real.log ε) = 0 := by
  simp

theorem gap3 (ε : ℝ) (hε : ε ∈ Ioc 0 1) :
    pvTrunc ε = 0 := by
  exact (gap1 ε hε).trans (gap2 ε hε.1)

theorem gap4 :
    Tendsto pvTrunc (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  have hlt : ∀ᶠ x in nhdsWithin (0 : ℝ) (Ioi 0), x < 1 :=
    (eventually_lt_nhds (show (0 : ℝ) < 1 from zero_lt_one)).filter_mono
      inf_le_left
  have hpos : ∀ᶠ x in nhdsWithin (0 : ℝ) (Ioi 0), x ∈ Ioi 0 := by
    exact self_mem_nhdsWithin
  have hpv :
      pvTrunc =ᶠ[nhdsWithin (0 : ℝ) (Ioi 0)] (fun _ => (0 : ℝ)) :=
    (hpos.and hlt).mono fun x hx =>
      gap3 x ⟨hx.1, le_of_lt hx.2⟩
  exact
    (tendsto_const_nhds :
      Tendsto (fun _ : ℝ => (0 : ℝ))
        (nhdsWithin 0 (Ioi 0)) (nhds 0)).congr' hpv.symm

end
end ProofGap.Exercise2390_1
