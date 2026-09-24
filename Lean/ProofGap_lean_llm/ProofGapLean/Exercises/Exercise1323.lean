import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Order.Filter.Tendsto
import Mathlib.Topology.Neighborhoods

namespace ProofGap.Exercise1323

noncomputable section
open Filter
open scoped Topology

def punctured (x₀ : ℝ) := nhdsWithin x₀ ({x₀} : Set ℝ)ᶜ
def cot (x : ℝ) := 1 / Real.tan x
def sec (x : ℝ) := 1 / Real.cos x
def original (x : ℝ) := (x * cot x - 1) / x ^ 2
def rewritten (x : ℝ) := (x - Real.tan x) / (x ^ 2 * Real.tan x)
def derivativeStage (x : ℝ) :=
  (1 - sec x ^ 2) / (2 * x * Real.tan x + x ^ 2 * sec x ^ 2)
def normalized (x : ℝ) :=
  -(1 / (x ^ 2 + 2 * (x / Real.tan x) + (x / Real.tan x) ^ 2))

private theorem ratio_tan_limit :
    Tendsto (fun x : ℝ => x / Real.tan x) (punctured 0) (nhds 1) := by
  have hxne : ∀ᶠ x : ℝ in punctured 0, (fun x : ℝ => x) x ≠ 0 := by
    unfold punctured
    filter_upwards [self_mem_nhdsWithin] with x hx
    simpa using hx
  have hsinc0 :
      Tendsto Real.sinc (nhds (0 : ℝ)) (nhds (Real.sinc 0)) :=
    Real.continuous_sinc.continuousAt
  have hsinc1 : Tendsto Real.sinc (nhds (0 : ℝ)) (nhds 1) := by
    simpa [Real.sinc] using hsinc0
  have hsincP : Tendsto Real.sinc (punctured 0) (nhds 1) :=
    hsinc1.mono_left inf_le_left
  have hs : Tendsto (fun x : ℝ => Real.sin x / x)
      (punctured 0) (nhds 1) := by
    apply hsincP.congr'
    filter_upwards [hxne] with x hx
    simp [Real.sinc, hx]
  have hsin : ∀ᶠ x : ℝ in punctured 0, Real.sin x ≠ 0 := by
    have hpos : ∀ᶠ y : ℝ in nhds 1, 0 < y :=
      eventually_gt_nhds (by norm_num : (0 : ℝ) < 1)
    have hpos' := hs.eventually hpos
    filter_upwards [hpos'] with x hx
    exact (div_ne_zero_iff.mp (ne_of_gt hx)).1
  have hc0 :
      Tendsto Real.cos (nhds (0 : ℝ)) (nhds (Real.cos 0)) :=
    Real.continuous_cos.continuousAt
  have hc1 : Tendsto Real.cos (nhds (0 : ℝ)) (nhds 1) := by
    simpa only [Real.cos_zero] using hc0
  have hc : Tendsto Real.cos (punctured 0) (nhds 1) :=
    hc1.mono_left inf_le_left
  have hcos : ∀ᶠ x : ℝ in punctured 0, Real.cos x ≠ 0 := by
    have hpos : ∀ᶠ y : ℝ in nhds 1, 0 < y :=
      eventually_gt_nhds (by norm_num : (0 : ℝ) < 1)
    have hpos' := hc.eventually hpos
    filter_upwards [hpos'] with x hx
    exact ne_of_gt hx
  have hxi : Tendsto (fun x : ℝ => x / Real.sin x)
      (punctured 0) (nhds 1) := by
    simpa only [inv_div, inv_one] using
      hs.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  have hprod : Tendsto (fun x : ℝ => (x / Real.sin x) * Real.cos x)
      (punctured 0) (nhds 1) := by
    simpa using hxi.mul hc
  have hrewrite :
      (fun x : ℝ => (x / Real.sin x) * Real.cos x) =ᶠ[punctured 0]
        (fun x : ℝ => x / Real.tan x) := by
    filter_upwards [hsin, hcos] with x hsinx hcosx
    rw [Real.tan_eq_sin_div_cos]
    field_simp [hsinx, hcosx] <;> ring
  exact hprod.congr' hrewrite

private theorem denominator_limit :
    Tendsto
      (fun x : ℝ => x ^ 2 + 2 * (x / Real.tan x) + (x / Real.tan x) ^ 2)
      (punctured 0) (nhds 3) := by
  have hx : Tendsto (fun x : ℝ => x) (punctured 0) (nhds 0) :=
    tendsto_id.mono_left inf_le_left
  have hr := ratio_tan_limit
  have htwo : Tendsto (fun _ : ℝ => (2 : ℝ)) (punctured 0) (nhds 2) :=
    tendsto_const_nhds
  convert (hx.pow 2).add ((htwo.mul hr).add (hr.pow 2)) using 1 <;>
    norm_num [add_assoc]

private theorem normalized_limit :
    Tendsto normalized (punctured 0) (nhds (-1 / 3 : ℝ)) := by
  have hone : Tendsto (fun _ : ℝ => (1 : ℝ)) (punctured 0) (nhds 1) :=
    tendsto_const_nhds
  have hq : Tendsto
      (fun x : ℝ => (1 : ℝ) /
        (x ^ 2 + 2 * (x / Real.tan x) + (x / Real.tan x) ^ 2))
      (punctured 0) (nhds ((1 : ℝ) / 3)) := by
    exact hone.div denominator_limit (by norm_num)
  change Tendsto
    (fun x : ℝ => -((1 : ℝ) /
      (x ^ 2 + 2 * (x / Real.tan x) + (x / Real.tan x) ^ 2)))
    (punctured 0) (nhds (-1 / 3 : ℝ))
  convert hq.neg using 1 <;> norm_num

private theorem eventually_normalized_denominator_ne_zero :
    ∀ᶠ x : ℝ in punctured 0,
      x ^ 2 + 2 * (x / Real.tan x) + (x / Real.tan x) ^ 2 ≠ 0 := by
  have hpos : ∀ᶠ y : ℝ in nhds 3, 0 < y :=
    eventually_gt_nhds (by norm_num : (0 : ℝ) < 3)
  have hpos' := denominator_limit.eventually hpos
  filter_upwards [hpos'] with x hx
  exact ne_of_gt hx

private theorem eventually_tan_ne_zero :
    ∀ᶠ x : ℝ in punctured 0, Real.tan x ≠ 0 := by
  have hpos : ∀ᶠ y : ℝ in nhds 1, 0 < y :=
    eventually_gt_nhds (by norm_num : (0 : ℝ) < 1)
  have hpos' := ratio_tan_limit.eventually hpos
  filter_upwards [hpos'] with x hx
  exact (div_ne_zero_iff.mp (ne_of_gt hx)).2

private theorem eventually_cos_ne_zero :
    ∀ᶠ x : ℝ in nhds 0, Real.cos x ≠ 0 := by
  have hc0 : ContinuousAt Real.cos (0 : ℝ) :=
    Real.continuous_cos.continuousAt
  have hc : Tendsto Real.cos (nhds 0) (nhds 1) := by
    simpa only [ContinuousAt, Real.cos_zero] using hc0
  have hpos : ∀ᶠ y : ℝ in nhds 1, 0 < y :=
    eventually_gt_nhds (by norm_num : (0 : ℝ) < 1)
  have hpos' := hc.eventually hpos
  filter_upwards [hpos'] with x hx
  exact ne_of_gt hx

private theorem derivative_eventually_eq_normalized :
    derivativeStage =ᶠ[punctured 0] normalized := by
  filter_upwards [eventually_tan_ne_zero,
    eventually_normalized_denominator_ne_zero] with x htan hnorm
  have hcos : Real.cos x ≠ 0 := by
    intro hcos
    apply htan
    rw [Real.tan_eq_sin_div_cos, hcos, div_zero]
  have hsec : sec x ^ 2 = 1 + Real.tan x ^ 2 := by
    unfold sec
    rw [Real.tan_eq_sin_div_cos]
    field_simp [hcos]
    nlinarith [Real.sin_sq_add_cos_sq x]
  have hnum : 1 - sec x ^ 2 = -(Real.tan x ^ 2) := by
    rw [hsec]
    ring
  have hden :
      2 * x * Real.tan x + x ^ 2 * sec x ^ 2 =
        Real.tan x ^ 2 *
          (x ^ 2 + 2 * (x / Real.tan x) + (x / Real.tan x) ^ 2) := by
    rw [hsec]
    field_simp [htan]
    ring
  unfold derivativeStage normalized
  rw [hnum, hden]
  field_simp [htan, hnorm]

private theorem derivative_limit :
    Tendsto derivativeStage (punctured 0) (nhds (-1 / 3 : ℝ)) := by
  exact normalized_limit.congr' derivative_eventually_eq_normalized.symm

private theorem derivative_denominator_ne_zero :
    ∀ᶠ x : ℝ in punctured 0,
      2 * x * Real.tan x + x ^ 2 * sec x ^ 2 ≠ 0 := by
  filter_upwards [eventually_tan_ne_zero,
    eventually_normalized_denominator_ne_zero] with x htan hnorm
  have hcos : Real.cos x ≠ 0 := by
    intro hcos
    apply htan
    rw [Real.tan_eq_sin_div_cos, hcos, div_zero]
  have hsec : sec x ^ 2 = 1 + Real.tan x ^ 2 := by
    unfold sec
    rw [Real.tan_eq_sin_div_cos]
    field_simp [hcos]
    nlinarith [Real.sin_sq_add_cos_sq x]
  have hden :
      2 * x * Real.tan x + x ^ 2 * sec x ^ 2 =
        Real.tan x ^ 2 *
          (x ^ 2 + 2 * (x / Real.tan x) + (x / Real.tan x) ^ 2) := by
    rw [hsec]
    field_simp [htan]
    ring
  rw [hden]
  exact mul_ne_zero (pow_ne_zero 2 htan) hnorm

private theorem rewritten_limit :
    Tendsto rewritten (punctured 0) (nhds (-1 / 3 : ℝ)) := by
  have ht0 : Tendsto Real.tan (nhds 0) (nhds 0) := by
    simpa only [ContinuousAt, Real.tan_zero] using
      (Real.hasDerivAt_tan (by norm_num : Real.cos 0 ≠ 0)).continuousAt
  have hx : Tendsto (fun x : ℝ => x) (nhds 0) (nhds 0) :=
    tendsto_id
  have hnum : Tendsto (fun x : ℝ => x - Real.tan x)
      (nhds 0) (nhds 0) := by
    simpa using hx.sub ht0
  have hden : Tendsto (fun x : ℝ => x ^ 2 * Real.tan x)
      (nhds 0) (nhds 0) := by
    simpa using (hx.pow 2).mul ht0
  have hf : ∀ᶠ x : ℝ in nhds 0,
      HasDerivAt (fun y : ℝ => y - Real.tan y) (1 - sec x ^ 2) x := by
    filter_upwards [eventually_cos_ne_zero] with x hcos
    simpa [sec, one_div, pow_two] using
      (hasDerivAt_id x).sub (Real.hasDerivAt_tan hcos)
  have hg : ∀ᶠ x : ℝ in nhds 0,
      HasDerivAt (fun y : ℝ => y ^ 2 * Real.tan y)
        (2 * x * Real.tan x + x ^ 2 * sec x ^ 2) x := by
    filter_upwards [eventually_cos_ne_zero] with x hcos
    convert ((hasDerivAt_id x).pow 2).mul (Real.hasDerivAt_tan hcos) using 1 <;>
      simp [sec, one_div, pow_two] <;> ring
  have hgt_le : 𝓝[>] (0 : ℝ) ≤ punctured 0 := by
    unfold punctured
    apply nhdsWithin_mono
    intro x hx
    simp only [Set.mem_Ioi] at hx
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    exact ne_of_gt hx
  have hlt_le : 𝓝[<] (0 : ℝ) ≤ punctured 0 := by
    unfold punctured
    apply nhdsWithin_mono
    intro x hx
    simp only [Set.mem_Iio] at hx
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    exact ne_of_lt hx
  have hright : Tendsto rewritten (𝓝[>] (0 : ℝ))
      (nhds (-1 / 3 : ℝ)) := by
    have hf' : ∀ᶠ x : ℝ in 𝓝[>] (0 : ℝ),
        HasDerivAt (fun y : ℝ => y - Real.tan y) (1 - sec x ^ 2) x :=
      hf.filter_mono inf_le_left
    have hg' : ∀ᶠ x : ℝ in 𝓝[>] (0 : ℝ),
        HasDerivAt (fun y : ℝ => y ^ 2 * Real.tan y)
          (2 * x * Real.tan x + x ^ 2 * sec x ^ 2) x :=
      hg.filter_mono inf_le_left
    have hnum' : Tendsto (fun x : ℝ => x - Real.tan x)
        (𝓝[>] (0 : ℝ)) (nhds 0) :=
      hnum.mono_left inf_le_left
    have hden' : Tendsto (fun x : ℝ => x ^ 2 * Real.tan x)
        (𝓝[>] (0 : ℝ)) (nhds 0) :=
      hden.mono_left inf_le_left
    have hderiv_ne := derivative_denominator_ne_zero.filter_mono hgt_le
    have hderiv_lim := derivative_limit.mono_left hgt_le
    simpa [rewritten] using
      HasDerivAt.lhopital_zero_nhdsGT hf' hg' hderiv_ne
        hnum' hden' hderiv_lim
  have hleft : Tendsto rewritten (𝓝[<] (0 : ℝ))
      (nhds (-1 / 3 : ℝ)) := by
    have hf' : ∀ᶠ x : ℝ in 𝓝[<] (0 : ℝ),
        HasDerivAt (fun y : ℝ => y - Real.tan y) (1 - sec x ^ 2) x :=
      hf.filter_mono inf_le_left
    have hg' : ∀ᶠ x : ℝ in 𝓝[<] (0 : ℝ),
        HasDerivAt (fun y : ℝ => y ^ 2 * Real.tan y)
          (2 * x * Real.tan x + x ^ 2 * sec x ^ 2) x :=
      hg.filter_mono inf_le_left
    have hnum' : Tendsto (fun x : ℝ => x - Real.tan x)
        (𝓝[<] (0 : ℝ)) (nhds 0) :=
      hnum.mono_left inf_le_left
    have hden' : Tendsto (fun x : ℝ => x ^ 2 * Real.tan x)
        (𝓝[<] (0 : ℝ)) (nhds 0) :=
      hden.mono_left inf_le_left
    have hderiv_ne := derivative_denominator_ne_zero.filter_mono hlt_le
    have hderiv_lim := derivative_limit.mono_left hlt_le
    simpa [rewritten] using
      HasDerivAt.lhopital_zero_nhdsLT hf' hg' hderiv_ne
        hnum' hden' hderiv_lim
  have hsets : ({0} : Set ℝ)ᶜ = Set.Iio 0 ∪ Set.Ioi 0 := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff,
      Set.mem_union, Set.mem_Iio, Set.mem_Ioi]
    constructor
    · exact lt_or_gt_of_ne
    · intro h
      exact h.elim ne_of_lt ne_of_gt
  have hsplit : punctured 0 = 𝓝[<] (0 : ℝ) ⊔ 𝓝[>] (0 : ℝ) := by
    unfold punctured
    rw [hsets, nhdsWithin_union]
  rw [hsplit]
  change Filter.map rewritten (𝓝[<] (0 : ℝ) ⊔ 𝓝[>] (0 : ℝ)) ≤
    nhds (-1 / 3 : ℝ)
  rw [Filter.map_sup]
  exact sup_le hleft hright

private theorem original_eventually_eq_rewritten :
    original =ᶠ[punctured 0] rewritten := by
  filter_upwards [eventually_tan_ne_zero] with x htan
  have hx : x ≠ 0 := by
    intro hx
    subst x
    norm_num at htan
  unfold original rewritten cot
  field_simp [hx, htan]

private theorem original_limit :
    Tendsto original (punctured 0) (nhds (-1 / 3 : ℝ)) := by
  exact rewritten_limit.congr' original_eventually_eq_rewritten.symm

theorem gap1 : Tendsto original (punctured 0) (nhds (-1 / 3 : ℝ)) := by
  simpa using original_limit
theorem gap2 : Tendsto rewritten (punctured 0) (nhds (-1 / 3 : ℝ)) := by
  simpa using rewritten_limit
theorem gap3 : Tendsto derivativeStage (punctured 0) (nhds (-1 / 3 : ℝ)) := by
  simpa using derivative_limit
theorem gap4 : Tendsto original (punctured 0) (nhds (-1 / 3 : ℝ)) := by
  exact gap1
theorem gap5 : Tendsto normalized (punctured 0) (nhds (-1 / 3 : ℝ)) := by
  simpa using normalized_limit
theorem gap6 : Tendsto normalized (punctured 0) (nhds (-1 / 3 : ℝ)) := by
  exact gap5
theorem gap7 : Tendsto original (punctured 0) (nhds (-1 / 3 : ℝ)) := by
  exact gap1

end
end ProofGap.Exercise1323
