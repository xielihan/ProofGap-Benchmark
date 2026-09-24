import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace ProofGap.Exercise2342
noncomputable section

open Filter MeasureTheory
open scoped Interval

def substitution (t : ℝ) : ℝ := 1 - t ^ 2
def integrand (x : ℝ) : ℝ := 1 / ((2 - x) * Real.sqrt (1 - x))
def transformedIntegrand (t : ℝ) : ℝ := -2 / (1 + t ^ 2)
def primitive (x : ℝ) : ℝ := -2 * Real.arctan (Real.sqrt (1 - x))
def transformedPrimitive (t : ℝ) : ℝ := -2 * Real.arctan t

def FamilyOn (s : Set ℝ) (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ s, HasDerivAt F (f x) x}

def TranslatesOn (s : Set ℝ) (P : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ s, F x = P x + C}

def HasImproperValue (L : ℝ) : Prop :=
  Tendsto (fun ε => ∫ x in (0 : ℝ)..(1 - ε), integrand x)
    (nhdsWithin 0 (Set.Ioi 0)) (nhds L)

private theorem transformedPrimitive_hasDerivAt (t : ℝ) :
    HasDerivAt transformedPrimitive (transformedIntegrand t) t := by
  unfold transformedPrimitive transformedIntegrand
  convert (Real.hasDerivAt_arctan t).const_mul (-2) using 1 <;> ring

private theorem primitive_hasDerivAt (x : ℝ) (hx : x < 1) :
    HasDerivAt primitive (integrand x) x := by
  have hpos : 0 < 1 - x := sub_pos.mpr hx
  have hinner : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := by
    convert (hasDerivAt_const x 1).sub (hasDerivAt_id x) using 1 <;> ring
  have hsqrt := hinner.sqrt hpos.ne'
  have hraw := hsqrt.arctan.const_mul (-2)
  have hsqrt0 : Real.sqrt (1 - x) ≠ 0 := (Real.sqrt_pos.2 hpos).ne'
  have hden : 2 - x ≠ 0 := by linarith
  unfold primitive integrand
  convert hraw using 1
  field_simp [hsqrt0, hden]
  rw [Real.sq_sqrt hpos.le]
  field_simp [hden]
  ring

private theorem primitive_continuous : Continuous primitive := by
  unfold primitive
  fun_prop

private theorem integrand_intervalIntegrable :
    IntervalIntegrable integrand volume 0 1 := by
  apply intervalIntegral.intervalIntegrable_deriv_of_nonneg
    primitive_continuous.continuousOn
  · intro x hx
    exact primitive_hasDerivAt x (by simpa using hx.2)
  · intro x hx
    have hxlt : x < 1 := by simpa using hx.2
    have htwo : 0 < 2 - x := by linarith
    have hsqrt : 0 < Real.sqrt (1 - x) := Real.sqrt_pos.2 (sub_pos.mpr hxlt)
    unfold integrand
    exact one_div_nonneg.mpr (mul_nonneg htwo.le hsqrt.le)

private theorem truncated_eq_primitive (ε : ℝ) (hε : ε ∈ Set.Ioo 0 1) :
    (∫ x in (0 : ℝ)..(1 - ε), integrand x) =
      primitive (1 - ε) - primitive 0 := by
  have hle : 0 ≤ 1 - ε := by linarith [hε.2]
  have hint : IntervalIntegrable integrand volume 0 (1 - ε) := by
    apply integrand_intervalIntegrable.mono_set
    rw [Set.uIcc_of_le hle, Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    intro x hx
    constructor <;> linarith [hx.1, hx.2, hε.1]
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x hx
    rw [Set.uIcc_of_le hle] at hx
    exact primitive_hasDerivAt x (by linarith [hx.2, hε.1])
  · exact hint

theorem gap1 (x t : ℝ) (hx : x ≤ 1)
    (ht : Real.sqrt (1 - x) = t) :
    x = 1 - t ^ 2 := by
  have hs := Real.sq_sqrt (sub_nonneg.mpr hx)
  rw [ht] at hs
  linarith

theorem gap2 (t : ℝ) :
    HasDerivAt substitution (-2 * t) t := by
  unfold substitution
  convert (hasDerivAt_const t 1).sub ((hasDerivAt_id t).pow 2) using 1 <;>
    simp [id] <;> ring

theorem gap3 (t : ℝ) :
    2 - substitution t = 1 + t ^ 2 := by
  unfold substitution
  ring

theorem gap4 (t : ℝ) (ht : 0 < t) :
    integrand (substitution t) * (-2 * t) = transformedIntegrand t := by
  have hsqrt : Real.sqrt (1 - substitution t) = t := by
    rw [show 1 - substitution t = t ^ 2 by unfold substitution; ring,
      Real.sqrt_sq_eq_abs, abs_of_pos ht]
  unfold integrand transformedIntegrand
  rw [hsqrt, gap3]
  field_simp [ht.ne']

theorem gap5 :
    FamilyOn Set.univ transformedIntegrand =
      TranslatesOn Set.univ transformedPrimitive := by
  ext F
  simp only [FamilyOn, TranslatesOn, Set.mem_setOf_eq]
  constructor
  · intro hF
    have hFall : ∀ x, HasDerivAt F (transformedIntegrand x) x :=
      fun x => hF x (Set.mem_univ x)
    have hFdiff : Differentiable ℝ F := fun x => (hFall x).differentiableAt
    have hpdiff : Differentiable ℝ transformedPrimitive :=
      fun x => (transformedPrimitive_hasDerivAt x).differentiableAt
    have hdiff : Differentiable ℝ (fun x => F x - transformedPrimitive x) :=
      hFdiff.sub hpdiff
    have hzero : ∀ x, deriv (fun y => F y - transformedPrimitive y) x = 0 := by
      intro x
      simpa using ((hFall x).sub (transformedPrimitive_hasDerivAt x)).deriv
    refine ⟨F 0 - transformedPrimitive 0, fun x _ => ?_⟩
    have hc := is_const_of_deriv_eq_zero hdiff hzero x 0
    linarith
  · rintro ⟨C, hC⟩
    have hfun : F = fun x => transformedPrimitive x + C :=
      funext fun x => hC x (Set.mem_univ x)
    subst F
    intro x _
    simpa using (transformedPrimitive_hasDerivAt x).add_const C

theorem gap6 :
    TranslatesOn Set.univ transformedPrimitive =
      {F | ∃ C : ℝ, ∀ t, F t = -2 * Real.arctan t + C} := by
  ext F
  simp [TranslatesOn, transformedPrimitive]

theorem gap7 :
    FamilyOn (Set.Iio 1) integrand =
      TranslatesOn (Set.Iio 1) primitive := by
  ext F
  simp only [FamilyOn, TranslatesOn, Set.mem_setOf_eq]
  constructor
  · intro hF
    have hFdiff : DifferentiableOn ℝ F (Set.Iio 1) :=
      fun x hx => (hF x hx).differentiableAt.differentiableWithinAt
    have hpdiff : DifferentiableOn ℝ primitive (Set.Iio 1) :=
      fun x hx => (primitive_hasDerivAt x hx).differentiableAt.differentiableWithinAt
    have hderiv : Set.EqOn (deriv F) (deriv primitive) (Set.Iio 1) :=
      fun x hx => by rw [(hF x hx).deriv, (primitive_hasDerivAt x hx).deriv]
    exact isOpen_Iio.exists_eq_add_of_deriv_eq
      (convex_Iio 1).isPreconnected hFdiff hpdiff hderiv
  · rintro ⟨C, hC⟩
    intro x hx
    have heq : F =ᶠ[nhds x] fun y => primitive y + C := by
      filter_upwards [isOpen_Iio.mem_nhds hx] with y hy
      exact hC y hy
    exact ((primitive_hasDerivAt x hx).add_const C).congr_of_eventuallyEq heq

theorem gap8 :
    FamilyOn (Set.Iio 1) integrand =
      TranslatesOn (Set.Iio 1) primitive := gap7

theorem gap9 :
    HasImproperValue (Real.pi / 2) ↔
      Tendsto (fun ε => primitive (1 - ε) - primitive 0)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (Real.pi / 2)) := by
  unfold HasImproperValue
  have heq : (fun ε : ℝ => ∫ x in (0 : ℝ)..(1 - ε), integrand x) =ᶠ[
      nhdsWithin 0 (Set.Ioi 0)] (fun ε => primitive (1 - ε) - primitive 0) := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
    exact truncated_eq_primitive ε hε
  constructor
  · exact fun h => h.congr' heq
  · exact fun h => h.congr' heq.symm

theorem gap10 :
    Tendsto (fun ε => primitive (1 - ε) - primitive 0)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (Real.pi / 2)) := by
  have hid : Tendsto (fun ε : ℝ => ε) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have harg : Tendsto (fun ε : ℝ => 1 - ε) (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    simpa using tendsto_const_nhds.sub hid
  have hp : Tendsto (fun ε : ℝ => primitive (1 - ε))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (primitive 1)) :=
    primitive_continuous.continuousAt.tendsto.comp harg
  have hc : Tendsto (fun _ : ℝ => primitive 0) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (primitive 0)) := tendsto_const_nhds
  convert hp.sub hc using 1 <;> simp [primitive] <;> ring

theorem gap11 : HasImproperValue (Real.pi / 2) := by
  exact gap9.mpr gap10

theorem gap12 :
    (∫ x in (0 : ℝ)..1, integrand x) = Real.pi / 2 := by
  have hcalc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (f := primitive) (f' := integrand) (by norm_num : (0 : ℝ) ≤ 1)
    primitive_continuous.continuousOn
    (fun x hx => primitive_hasDerivAt x hx.2) integrand_intervalIntegrable
  convert hcalc using 1 <;> simp [primitive] <;> ring

end
end ProofGap.Exercise2342
