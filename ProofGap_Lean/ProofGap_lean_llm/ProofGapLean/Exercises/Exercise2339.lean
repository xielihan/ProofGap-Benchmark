import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace ProofGap.Exercise2339
noncomputable section

open Filter MeasureTheory
open scoped Interval

def integrand (x : ℝ) : ℝ := 1 / (x ^ 2 + x + 1) ^ 2

def primitive (x : ℝ) : ℝ :=
  (2 * x + 1) / (3 * (x ^ 2 + x + 1)) +
    4 / (3 * Real.sqrt 3) * Real.arctan ((2 * x + 1) / Real.sqrt 3)

def Antiderivatives : Set (ℝ → ℝ) :=
  {F | ∀ x, HasDerivAt F (integrand x) x}

def PrimitiveFamily : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x, F x = primitive x + C}

def HasTwoSidedImproperValue (L : ℝ) : Prop :=
  ∃ l r : ℝ,
    Tendsto (fun a => ∫ x in a..0, integrand x) atBot (nhds l) ∧
    Tendsto (fun b => ∫ x in (0 : ℝ)..b, integrand x) atTop (nhds r) ∧
    l + r = L

private theorem quadratic_pos (x : ℝ) : 0 < x ^ 2 + x + 1 := by
  nlinarith [sq_nonneg (2 * x + 1)]

private theorem primitive_hasDerivAt (x : ℝ) : HasDerivAt primitive (integrand x) x := by
  have hq : HasDerivAt (fun y : ℝ => y ^ 2 + y + 1) (2 * x + 1) x := by
    convert (((hasDerivAt_id x).pow 2).add (hasDerivAt_id x)).add_const 1 using 1 <;>
      simp [id] <;> ring
  have hnum : HasDerivAt (fun y : ℝ => 2 * y + 1) 2 x := by
    convert ((hasDerivAt_id x).const_mul 2).add_const 1 using 1 <;> simp <;> ring
  have hq0 : x ^ 2 + x + 1 ≠ 0 := (quadratic_pos x).ne'
  have hq0' : x * (x + 1) + 1 ≠ 0 := by
    convert hq0 using 1 <;> ring
  have hsqrt : Real.sqrt 3 ≠ 0 := Real.sqrt_ne_zero'.2 (by norm_num)
  have hatan : 1 + ((2 * x + 1) / Real.sqrt 3) ^ 2 ≠ 0 := by positivity
  have hfirst := hnum.div (hq.const_mul 3) (mul_ne_zero (by norm_num) hq0)
  have harg := hnum.div_const (Real.sqrt 3)
  have hsecond := (harg.arctan).const_mul (4 / (3 * Real.sqrt 3))
  unfold primitive integrand
  convert hfirst.add hsecond using 1
  field_simp [hq0, hsqrt, hatan]
  field_simp [hq0']
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  ring

private theorem integrand_continuous : Continuous integrand := by
  unfold integrand
  apply continuous_const.div
  · fun_prop
  · intro x
    exact pow_ne_zero 2 (quadratic_pos x).ne'

private theorem interval_integral_eq_primitive_sub (a b : ℝ) :
    (∫ x in a..b, integrand x) = primitive b - primitive a := by
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => primitive_hasDerivAt x)
    integrand_continuous.continuousOn.intervalIntegrable

private theorem rational_tendsto_zero {l : Filter ℝ}
    (hinv : Tendsto (fun x : ℝ => x⁻¹) l (nhds 0))
    (hne : ∀ᶠ x : ℝ in l, x ≠ 0) :
    Tendsto (fun x : ℝ => (2 * x + 1) / (3 * (x ^ 2 + x + 1))) l (nhds 0) := by
  have hnum : Tendsto (fun x : ℝ => 2 * x⁻¹ + (x⁻¹) ^ 2) l (nhds 0) := by
    simpa using
      ((tendsto_const_nhds : Tendsto (fun _ : ℝ => (2 : ℝ)) l (nhds 2)).mul hinv).add
        (hinv.pow 2)
  have hone : Tendsto (fun x : ℝ => 1 + x⁻¹ + (x⁻¹) ^ 2) l (nhds 1) := by
    simpa using
      ((tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ)) l (nhds 1)).add hinv).add
        (hinv.pow 2)
  have hden : Tendsto (fun x : ℝ => 3 * (1 + x⁻¹ + (x⁻¹) ^ 2)) l (nhds 3) := by
    simpa using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => (3 : ℝ)) l (nhds 3)).mul hone
  have hquot : Tendsto (fun x : ℝ =>
      (2 * x⁻¹ + (x⁻¹) ^ 2) / (3 * (1 + x⁻¹ + (x⁻¹) ^ 2))) l (nhds 0) := by
    simpa using hnum.div hden (by norm_num : (3 : ℝ) ≠ 0)
  apply hquot.congr'
  filter_upwards [hne] with x hx
  field_simp [hx]

private theorem primitive_tendsto_atTop :
    Tendsto primitive atTop (nhds (2 * Real.pi / (3 * Real.sqrt 3))) := by
  have hne : ∀ᶠ x : ℝ in atTop, x ≠ 0 :=
    (eventually_gt_atTop 0).mono fun x hx => hx.ne'
  have hr := rational_tendsto_zero tendsto_inv_atTop_zero hne
  have hlin : Tendsto (fun x : ℝ => 2 * x + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1
      (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2))
  have harg : Tendsto (fun x : ℝ => (2 * x + 1) / Real.sqrt 3) atTop atTop :=
    hlin.atTop_div_const (Real.sqrt_pos.2 (by norm_num))
  have hatan : Tendsto (fun x : ℝ => Real.arctan ((2 * x + 1) / Real.sqrt 3))
      atTop (nhds (Real.pi / 2)) :=
    (tendsto_nhdsWithin_iff.mp Real.tendsto_arctan_atTop).1.comp harg
  unfold primitive
  convert hr.add (tendsto_const_nhds.mul hatan) using 1 <;>
    field_simp [Real.sqrt_ne_zero'.2 (by norm_num : (0 : ℝ) < 3)] <;> ring

private theorem primitive_tendsto_atBot :
    Tendsto primitive atBot (nhds (-(2 * Real.pi / (3 * Real.sqrt 3)))) := by
  have hne : ∀ᶠ x : ℝ in atBot, x ≠ 0 :=
    (eventually_lt_atBot 0).mono fun x hx => hx.ne
  have hr := rational_tendsto_zero tendsto_inv_atBot_zero hne
  have hlin : Tendsto (fun x : ℝ => 2 * x + 1) atBot atBot :=
    tendsto_atBot_add_const_right atBot 1
      (tendsto_id.const_mul_atBot (by norm_num : (0 : ℝ) < 2))
  have harg : Tendsto (fun x : ℝ => (2 * x + 1) / Real.sqrt 3) atBot atBot :=
    hlin.atBot_div_const (Real.sqrt_pos.2 (by norm_num))
  have hatan : Tendsto (fun x : ℝ => Real.arctan ((2 * x + 1) / Real.sqrt 3))
      atBot (nhds (-(Real.pi / 2))) :=
    (tendsto_nhdsWithin_iff.mp Real.tendsto_arctan_atBot).1.comp harg
  unfold primitive
  convert hr.add (tendsto_const_nhds.mul hatan) using 1 <;>
    field_simp [Real.sqrt_ne_zero'.2 (by norm_num : (0 : ℝ) < 3)] <;> ring

private theorem integrand_integrable : Integrable integrand := by
  have hg : Integrable (fun x : ℝ => 16 * (1 + x ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul 16
  apply hg.mono' integrand_continuous.aestronglyMeasurable
  filter_upwards with x
  have hA : 0 < 1 + x ^ 2 := by positivity
  have hq : 0 < x ^ 2 + x + 1 := quadratic_pos x
  have hqbound : (1 + x ^ 2) / 4 ≤ x ^ 2 + x + 1 := by
    nlinarith [sq_nonneg (3 * x + 2)]
  have hsq :=
    mul_self_le_mul_self (by positivity : 0 ≤ (1 + x ^ 2) / 4) hqbound
  have hcross : 1 + x ^ 2 ≤ 16 * (x ^ 2 + x + 1) ^ 2 := by
    nlinarith [sq_nonneg x]
  rw [show integrand x = 1 / (x ^ 2 + x + 1) ^ 2 by rfl,
    Real.norm_eq_abs, abs_of_nonneg (one_div_nonneg.mpr (sq_nonneg _)),
    show 16 * (1 + x ^ 2)⁻¹ = 16 / (1 + x ^ 2) by simp [div_eq_mul_inv],
    div_le_div_iff₀ (sq_pos_of_pos hq) hA]
  simpa using hcross

theorem gap1 : Antiderivatives = PrimitiveFamily := by
  ext F
  simp only [Antiderivatives, PrimitiveFamily, Set.mem_setOf_eq]
  constructor
  · intro hF
    have hFdiff : Differentiable ℝ F := fun x => (hF x).differentiableAt
    have hpdiff : Differentiable ℝ primitive :=
      fun x => (primitive_hasDerivAt x).differentiableAt
    have hdiff : Differentiable ℝ (fun x => F x - primitive x) := hFdiff.sub hpdiff
    have hzero : ∀ x, deriv (fun y => F y - primitive y) x = 0 := by
      intro x
      simpa using ((hF x).sub (primitive_hasDerivAt x)).deriv
    refine ⟨F 0 - primitive 0, fun x => ?_⟩
    have hc := is_const_of_deriv_eq_zero hdiff hzero x 0
    linarith
  · rintro ⟨C, hC⟩
    have hfun : F = fun x => primitive x + C := funext hC
    subst F
    intro x
    simpa using (primitive_hasDerivAt x).add_const C

theorem gap2 :
    HasTwoSidedImproperValue (4 * Real.pi / (3 * Real.sqrt 3)) := by
  refine ⟨primitive 0 + 2 * Real.pi / (3 * Real.sqrt 3),
    2 * Real.pi / (3 * Real.sqrt 3) - primitive 0, ?_, ?_, by ring⟩
  · have hlim : Tendsto (fun a => primitive 0 - primitive a) atBot
        (nhds (primitive 0 + 2 * Real.pi / (3 * Real.sqrt 3))) := by
      convert tendsto_const_nhds.sub primitive_tendsto_atBot using 1 <;> ring
    apply hlim.congr'
    filter_upwards with a
    exact (interval_integral_eq_primitive_sub a 0).symm
  · have hlim : Tendsto (fun b => primitive b - primitive 0) atTop
        (nhds (2 * Real.pi / (3 * Real.sqrt 3) - primitive 0)) := by
      convert primitive_tendsto_atTop.sub tendsto_const_nhds using 1 <;> ring
    apply hlim.congr'
    filter_upwards with b
    exact (interval_integral_eq_primitive_sub 0 b).symm

theorem gap3 :
    (∫ x : ℝ, integrand x) = 4 * Real.pi / (3 * Real.sqrt 3) := by
  have h := MeasureTheory.integral_of_hasDerivAt_of_tendsto
    primitive_hasDerivAt integrand_integrable primitive_tendsto_atBot primitive_tendsto_atTop
  convert h using 1 <;> ring

end
end ProofGap.Exercise2339
