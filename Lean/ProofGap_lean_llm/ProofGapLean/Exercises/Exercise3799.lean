import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Data.Real.Sign
import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3799

noncomputable section

open Filter MeasureTheory Set
open scoped Interval Topology

def integrand (α x : ℝ) : ℝ :=
  Real.arctan (α * x) / (x ^ 2 * Real.sqrt (x ^ 2 - 1))

def I (α : ℝ) : ℝ :=
  ∫ x in Set.Ioi (1 : ℝ), integrand α x

def transformedDerivative (α t : ℝ) : ℝ :=
  t ^ 2 / (Real.sqrt (1 - t ^ 2) * (t ^ 2 + α ^ 2))

def positiveDerivative (α : ℝ) : ℝ :=
  Real.pi / 2 -
    α * Real.pi / (2 * Real.sqrt (1 + α ^ 2))

def PositivePrimitiveFamily : Set (ℝ → ℝ) :=
  {G | ∀ α : ℝ, 0 < α → HasDerivAt G (positiveDerivative α) α}

def PositiveClosedFormFamily : Set (ℝ → ℝ) :=
  {G | ∃ C : ℝ, ∀ α : ℝ, 0 < α →
    G α = Real.pi / 2 * α -
      Real.pi / 2 * Real.sqrt (1 + α ^ 2) + C}

private def paramKernel (a x : ℝ) : ℝ :=
  Real.arctan (a * x) / (x ^ 2 * Real.sqrt (x ^ 2 - 1))

private def derivativeKernel (a x : ℝ) : ℝ :=
  1 / (x * Real.sqrt (x ^ 2 - 1) * (1 + a ^ 2 * x ^ 2))

private def integralValue (a : ℝ) : ℝ :=
  ∫ x in Ioi (1 : ℝ), paramKernel a x ∂volume

private def ratio (a : ℝ) : ℝ :=
  |a| / Real.sqrt (1 + a ^ 2)

private def derivativePrimitive (a x : ℝ) : ℝ :=
  Real.arctan (Real.sqrt (x ^ 2 - 1)) -
    ratio a *
      Real.arctan (ratio a * Real.sqrt (x ^ 2 - 1))

private theorem ratio_sq_mul (a : ℝ) :
    ratio a ^ 2 * (1 + a ^ 2) = a ^ 2 := by
  have hs : Real.sqrt (1 + a ^ 2) ≠ 0 := by positivity
  unfold ratio
  rw [div_pow, sq_abs, Real.sq_sqrt (by positivity)]
  field_simp [hs]

private theorem continuous_derivativePrimitive (a : ℝ) :
    Continuous (derivativePrimitive a) := by
  unfold derivativePrimitive
  fun_prop

private theorem derivativePrimitive_hasDerivAt
    (a x : ℝ) (hx : 1 < x) :
    HasDerivAt (derivativePrimitive a) (derivativeKernel a x) x := by
  have hrad : 0 < x ^ 2 - 1 := by nlinarith
  have hrpos : 0 < Real.sqrt (x ^ 2 - 1) :=
    Real.sqrt_pos.2 hrad
  have hrSq :
      Real.sqrt (x ^ 2 - 1) ^ 2 = x ^ 2 - 1 :=
    Real.sq_sqrt hrad.le
  have hr :
      HasDerivAt (fun y : ℝ => Real.sqrt (y ^ 2 - 1))
        (x / Real.sqrt (x ^ 2 - 1)) x := by
    have hinner :
        HasDerivAt (fun y : ℝ => y ^ 2 - 1) (2 * x) x := by
      convert ((hasDerivAt_id x).pow 2).sub_const 1 using 1 <;>
        simp [id] <;> ring
    have h :=
      (Real.hasDerivAt_sqrt hrad.ne').comp x hinner
    convert h using 1
    field_simp [hrpos.ne'] <;> ring
  have hfirst :=
    (Real.hasDerivAt_arctan (Real.sqrt (x ^ 2 - 1))).comp x hr
  have hscaled :
      HasDerivAt
        (fun y : ℝ => ratio a * Real.sqrt (y ^ 2 - 1))
        (ratio a * (x / Real.sqrt (x ^ 2 - 1))) x :=
    hr.const_mul (ratio a)
  have hsecond :=
    (Real.hasDerivAt_arctan
      (ratio a * Real.sqrt (x ^ 2 - 1))).comp x hscaled
  have hprimitive := hfirst.sub (hsecond.const_mul (ratio a))
  have hx0 : x ≠ 0 := ne_of_gt (by linarith)
  have hfactor :
      0 < 1 + a ^ 2 * x ^ 2 := by positivity
  have hratio := ratio_sq_mul a
  have hone :
      1 + Real.sqrt (x ^ 2 - 1) ^ 2 = x ^ 2 := by
    nlinarith
  have honepa : 0 < 1 + a ^ 2 := by positivity
  have hratioDiv :
      ratio a ^ 2 = a ^ 2 / (1 + a ^ 2) :=
    (eq_div_iff honepa.ne').2 hratio
  have hratioDen :
      1 + ratio a ^ 2 * Real.sqrt (x ^ 2 - 1) ^ 2 =
        (1 + a ^ 2 * x ^ 2) / (1 + a ^ 2) := by
    rw [hratioDiv]
    field_simp [honepa.ne']
    nlinarith
  unfold derivativePrimitive derivativeKernel
  convert hprimitive using 1
  rw [hone, mul_pow, hratioDen]
  field_simp [hx0, hrpos.ne', hfactor.ne', honepa.ne']
  nlinarith [hratio]

private theorem derivativePrimitive_tendsto (a : ℝ) :
    Tendsto (derivativePrimitive a) atTop
      (𝓝 (Real.pi / 2 - ratio a * (Real.pi / 2))) := by
  have hsquare :
      Tendsto (fun x : ℝ => x ^ 2) atTop atTop := by
    simpa using
      (tendsto_pow_atTop_atTop_of_one_lt
        (R := ℝ) (by norm_num : 1 < (2 : ℕ)))
  have harg :
      Tendsto (fun x : ℝ => x ^ 2 - 1) atTop atTop := by
    simpa only [sub_eq_add_neg] using
      (Filter.tendsto_atTop_add_const_right atTop (-1) hsquare)
  have hroot :
      Tendsto (fun x : ℝ => Real.sqrt (x ^ 2 - 1))
        atTop atTop :=
    Real.tendsto_sqrt_atTop.comp harg
  have hfirst :
      Tendsto
        (fun x : ℝ => Real.arctan (Real.sqrt (x ^ 2 - 1)))
        atTop (𝓝 (Real.pi / 2)) :=
    tendsto_nhds_of_tendsto_nhdsWithin
      (Real.tendsto_arctan_atTop.comp hroot)
  by_cases ha : a = 0
  · subst a
    have hr0 : ratio 0 = 0 := by
      unfold ratio
      norm_num
    change Tendsto
      (fun x : ℝ =>
        Real.arctan (Real.sqrt (x ^ 2 - 1)) -
          ratio 0 *
            Real.arctan
              (ratio 0 * Real.sqrt (x ^ 2 - 1)))
      atTop
      (𝓝 (Real.pi / 2 - ratio 0 * (Real.pi / 2)))
    rw [hr0]
    simpa using hfirst
  · have hratioPos : 0 < ratio a := by
      unfold ratio
      exact div_pos (abs_pos.mpr ha)
        (Real.sqrt_pos.2 (by positivity))
    have hscaled :
        Tendsto
          (fun x : ℝ =>
            ratio a * Real.sqrt (x ^ 2 - 1)) atTop atTop :=
      hroot.const_mul_atTop hratioPos
    have hsecond :
        Tendsto
          (fun x : ℝ =>
            Real.arctan
              (ratio a * Real.sqrt (x ^ 2 - 1)))
          atTop (𝓝 (Real.pi / 2)) :=
      tendsto_nhds_of_tendsto_nhdsWithin
        (Real.tendsto_arctan_atTop.comp hscaled)
    simpa only [derivativePrimitive] using
      hfirst.sub (tendsto_const_nhds.mul hsecond)

private theorem derivativePrimitive_one (a : ℝ) :
    derivativePrimitive a 1 = 0 := by
  simp [derivativePrimitive]

private theorem derivativeKernel_nonneg
    (a x : ℝ) (hx : x ∈ Ioi (1 : ℝ)) :
    0 ≤ derivativeKernel a x := by
  unfold derivativeKernel
  have hx0 : 0 < x := by
    change (1 : ℝ) < x at hx
    linarith
  have hroot : 0 < Real.sqrt (x ^ 2 - 1) := by
    apply Real.sqrt_pos.2
    change (1 : ℝ) < x at hx
    nlinarith
  positivity

private theorem derivativeKernel_integrable (a : ℝ) :
    IntegrableOn (derivativeKernel a) (Ioi (1 : ℝ)) volume := by
  exact integrableOn_Ioi_deriv_of_nonneg
    (continuous_derivativePrimitive a).continuousAt.continuousWithinAt
    (fun x hx => derivativePrimitive_hasDerivAt a x hx)
    (derivativeKernel_nonneg a)
    (derivativePrimitive_tendsto a)

private theorem derivativeKernel_integral (a : ℝ) :
    (∫ x in Ioi (1 : ℝ), derivativeKernel a x ∂volume) =
      Real.pi / 2 - ratio a * (Real.pi / 2) := by
  have h :=
    integral_Ioi_of_hasDerivAt_of_tendsto
      (continuous_derivativePrimitive a).continuousAt.continuousWithinAt
      (fun x hx => derivativePrimitive_hasDerivAt a x hx)
      (derivativeKernel_integrable a)
      (derivativePrimitive_tendsto a)
  simpa only [derivativePrimitive_one, sub_zero] using h

private theorem continuousOn_derivativeKernel (a : ℝ) :
    ContinuousOn (derivativeKernel a) (Ioi (1 : ℝ)) := by
  intro x hx
  change (1 : ℝ) < x at hx
  have hrad : 0 < x ^ 2 - 1 := by nlinarith
  have hroot : Real.sqrt (x ^ 2 - 1) ≠ 0 := by positivity
  have hx0 : x ≠ 0 := by linarith
  unfold derivativeKernel
  apply ContinuousAt.continuousWithinAt
  apply ContinuousAt.div continuousAt_const
  · fun_prop
  · change x * Real.sqrt (x ^ 2 - 1) *
      (1 + a ^ 2 * x ^ 2) ≠ 0
    positivity

private theorem continuousOn_paramKernel (a : ℝ) :
    ContinuousOn (paramKernel a) (Ioi (1 : ℝ)) := by
  intro x hx
  change (1 : ℝ) < x at hx
  have hrad : 0 < x ^ 2 - 1 := by nlinarith
  have hx0 : x ≠ 0 := by linarith
  have hroot : Real.sqrt (x ^ 2 - 1) ≠ 0 := by positivity
  unfold paramKernel
  apply ContinuousAt.continuousWithinAt
  apply ContinuousAt.div
  · fun_prop
  · fun_prop
  · change x ^ 2 * Real.sqrt (x ^ 2 - 1) ≠ 0
    exact mul_ne_zero (pow_ne_zero 2 hx0) hroot

private theorem abs_arctan_le (x : ℝ) :
    |Real.arctan x| ≤ Real.pi / 2 := by
  apply abs_le.mpr
  exact
    ⟨(Real.neg_pi_div_two_lt_arctan x).le,
      (Real.arctan_lt_pi_div_two x).le⟩

private theorem norm_paramKernel_le
    (a x : ℝ) (hx : x ∈ Ioi (1 : ℝ)) :
    ‖paramKernel a x‖ ≤
      (Real.pi / 2) * derivativeKernel 0 x := by
  change (1 : ℝ) < x at hx
  have hx0 : 0 < x := by linarith
  have hroot : 0 < Real.sqrt (x ^ 2 - 1) := by
    exact Real.sqrt_pos.2 (by nlinarith)
  have hden :
      x * Real.sqrt (x ^ 2 - 1) ≤
        x ^ 2 * Real.sqrt (x ^ 2 - 1) := by
    apply mul_le_mul_of_nonneg_right _ hroot.le
    nlinarith
  unfold paramKernel derivativeKernel
  rw [Real.norm_eq_abs, abs_div,
    abs_of_pos (mul_pos (sq_pos_of_pos hx0) hroot)]
  have hdiv :
      |Real.arctan (a * x)| /
          (x ^ 2 * Real.sqrt (x ^ 2 - 1)) ≤
        (Real.pi / 2) /
          (x * Real.sqrt (x ^ 2 - 1)) := by
    exact div_le_div₀ (by positivity) (abs_arctan_le _)
      (mul_pos hx0 hroot) hden
  calc
    |Real.arctan (a * x)| /
          (x ^ 2 * Real.sqrt (x ^ 2 - 1)) ≤
        (Real.pi / 2) /
          (x * Real.sqrt (x ^ 2 - 1)) := hdiv
    _ = (Real.pi / 2) *
          (1 /
            (x * Real.sqrt (x ^ 2 - 1) *
              (1 + 0 ^ 2 * x ^ 2))) := by
      norm_num
      ring

private theorem paramKernel_integrable (a : ℝ) :
    IntegrableOn (paramKernel a) (Ioi (1 : ℝ)) volume := by
  have hmajor :
      IntegrableOn
        (fun x : ℝ => (Real.pi / 2) * derivativeKernel 0 x)
        (Ioi (1 : ℝ)) volume :=
    (derivativeKernel_integrable 0).const_mul _
  change Integrable (paramKernel a)
    (volume.restrict (Ioi (1 : ℝ)))
  change Integrable
    (fun x : ℝ => (Real.pi / 2) * derivativeKernel 0 x)
    (volume.restrict (Ioi (1 : ℝ))) at hmajor
  apply hmajor.mono
  · exact
      (continuousOn_paramKernel a).aestronglyMeasurable
        measurableSet_Ioi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hnon :
        0 ≤ (Real.pi / 2) * derivativeKernel 0 x :=
      mul_nonneg (by positivity) (derivativeKernel_nonneg 0 x hx)
    simpa only [Real.norm_eq_abs, abs_of_nonneg hnon] using
      norm_paramKernel_le a x hx

private theorem norm_derivativeKernel_le
    (a x : ℝ) (hx : x ∈ Ioi (1 : ℝ)) :
    ‖derivativeKernel a x‖ ≤ derivativeKernel 0 x := by
  change (1 : ℝ) < x at hx
  have hx0 : 0 < x := by linarith
  have hroot : 0 < Real.sqrt (x ^ 2 - 1) := by
    exact Real.sqrt_pos.2 (by nlinarith)
  have hbase : 0 < x * Real.sqrt (x ^ 2 - 1) :=
    mul_pos hx0 hroot
  have hfactor : 1 ≤ 1 + a ^ 2 * x ^ 2 := by
    exact le_add_of_nonneg_right
      (mul_nonneg (sq_nonneg _) (sq_nonneg _))
  unfold derivativeKernel
  rw [Real.norm_eq_abs, abs_of_pos (by positivity :
    0 < 1 /
      (x * Real.sqrt (x ^ 2 - 1) *
        (1 + a ^ 2 * x ^ 2)))]
  have hden :
      x * Real.sqrt (x ^ 2 - 1) ≤
        x * Real.sqrt (x ^ 2 - 1) *
          (1 + a ^ 2 * x ^ 2) := by
    nlinarith
  calc
    1 /
        (x * Real.sqrt (x ^ 2 - 1) *
          (1 + a ^ 2 * x ^ 2)) ≤
        1 / (x * Real.sqrt (x ^ 2 - 1)) :=
      one_div_le_one_div_of_le hbase hden
    _ = 1 /
        (x * Real.sqrt (x ^ 2 - 1) *
          (1 + 0 ^ 2 * x ^ 2)) := by norm_num

private theorem paramKernel_hasDerivAt (a x : ℝ)
    (hx : x ∈ Ioi (1 : ℝ)) :
    HasDerivAt (fun b : ℝ => paramKernel b x)
      (derivativeKernel a x) a := by
  have hinner :
      HasDerivAt (fun b : ℝ => b * x) x a :=
    by
      simpa only [id_eq, one_mul] using
        (hasDerivAt_id a).mul_const x
  have hatan :=
    (Real.hasDerivAt_arctan (a * x)).comp a hinner
  change (1 : ℝ) < x at hx
  have hrad : 0 < x ^ 2 - 1 := by nlinarith
  have hx0 : x ≠ 0 := by linarith
  have hroot : Real.sqrt (x ^ 2 - 1) ≠ 0 := by positivity
  have h := hatan.div_const
    (x ^ 2 * Real.sqrt (x ^ 2 - 1))
  unfold paramKernel derivativeKernel
  convert h using 1
  field_simp [hx0, hroot] <;> ring

private theorem integralValue_hasDerivAt (a : ℝ) :
    HasDerivAt integralValue
      (Real.pi / 2 - ratio a * (Real.pi / 2)) a := by
  let μ : Measure ℝ := volume.restrict (Ioi (1 : ℝ))
  have hmeas :
      ∀ᶠ b in 𝓝 a,
        AEStronglyMeasurable (paramKernel b) μ :=
    Filter.Eventually.of_forall fun b =>
      (continuousOn_paramKernel b).aestronglyMeasurable
        measurableSet_Ioi
  have hderivMeas :
      AEStronglyMeasurable (derivativeKernel a) μ :=
    (continuousOn_derivativeKernel a).aestronglyMeasurable
      measurableSet_Ioi
  have hbound :
      ∀ᵐ x ∂μ, ∀ b ∈ (Set.univ : Set ℝ),
        ‖derivativeKernel b x‖ ≤ derivativeKernel 0 x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact fun b _ => norm_derivativeKernel_le b x hx
  have hdiff :
      ∀ᵐ x ∂μ, ∀ b ∈ (Set.univ : Set ℝ),
        HasDerivAt (fun c : ℝ => paramKernel c x)
          (derivativeKernel b x) b := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact fun b _ => paramKernel_hasDerivAt b x hx
  have hmain :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := μ) (F := paramKernel) (F' := derivativeKernel)
      univ_mem hmeas (paramKernel_integrable a)
      hderivMeas hbound (derivativeKernel_integrable 0) hdiff
  rw [derivativeKernel_integral a] at hmain
  simpa only [integralValue, μ] using hmain.2

private def positiveForm (a : ℝ) : ℝ :=
  (Real.pi / 2) *
    (1 + a - Real.sqrt (1 + a ^ 2))

private theorem positiveForm_hasDerivAt (a : ℝ) :
    HasDerivAt positiveForm
      ((Real.pi / 2) *
        (1 - a / Real.sqrt (1 + a ^ 2))) a := by
  have hinner :
      HasDerivAt (fun b : ℝ => 1 + b ^ 2) (2 * a) a := by
    convert
      (hasDerivAt_const a 1).add ((hasDerivAt_id a).pow 2)
      using 1 <;> simp [id] <;> ring
  have hroot :=
    (Real.hasDerivAt_sqrt (by positivity :
      1 + a ^ 2 ≠ 0)).comp a hinner
  unfold positiveForm
  convert
    (((hasDerivAt_const a 1).add (hasDerivAt_id a)).sub
      hroot).const_mul (Real.pi / 2) using 1
  field_simp [show Real.sqrt (1 + a ^ 2) ≠ 0 by positivity]
  ring

private theorem integralValue_zero :
    integralValue 0 = 0 := by
  unfold integralValue paramKernel
  simp

private theorem positiveForm_zero :
    positiveForm 0 = 0 := by
  simp [positiveForm]

private theorem integralValue_eq_positiveForm
    (a : ℝ) (ha : 0 ≤ a) :
    integralValue a = positiveForm a := by
  let G : ℝ → ℝ := fun t =>
    integralValue t - positiveForm t
  have hG (t : ℝ) (ht : t ∈ Icc (0 : ℝ) a) :
      HasDerivAt G 0 t := by
    have hratio :
        ratio t = t / Real.sqrt (1 + t ^ 2) := by
      unfold ratio
      rw [abs_of_nonneg ht.1]
    have h :=
      (integralValue_hasDerivAt t).sub
        (positiveForm_hasDerivAt t)
    apply h.congr_deriv
    rw [hratio]
    ring
  have hbound :=
    Convex.norm_image_sub_le_of_norm_deriv_le
      (f := G) (s := Icc (0 : ℝ) a) (C := 0)
      (fun t ht => (hG t ht).differentiableAt)
      (fun t ht => by rw [(hG t ht).deriv, norm_zero])
      (convex_Icc (0 : ℝ) a)
      (by exact ⟨le_rfl, ha⟩)
      (by exact ⟨ha, le_rfl⟩)
  have hGa : G a = G 0 := by
    have hbound0 : ‖G a - G 0‖ ≤ 0 := by simpa using hbound
    have : ‖G a - G 0‖ = 0 :=
      le_antisymm hbound0 (norm_nonneg _)
    exact sub_eq_zero.mp (norm_eq_zero.mp this)
  dsimp [G] at hGa
  rw [integralValue_zero, positiveForm_zero, sub_zero] at hGa
  exact sub_eq_zero.mp hGa

private theorem integralValue_neg (a : ℝ) :
    integralValue (-a) = -integralValue a := by
  unfold integralValue paramKernel
  rw [← integral_neg]
  apply integral_congr_ae
  filter_upwards with x
  rw [neg_mul, Real.arctan_neg]
  ring

private theorem sqrt_sub_relation (x : ℝ) (hx : 1 < x) :
    Real.sqrt (x ^ 2 - 1) =
      x * Real.sqrt (1 - x⁻¹ ^ 2) := by
  rw [show x ^ 2 - 1 = x ^ 2 * (1 - x⁻¹ ^ 2) by
    field_simp [ne_of_gt (zero_lt_one.trans hx)]
    <;> ring]
  rw [Real.sqrt_mul (sq_nonneg x), Real.sqrt_sq (le_of_lt (zero_lt_one.trans hx))]

private theorem inv_sq_mul_transformedDerivative
    (a x : ℝ) (hx : 1 < x) :
    x⁻¹ ^ 2 * transformedDerivative a x⁻¹ =
      derivativeKernel a x := by
  have hx0 : x ≠ 0 := ne_of_gt (zero_lt_one.trans hx)
  have hs := sqrt_sub_relation x hx
  unfold transformedDerivative derivativeKernel
  rw [hs]
  field_simp [hx0]

private theorem transformed_integral_eq_derivativeKernel (a : ℝ) :
    (∫ t in (0 : ℝ)..1, transformedDerivative a t) =
      ∫ x in Ioi (1 : ℝ), derivativeKernel a x := by
  let g : ℝ → ℝ :=
    (Ioc (0 : ℝ) 1).indicator (transformedDerivative a)
  have hchange := integral_comp_rpow_Ioi g
    (p := (-1 : ℝ)) (by norm_num)
  have hleft :
      (∫ x in Ioi (0 : ℝ),
        (|(-1 : ℝ)| * x ^ ((-1 : ℝ) - 1)) •
          g (x ^ (-1 : ℝ))) =
        ∫ x in Ioi (1 : ℝ), derivativeKernel a x := by
    calc
      _ = ∫ x in Ioi (0 : ℝ),
          (Ioi (1 : ℝ)).indicator (derivativeKernel a) x := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro x hx
        dsimp only
        rcases lt_trichotomy x 1 with hxlt | rfl | hxgt
        · have hinv : 1 < x⁻¹ := (one_lt_inv₀ hx).2 hxlt
          have hnot : x⁻¹ ∉ Ioc (0 : ℝ) 1 := by
            exact fun h => (not_lt_of_ge h.2) hinv
          have hg : g x⁻¹ = 0 := by
            simp [g, hnot]
          rw [Real.rpow_neg_one, hg]
          have hxnot : x ∉ Ioi (1 : ℝ) := not_lt.mpr hxlt.le
          rw [Set.indicator_of_notMem hxnot]
          simp
        · simp [g, transformedDerivative]
        · have hinv : x⁻¹ ∈ Ioc (0 : ℝ) 1 := by
            exact ⟨inv_pos.mpr (zero_lt_one.trans hxgt),
              (inv_le_one₀ (zero_lt_one.trans hxgt)).2 hxgt.le⟩
          have hg : g x⁻¹ = transformedDerivative a x⁻¹ := by
            simp [g, hinv]
          rw [Real.rpow_neg_one, hg]
          have hind :
              (Ioi (1 : ℝ)).indicator (derivativeKernel a) x =
                derivativeKernel a x :=
            Set.indicator_of_mem hxgt _
          rw [hind]
          norm_num
          simpa only [inv_pow] using
            inv_sq_mul_transformedDerivative a x hxgt
      _ = ∫ x in Ioi (1 : ℝ), derivativeKernel a x := by
        rw [setIntegral_indicator measurableSet_Ioi]
        have hset :
            Ioi (0 : ℝ) ∩ Ioi (1 : ℝ) = Ioi (1 : ℝ) := by
          ext x
          simp only [mem_inter_iff, mem_Ioi]
          constructor
          · exact fun hx => hx.2
          · exact fun hx => ⟨zero_lt_one.trans hx, hx⟩
        rw [hset]
  have hright :
      (∫ y in Ioi (0 : ℝ), g y) =
        ∫ t in (0 : ℝ)..1, transformedDerivative a t := by
    unfold g
    rw [setIntegral_indicator measurableSet_Ioc]
    have hset :
        Ioi (0 : ℝ) ∩ Ioc (0 : ℝ) 1 = Ioc (0 : ℝ) 1 := by
      ext x
      simp
    rw [hset, ← intervalIntegral.integral_of_le zero_le_one]
  rw [hleft, hright] at hchange
  exact hchange.symm

private theorem integrand_asymptotic (α : ℝ) (hα : 0 < α) :
    Tendsto (fun x : ℝ => x ^ 3 * integrand α x)
      atTop (nhds (Real.pi / 2)) := by
  have hinv :
      Tendsto (fun x : ℝ => x⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero
  have hbase :
      Tendsto (fun x : ℝ => 1 - x⁻¹ ^ 2) atTop (nhds 1) := by
    simpa using tendsto_const_nhds.sub (hinv.pow 2)
  have hroot :
      Tendsto (fun x : ℝ => Real.sqrt (1 - x⁻¹ ^ 2))
        atTop (nhds 1) := by
    simpa using (Real.continuous_sqrt.tendsto 1).comp hbase
  have hrootinv :
      Tendsto (fun x : ℝ => (Real.sqrt (1 - x⁻¹ ^ 2))⁻¹)
        atTop (nhds 1) := by
    simpa using hroot.inv₀ one_ne_zero
  have hratio :
      Tendsto (fun x : ℝ => x / Real.sqrt (x ^ 2 - 1))
        atTop (nhds 1) := by
    apply hrootinv.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    rw [sqrt_sub_relation x hx]
    field_simp [ne_of_gt (zero_lt_one.trans hx)]
  have harg : Tendsto (fun x : ℝ => α * x) atTop atTop :=
    Tendsto.const_mul_atTop hα tendsto_id
  have hatan :
      Tendsto (fun x : ℝ => Real.arctan (α * x))
        atTop (nhds (Real.pi / 2)) :=
    (Real.tendsto_arctan_atTop.mono_right inf_le_left).comp harg
  have hprod :
      Tendsto
        (fun x : ℝ =>
          Real.arctan (α * x) * (x / Real.sqrt (x ^ 2 - 1)))
        atTop (nhds (Real.pi / 2)) := by
    simpa using hatan.mul hratio
  apply hprod.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hx0 : x ≠ 0 := ne_of_gt (zero_lt_one.trans hx)
  have hrootpos : 0 < Real.sqrt (x ^ 2 - 1) :=
    Real.sqrt_pos.2 (by nlinarith)
  unfold integrand
  field_simp [hx0, hrootpos.ne']

private theorem transformedDerivative_bound
    (t α : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    |transformedDerivative α t| ≤
      1 / Real.sqrt (1 - t ^ 2) := by
  have htpos : 0 < t := ht.1
  have hsub : 0 < 1 - t ^ 2 := by
    nlinarith [(sq_lt_sq₀ htpos.le zero_le_one).2 ht.2]
  have hroot : 0 < Real.sqrt (1 - t ^ 2) :=
    Real.sqrt_pos.2 hsub
  have hsum : 0 < t ^ 2 + α ^ 2 := by
    nlinarith [sq_pos_of_pos htpos, sq_nonneg α]
  unfold transformedDerivative
  rw [abs_of_pos (div_pos (sq_pos_of_pos htpos) (mul_pos hroot hsum))]
  rw [div_le_iff₀ (mul_pos hroot hsum)]
  field_simp [hroot.ne']
  exact le_add_of_nonneg_right (sq_nonneg α)


theorem gap1 :
    I 0 = 0 := by
  change integralValue 0 = 0
  exact integralValue_zero

theorem gap2 (α : ℝ) (hα : 0 < α) :
    Tendsto (fun x : ℝ => x ^ 3 * integrand α x)
      atTop (nhds (Real.pi / 2)) := by
  exact integrand_asymptotic α hα

theorem gap3 (α : ℝ) (hα : 0 < α) :
    IntegrableOn (integrand α) (Set.Ioi (1 : ℝ)) := by
  exact paramKernel_integrable α

theorem gap4 (α : ℝ) :
    (∫ x in Set.Ioi (1 : ℝ),
      deriv (fun a : ℝ => integrand a x) α) =
        ∫ t in (0 : ℝ)..1, transformedDerivative α t := by
  calc
    (∫ x in Set.Ioi (1 : ℝ),
        deriv (fun a : ℝ => integrand a x) α) =
        ∫ x in Set.Ioi (1 : ℝ), derivativeKernel α x := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      exact (paramKernel_hasDerivAt α x hx).deriv
    _ = ∫ t in (0 : ℝ)..1, transformedDerivative α t :=
      (transformed_integral_eq_derivativeKernel α).symm

theorem gap5 (t α : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    |transformedDerivative α t| ≤
      1 / Real.sqrt (1 - t ^ 2) := by
  exact transformedDerivative_bound t α ht

theorem gap6 (α : ℝ) :
    deriv I α =
      ∫ t in (0 : ℝ)..1, transformedDerivative α t := by
  change deriv integralValue α =
    ∫ t in (0 : ℝ)..1, transformedDerivative α t
  rw [(integralValue_hasDerivAt α).deriv,
    transformed_integral_eq_derivativeKernel α,
    derivativeKernel_integral α]

private theorem invSqrt_intervalIntegrable :
    IntervalIntegrable
      (fun t : ℝ => 1 / Real.sqrt (1 - t ^ 2)) volume 0 1 := by
  apply intervalIntegral.intervalIntegrable_deriv_of_nonneg
  · simpa [Set.uIcc_of_le zero_le_one] using
      Real.continuous_arcsin.continuousOn
  · intro t ht
    norm_num at ht
    exact Real.hasDerivAt_arcsin (by linarith) (by linarith)
  · intro t ht
    positivity

private theorem transformed_intervalIntegrable (a : ℝ) :
    IntervalIntegrable (transformedDerivative a) volume 0 1 := by
  have hmajor := invSqrt_intervalIntegrable
  rw [intervalIntegrable_iff, Set.uIoc_of_le zero_le_one] at hmajor ⊢
  apply hmajor.mono'
  · have hm : Measurable (transformedDerivative a) := by
      unfold transformedDerivative
      fun_prop
    exact hm.aestronglyMeasurable
  · have hne0 : ∀ᵐ t : ℝ ∂volume, t ≠ 0 := volume.ae_ne 0
    have hne1 : ∀ᵐ t : ℝ ∂volume, t ≠ 1 := volume.ae_ne 1
    filter_upwards [ae_restrict_mem measurableSet_Ioc,
      ae_restrict_of_ae hne0, ae_restrict_of_ae hne1] with t ht ht0 ht1
    have ht' : t ∈ Ioo (0 : ℝ) 1 :=
      ⟨ht.1, lt_of_le_of_ne ht.2 ht1⟩
    have hnon : 0 ≤ 1 / Real.sqrt (1 - t ^ 2) := by positivity
    simpa only [Real.norm_eq_abs, abs_of_nonneg hnon] using
      transformedDerivative_bound t a ht'

private theorem transformed_integral_decomposition (a : ℝ) :
    (∫ t in (0 : ℝ)..1, transformedDerivative a t) =
      (∫ t in (0 : ℝ)..1, 1 / Real.sqrt (1 - t ^ 2)) -
        a ^ 2 * ∫ t in (0 : ℝ)..1,
          1 / (Real.sqrt (1 - t ^ 2) * (t ^ 2 + a ^ 2)) := by
  let base : ℝ → ℝ :=
    fun t => 1 / Real.sqrt (1 - t ^ 2)
  let scaled : ℝ → ℝ :=
    fun t => a ^ 2 *
      (1 / (Real.sqrt (1 - t ^ 2) * (t ^ 2 + a ^ 2)))
  have hbase : IntervalIntegrable base volume 0 1 :=
    invSqrt_intervalIntegrable
  have htrans : IntervalIntegrable (transformedDerivative a) volume 0 1 :=
    transformed_intervalIntegrable a
  have hscaled : IntervalIntegrable scaled volume 0 1 := by
    apply (hbase.sub htrans).congr_ae
    have hne0 : ∀ᵐ t : ℝ ∂volume, t ≠ 0 := volume.ae_ne 0
    have hne1 : ∀ᵐ t : ℝ ∂volume, t ≠ 1 := volume.ae_ne 1
    filter_upwards [ae_restrict_mem measurableSet_uIoc,
      ae_restrict_of_ae hne0, ae_restrict_of_ae hne1] with t ht ht0 ht1
    rw [Set.uIoc_of_le zero_le_one] at ht
    dsimp [base, scaled]
    unfold transformedDerivative
    have hroot : Real.sqrt (1 - t ^ 2) ≠ 0 := by
      rw [Real.sqrt_ne_zero']
      have htlt : t < 1 := lt_of_le_of_ne ht.2 ht1
      nlinarith [(sq_lt_sq₀ ht.1.le zero_le_one).2 htlt]
    field_simp [ht0, hroot]
    ring
  rw [← intervalIntegral.integral_const_mul]
  change (∫ t in (0 : ℝ)..1, transformedDerivative a t) =
    (∫ t in (0 : ℝ)..1, base t) -
      ∫ t in (0 : ℝ)..1, scaled t
  rw [← intervalIntegral.integral_sub hbase hscaled]
  apply intervalIntegral.integral_congr_ae
  have hne0 : ∀ᵐ t : ℝ ∂volume, t ≠ 0 := volume.ae_ne 0
  have hne1 : ∀ᵐ t : ℝ ∂volume, t ≠ 1 := volume.ae_ne 1
  filter_upwards [hne0, hne1] with t ht0 ht1
  intro ht
  dsimp [base, scaled]
  unfold transformedDerivative
  have hroot : Real.sqrt (1 - t ^ 2) ≠ 0 := by
    rw [Real.sqrt_ne_zero']
    change t ∈ Set.uIoc (0 : ℝ) 1 at ht
    rw [Set.uIoc_of_le zero_le_one] at ht
    have htlt : t < 1 := lt_of_le_of_ne ht.2 ht1
    nlinarith [(sq_lt_sq₀ ht.1.le zero_le_one).2 htlt]
  field_simp [ht0, hroot]
  ring

private theorem positiveClosedPrimitive_hasDerivAt (a : ℝ) :
    HasDerivAt
      (fun b : ℝ =>
        Real.pi / 2 * b -
          Real.pi / 2 * Real.sqrt (1 + b ^ 2))
      (positiveDerivative a) a := by
  have h := (positiveForm_hasDerivAt a).sub_const (Real.pi / 2)
  convert h using 1
  · funext b
    unfold positiveForm
    ring
  · unfold positiveDerivative
    ring

theorem gap7 (α : ℝ) :
    deriv I α =
      ∫ t in (0 : ℝ)..1,
        (t ^ 2 + α ^ 2 - α ^ 2) /
          (Real.sqrt (1 - t ^ 2) * (t ^ 2 + α ^ 2)) := by
  rw [gap6 α]
  apply intervalIntegral.integral_congr
  intro t ht
  simp only [transformedDerivative]
  congr 1
  ring

theorem gap8 (α : ℝ) :
    deriv I α =
      (∫ t in (0 : ℝ)..1, 1 / Real.sqrt (1 - t ^ 2)) -
        α ^ 2 * ∫ t in (0 : ℝ)..1,
          1 / (Real.sqrt (1 - t ^ 2) * (t ^ 2 + α ^ 2)) := by
  rw [gap6 α]
  exact transformed_integral_decomposition α

theorem gap9 (α : ℝ) (hα : 0 < α) :
    deriv I α = positiveDerivative α := by
  change deriv integralValue α = positiveDerivative α
  rw [(integralValue_hasDerivAt α).deriv]
  unfold positiveDerivative ratio
  rw [abs_of_pos hα]
  ring

theorem gap10 :
    I ∈ PositivePrimitiveFamily := by
  intro α hα
  change HasDerivAt integralValue (positiveDerivative α) α
  have h := integralValue_hasDerivAt α
  convert h using 1
  unfold positiveDerivative ratio
  rw [abs_of_pos hα]
  ring

theorem gap11 :
    PositivePrimitiveFamily = PositiveClosedFormFamily := by
  ext G
  constructor
  · intro hG
    change ∀ α : ℝ, 0 < α →
      HasDerivAt G (positiveDerivative α) α at hG
    let F : ℝ → ℝ :=
      fun α => Real.pi / 2 * α -
        Real.pi / 2 * Real.sqrt (1 + α ^ 2)
    have hF (α : ℝ) :
        HasDerivAt F (positiveDerivative α) α := by
      exact positiveClosedPrimitive_hasDerivAt α
    have hGdiff : DifferentiableOn ℝ G (Ioi (0 : ℝ)) := by
      intro α hα
      exact (hG α hα).differentiableAt.differentiableWithinAt
    have hFdiff : DifferentiableOn ℝ F (Ioi (0 : ℝ)) := by
      intro α hα
      exact (hF α).differentiableAt.differentiableWithinAt
    have hderiv :
        Set.EqOn (deriv G) (deriv F) (Ioi (0 : ℝ)) := by
      intro α hα
      rw [(hG α hα).deriv, (hF α).deriv]
    obtain ⟨C, hC⟩ :=
      isOpen_Ioi.exists_eq_add_of_deriv_eq
        isPreconnected_Ioi hGdiff hFdiff hderiv
    refine ⟨C, ?_⟩
    intro α hα
    exact hC hα
  · rintro ⟨C, hG⟩
    change ∀ α : ℝ, 0 < α →
      HasDerivAt G (positiveDerivative α) α
    intro α hα
    have heq :
        G =ᶠ[nhds α]
          fun b : ℝ =>
            (Real.pi / 2 * b -
              Real.pi / 2 * Real.sqrt (1 + b ^ 2)) + C := by
      filter_upwards [Ioi_mem_nhds hα] with b hb
      exact hG b hb
    exact
      ((positiveClosedPrimitive_hasDerivAt α).add_const C).congr_of_eventuallyEq heq

theorem gap12 :
    I ∈ PositiveClosedFormFamily := by
  rw [← gap11]
  exact gap10

theorem gap13 :
    I 0 = 0 := by
  exact gap1

theorem gap14 :
    ∃ C : ℝ, 0 = -(Real.pi / 2) + C := by
  refine ⟨Real.pi / 2, ?_⟩
  ring

theorem gap15 :
    ∃ C : ℝ, I 0 = -(Real.pi / 2) + C := by
  rw [gap1]
  exact gap14

theorem gap16 :
    ∃ C : ℝ, C = Real.pi / 2 := by
  exact ⟨Real.pi / 2, rfl⟩

theorem gap17 (α : ℝ) (hα : 0 ≤ α) :
    I α = Real.pi / 2 *
      (1 + α - Real.sqrt (1 + α ^ 2)) := by
  change integralValue α = _
  simpa [positiveForm] using integralValue_eq_positiveForm α hα

theorem gap18 (α : ℝ) (hα : α < 0) :
    I α = -I (-α) := by
  unfold I integrand
  rw [← MeasureTheory.integral_neg]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with x
  rw [show (-α) * x = -(α * x) by ring, Real.arctan_neg]
  ring

theorem gap19 (α : ℝ) (hα : α < 0) :
    I α = -(Real.pi / 2) *
      (1 - α - Real.sqrt (1 + α ^ 2)) := by
  rw [gap18 α hα, gap17 (-α) (by linarith)]
  congr 2
  ring

theorem gap20 (α : ℝ) :
    I α = Real.pi / 2 *
      (1 + |α| - Real.sqrt (1 + α ^ 2)) * SignType.sign α := by
  by_cases hzero : α = 0
  · subst α
    simp [gap1]
  rcases lt_or_gt_of_ne hzero with hneg | hpos
  · rw [gap19 α hneg, abs_of_neg hneg, sign_neg hneg]
    simp only [SignType.coe_neg_one]
    ring
  · rw [gap17 α hpos.le, abs_of_pos hpos, sign_pos hpos]
    simp

end

end ProofGap.Exercise3799
