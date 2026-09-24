import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Data.Real.Sign
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3801

noncomputable section

open Filter MeasureTheory Set
open scoped Interval Topology

def integrand (α β x : ℝ) : ℝ :=
  Real.arctan (α * x) * Real.arctan (β * x) / x ^ 2

def I (α β : ℝ) : ℝ :=
  ∫ x in Set.Ioi (0 : ℝ), integrand α β x

def J (α β : ℝ) : ℝ :=
  ∫ x in Set.Ioi (0 : ℝ),
    Real.arctan (β * x) / (x * (1 + α ^ 2 * x ^ 2))

def K (α β : ℝ) : ℝ :=
  ∫ x in Set.Ioi (0 : ℝ),
    1 / ((1 + α ^ 2 * x ^ 2) * (1 + β ^ 2 * x ^ 2))

def entropyForm (α β : ℝ) : ℝ :=
  (α + β) * Real.log (α + β) -
    α * Real.log α - β * Real.log β

def alphaPrimitive (α β : ℝ) : ℝ :=
  (α + β) * Real.log (α + β) - α * Real.log α

private def oneKernel (a x : ℝ) : ℝ :=
  1 / (1 + a ^ 2 * x ^ 2)

private def onePrimitive (a x : ℝ) : ℝ :=
  Real.arctan (a * x) / a

private theorem onePrimitive_hasDerivAt
    (a x : ℝ) (ha : 0 < a) :
    HasDerivAt (onePrimitive a) (oneKernel a x) x := by
  have hinner :
      HasDerivAt (fun y : ℝ => a * y) a x := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id x).const_mul a
  have h :=
    ((Real.hasDerivAt_arctan (a * x)).comp x hinner).div_const a
  unfold onePrimitive oneKernel
  convert h using 1
  field_simp [ha.ne']

private theorem onePrimitive_tendsto
    (a : ℝ) (ha : 0 < a) :
    Tendsto (onePrimitive a) atTop
      (𝓝 (Real.pi / (2 * a))) := by
  have harg :
      Tendsto (fun x : ℝ => a * x) atTop atTop :=
    tendsto_id.const_mul_atTop ha
  have hatan :
      Tendsto (fun x : ℝ => Real.arctan (a * x))
        atTop (𝓝 (Real.pi / 2)) :=
    tendsto_nhds_of_tendsto_nhdsWithin
      (Real.tendsto_arctan_atTop.comp harg)
  simpa only [onePrimitive, div_div] using hatan.div_const a

private theorem oneKernel_nonneg (a x : ℝ) :
    0 ≤ oneKernel a x := by
  unfold oneKernel
  positivity

private theorem oneKernel_integrable
    (a : ℝ) (ha : 0 < a) :
    IntegrableOn (oneKernel a) (Ioi (0 : ℝ)) volume := by
  exact integrableOn_Ioi_deriv_of_nonneg
    (by
      unfold onePrimitive
      fun_prop)
    (fun x _ => onePrimitive_hasDerivAt a x ha)
    (fun x _ => oneKernel_nonneg a x)
    (onePrimitive_tendsto a ha)

private theorem oneKernel_integral
    (a : ℝ) (ha : 0 < a) :
    (∫ x in Ioi (0 : ℝ), oneKernel a x ∂volume) =
      Real.pi / (2 * a) := by
  have h :=
    integral_Ioi_of_hasDerivAt_of_tendsto
      (by
        unfold onePrimitive
        fun_prop)
      (fun x _ => onePrimitive_hasDerivAt a x ha)
      (oneKernel_integrable a ha)
      (onePrimitive_tendsto a ha)
  simpa [onePrimitive] using h

private def squareOneKernel (a x : ℝ) : ℝ :=
  1 / (1 + a ^ 2 * x ^ 2) ^ 2

private def squareOnePrimitive (a x : ℝ) : ℝ :=
  Real.arctan (a * x) / (2 * a) +
    x / (2 * (1 + a ^ 2 * x ^ 2))

private theorem squareOnePrimitive_hasDerivAt
    (a x : ℝ) (ha : 0 < a) :
    HasDerivAt (squareOnePrimitive a)
      (squareOneKernel a x) x := by
  have hinner :
      HasDerivAt (fun y : ℝ => a * y) a x := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id x).const_mul a
  have hatan :=
    ((Real.hasDerivAt_arctan (a * x)).comp x hinner).div_const (2 * a)
  have hden :
      HasDerivAt (fun y : ℝ => 2 * (1 + a ^ 2 * y ^ 2))
        (4 * a ^ 2 * x) x := by
    convert
      ((hasDerivAt_const x 1).add
        (((hasDerivAt_id x).pow 2).const_mul (a ^ 2))).const_mul 2
      using 1 <;>
      simp only [id_eq] <;> ring
  have hquot :=
    (hasDerivAt_id x).div hden
      (by positivity : 2 * (1 + a ^ 2 * x ^ 2) ≠ 0)
  simp only [id_eq] at hquot
  unfold squareOnePrimitive squareOneKernel
  convert hatan.add hquot using 1
  field_simp [ha.ne']
  ring

private theorem squareOnePrimitive_continuous
    (a : ℝ) (ha : 0 < a) :
    Continuous (squareOnePrimitive a) := by
  unfold squareOnePrimitive
  apply Continuous.add
  · fun_prop
  · apply Continuous.div
    · fun_prop
    · fun_prop
    · intro x
      positivity

private theorem squareOnePrimitive_tendsto
    (a : ℝ) (ha : 0 < a) :
    Tendsto (squareOnePrimitive a) atTop
      (𝓝 (Real.pi / (4 * a))) := by
  have harg :
      Tendsto (fun x : ℝ => a * x) atTop atTop :=
    tendsto_id.const_mul_atTop ha
  have hatan :
      Tendsto (fun x : ℝ => Real.arctan (a * x) / (2 * a))
        atTop (𝓝 (Real.pi / (4 * a))) := by
    have h :=
      (tendsto_nhds_of_tendsto_nhdsWithin
        (Real.tendsto_arctan_atTop.comp harg)).div_const (2 * a)
    convert h using 1 <;> ring
  have hratio :
      Tendsto (fun x : ℝ => x / (1 + a ^ 2 * x ^ 2))
        atTop (𝓝 0) := by
    have hden :
        Tendsto (fun x : ℝ => 1 / x + a ^ 2 * x)
          atTop atTop :=
      (tendsto_const_nhds.div_atTop tendsto_id).add_atTop
        (tendsto_id.const_mul_atTop (sq_pos_of_pos ha))
    have hbase :
        Tendsto (fun x : ℝ => 1 / (1 / x + a ^ 2 * x))
          atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hden
    apply hbase.congr'
    filter_upwards [eventually_ne_atTop (0 : ℝ)] with x hx
    field_simp [ha.ne']
  have hsecond :
      Tendsto (fun x : ℝ => x / (2 * (1 + a ^ 2 * x ^ 2)))
        atTop (𝓝 0) := by
    have heq :
        (fun x : ℝ => x / (2 * (1 + a ^ 2 * x ^ 2))) =
          (fun x : ℝ => (x / (1 + a ^ 2 * x ^ 2)) / 2) := by
      funext x
      have hd : 1 + a ^ 2 * x ^ 2 ≠ 0 := by positivity
      field_simp [hd]
    rw [heq]
    simpa using hratio.div_const 2
  simpa only [squareOnePrimitive, add_zero] using hatan.add hsecond

private theorem squareOneKernel_integrable
    (a : ℝ) (ha : 0 < a) :
    IntegrableOn (squareOneKernel a) (Ioi (0 : ℝ)) volume := by
  exact integrableOn_Ioi_deriv_of_nonneg
    (squareOnePrimitive_continuous a ha).continuousAt.continuousWithinAt
    (fun x _ => squareOnePrimitive_hasDerivAt a x ha)
    (fun x _ => by unfold squareOneKernel; positivity)
    (squareOnePrimitive_tendsto a ha)

private theorem squareOneKernel_integral
    (a : ℝ) (ha : 0 < a) :
    (∫ x in Ioi (0 : ℝ), squareOneKernel a x ∂volume) =
      Real.pi / (4 * a) := by
  have h :=
    integral_Ioi_of_hasDerivAt_of_tendsto
      (squareOnePrimitive_continuous a ha).continuousAt.continuousWithinAt
      (fun x _ => squareOnePrimitive_hasDerivAt a x ha)
      (squareOneKernel_integrable a ha)
      (squareOnePrimitive_tendsto a ha)
  simpa [squareOnePrimitive] using h

private def mixedKernel (a b x : ℝ) : ℝ :=
  1 / ((1 + a ^ 2 * x ^ 2) * (1 + b ^ 2 * x ^ 2))

private theorem mixedKernel_continuous (a b : ℝ) :
    Continuous (mixedKernel a b) := by
  unfold mixedKernel
  apply Continuous.div
  · fun_prop
  · fun_prop
  · intro x
    positivity

private theorem mixedKernel_nonneg (a b x : ℝ) :
    0 ≤ mixedKernel a b x := by
  unfold mixedKernel
  positivity

private theorem mixedKernel_le_oneKernel
    (a b x : ℝ) :
    mixedKernel a b x ≤ oneKernel a x := by
  have hA : 0 < 1 + a ^ 2 * x ^ 2 := by positivity
  have hB : 1 ≤ 1 + b ^ 2 * x ^ 2 := by
    nlinarith [mul_nonneg (sq_nonneg b) (sq_nonneg x)]
  unfold mixedKernel oneKernel
  have hden :
      1 + a ^ 2 * x ^ 2 ≤
        (1 + a ^ 2 * x ^ 2) * (1 + b ^ 2 * x ^ 2) := by
    nlinarith
  exact one_div_le_one_div_of_le hA hden

private theorem mixedKernel_integrable
    (a b : ℝ) (ha : 0 < a) :
    IntegrableOn (mixedKernel a b) (Ioi (0 : ℝ)) volume := by
  apply (oneKernel_integrable a ha).mono'
  · exact (mixedKernel_continuous a b).aestronglyMeasurable
  · filter_upwards with x
    rw [Real.norm_eq_abs,
      abs_of_nonneg (mixedKernel_nonneg a b x)]
    exact mixedKernel_le_oneKernel a b x

private theorem mixedKernel_eq_partialFractions
    (a b x : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hab : a ≠ b) :
    mixedKernel a b x =
      a ^ 2 / (a ^ 2 - b ^ 2) * oneKernel a x -
        b ^ 2 / (a ^ 2 - b ^ 2) * oneKernel b x := by
  have hfactor : a ^ 2 - b ^ 2 ≠ 0 := by
    intro h
    have hsquare : a ^ 2 = b ^ 2 := by linarith
    have : a = b := by nlinarith
    exact hab this
  have hA : 1 + a ^ 2 * x ^ 2 ≠ 0 := by positivity
  have hB : 1 + b ^ 2 * x ^ 2 ≠ 0 := by positivity
  unfold mixedKernel oneKernel
  field_simp [hfactor, hA, hB]
  ring

private theorem mixedKernel_integral
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (∫ x in Ioi (0 : ℝ), mixedKernel a b x ∂volume) =
      Real.pi / (2 * (a + b)) := by
  by_cases hab : a = b
  · subst b
    have heq :
        mixedKernel a a = squareOneKernel a := by
      funext x
      unfold mixedKernel squareOneKernel
      ring
    rw [heq, squareOneKernel_integral a ha]
    field_simp [ha.ne']
    norm_num
  · have hfactor : a ^ 2 - b ^ 2 ≠ 0 := by
      intro h
      have hsquare : a ^ 2 = b ^ 2 := by linarith
      have : a = b := by nlinarith
      exact hab this
    calc
      (∫ x in Ioi (0 : ℝ), mixedKernel a b x ∂volume) =
          ∫ x in Ioi (0 : ℝ),
            (a ^ 2 / (a ^ 2 - b ^ 2) * oneKernel a x -
              b ^ 2 / (a ^ 2 - b ^ 2) * oneKernel b x) ∂volume := by
            apply setIntegral_congr_fun measurableSet_Ioi
            intro x _
            exact mixedKernel_eq_partialFractions a b x ha hb hab
      _ = a ^ 2 / (a ^ 2 - b ^ 2) *
            ∫ x in Ioi (0 : ℝ), oneKernel a x ∂volume -
          b ^ 2 / (a ^ 2 - b ^ 2) *
            ∫ x in Ioi (0 : ℝ), oneKernel b x ∂volume := by
            rw [integral_sub
              ((oneKernel_integrable a ha).const_mul _)
              ((oneKernel_integrable b hb).const_mul _)]
            rw [integral_const_mul, integral_const_mul]
      _ = a ^ 2 / (a ^ 2 - b ^ 2) *
            (Real.pi / (2 * a)) -
          b ^ 2 / (a ^ 2 - b ^ 2) *
            (Real.pi / (2 * b)) := by
            rw [oneKernel_integral a ha, oneKernel_integral b hb]
      _ = Real.pi / (2 * (a + b)) := by
            have hsum : a + b ≠ 0 := by positivity
            field_simp [ha.ne', hb.ne', hfactor, hsum]
            ring

private theorem arctan_le_self_of_nonneg
    (z : ℝ) (hz : 0 ≤ z) :
    Real.arctan z ≤ z := by
  calc
    Real.arctan z ≤ Real.tan (Real.arctan z) :=
      Real.le_tan (Real.arctan_nonneg.mpr hz)
        (Real.arctan_lt_pi_div_two z)
    _ = z := Real.tan_arctan z

private theorem abs_arctan_le_abs (z : ℝ) :
    |Real.arctan z| ≤ |z| := by
  by_cases hz : 0 ≤ z
  · rw [abs_of_nonneg (Real.arctan_nonneg.mpr hz), abs_of_nonneg hz]
    exact arctan_le_self_of_nonneg z hz
  · have hnz : 0 ≤ -z := neg_nonneg.mpr (le_of_not_ge hz)
    calc
      |Real.arctan z| = |Real.arctan (-z)| := by
        rw [Real.arctan_neg, abs_neg]
      _ = Real.arctan (-z) :=
        abs_of_nonneg (Real.arctan_nonneg.mpr hnz)
      _ ≤ -z := arctan_le_self_of_nonneg (-z) hnz
      _ = |z| := (abs_of_nonpos (le_of_not_ge hz)).symm

private def jKernel (a b x : ℝ) : ℝ :=
  Real.arctan (b * x) / (x * (1 + a ^ 2 * x ^ 2))

private def jValue (a b : ℝ) : ℝ :=
  ∫ x in Ioi (0 : ℝ), jKernel a b x ∂volume

private theorem jKernel_continuousOn (a b : ℝ) :
    ContinuousOn (jKernel a b) (Ioi (0 : ℝ)) := by
  intro x hx
  have hx0 : x ≠ 0 := ne_of_gt hx
  unfold jKernel
  apply ContinuousAt.continuousWithinAt
  apply ContinuousAt.div
  · fun_prop
  · fun_prop
  · exact mul_ne_zero hx0 (by positivity)

private theorem norm_jKernel_le
    (a b x : ℝ) (hx : 0 < x) :
    ‖jKernel a b x‖ ≤ |b| * oneKernel a x := by
  have hden : 0 < x * (1 + a ^ 2 * x ^ 2) := by positivity
  unfold jKernel oneKernel
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hden]
  have hnum := abs_arctan_le_abs (b * x)
  rw [abs_mul, abs_of_pos hx] at hnum
  calc
    |Real.arctan (b * x)| / (x * (1 + a ^ 2 * x ^ 2)) ≤
        (|b| * x) / (x * (1 + a ^ 2 * x ^ 2)) :=
      div_le_div_of_nonneg_right hnum hden.le
    _ = |b| * (1 / (1 + a ^ 2 * x ^ 2)) := by
      field_simp [hx.ne']

private theorem jKernel_integrable
    (a b : ℝ) (ha : 0 < a) :
    IntegrableOn (jKernel a b) (Ioi (0 : ℝ)) volume := by
  have hmajor :
      IntegrableOn (fun x : ℝ => |b| * oneKernel a x)
        (Ioi (0 : ℝ)) volume :=
    (oneKernel_integrable a ha).const_mul _
  apply hmajor.mono'
  · exact (jKernel_continuousOn a b).aestronglyMeasurable
      measurableSet_Ioi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact norm_jKernel_le a b x hx

private theorem jKernel_hasDerivAt
    (a b x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun c : ℝ => jKernel a c x)
      (mixedKernel a b x) b := by
  have hinner :
      HasDerivAt (fun c : ℝ => c * x) x b := by
    simpa only [id_eq, one_mul] using
      (hasDerivAt_id b).mul_const x
  have hatan :=
    (Real.hasDerivAt_arctan (b * x)).comp b hinner
  have h := hatan.div_const (x * (1 + a ^ 2 * x ^ 2))
  unfold jKernel mixedKernel
  convert h using 1
  have hA : 1 + a ^ 2 * x ^ 2 ≠ 0 := by positivity
  have hB : 1 + b ^ 2 * x ^ 2 ≠ 0 := by positivity
  field_simp [hx.ne', hA, hB]

private theorem jValue_hasDerivAt
    (a b : ℝ) (ha : 0 < a) :
    HasDerivAt (jValue a)
      (∫ x in Ioi (0 : ℝ), mixedKernel a b x ∂volume) b := by
  let μ : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
  have hmeas :
      ∀ᶠ c in 𝓝 b,
        AEStronglyMeasurable (jKernel a c) μ :=
    Filter.Eventually.of_forall fun c =>
      (jKernel_continuousOn a c).aestronglyMeasurable
        measurableSet_Ioi
  have hderivMeas :
      AEStronglyMeasurable (mixedKernel a b) μ :=
    (mixedKernel_continuous a b).aestronglyMeasurable
  have hbound :
      ∀ᵐ x ∂μ, ∀ c ∈ (Set.univ : Set ℝ),
        ‖mixedKernel a c x‖ ≤ oneKernel a x := by
    filter_upwards with x
    intro c _
    rw [Real.norm_eq_abs,
      abs_of_nonneg (mixedKernel_nonneg a c x)]
    exact mixedKernel_le_oneKernel a c x
  have hdiff :
      ∀ᵐ x ∂μ, ∀ c ∈ (Set.univ : Set ℝ),
        HasDerivAt (fun d : ℝ => jKernel a d x)
          (mixedKernel a c x) c := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact fun c _ => jKernel_hasDerivAt a c x hx
  have hmain :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := μ) (F := fun c x => jKernel a c x)
      (F' := fun c x => mixedKernel a c x)
      univ_mem hmeas (jKernel_integrable a b ha)
      hderivMeas hbound (oneKernel_integrable a ha) hdiff
  simpa only [jValue, μ] using hmain.2

private theorem jValue_hasDerivAt_formula
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    HasDerivAt (jValue a)
      (Real.pi / (2 * (a + b))) b := by
  rw [← mixedKernel_integral a b ha hb]
  exact jValue_hasDerivAt a b ha

private def jForm (a b : ℝ) : ℝ :=
  (Real.pi / 2) * Real.log ((a + b) / a)

private theorem jForm_hasDerivAt
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    HasDerivAt (jForm a)
      (Real.pi / (2 * (a + b))) b := by
  have hinner :
      HasDerivAt (fun c : ℝ => (a + c) / a) (1 / a) b := by
    convert
      ((hasDerivAt_const b a).add (hasDerivAt_id b)).div_const a
      using 1 <;>
      simp only [id_eq, zero_add, one_div]
  have hlog :=
    (Real.hasDerivAt_log
      (by positivity : (a + b) / a ≠ 0)).comp b hinner
  unfold jForm
  convert hlog.const_mul (Real.pi / 2) using 1
  field_simp [ha.ne']

private theorem jValue_tendsto_zero
    (a : ℝ) (ha : 0 < a) :
    Tendsto (jValue a)
      (𝓝[Set.Ioi (0 : ℝ)] (0 : ℝ)) (𝓝 0) := by
  have hcont :
      Tendsto (jValue a) (𝓝 (0 : ℝ)) (𝓝 (jValue a 0)) :=
    (jValue_hasDerivAt a 0 ha).continuousAt
  have hzero : jValue a 0 = 0 := by
    simp [jValue, jKernel]
  simpa only [hzero] using hcont.mono_left inf_le_left

private theorem jForm_tendsto_zero
    (a : ℝ) (ha : 0 < a) :
    Tendsto (jForm a)
      (𝓝[Set.Ioi (0 : ℝ)] (0 : ℝ)) (𝓝 0) := by
  have hcont :
      Tendsto (jForm a) (𝓝 (0 : ℝ)) (𝓝 (jForm a 0)) := by
    apply ContinuousAt.tendsto
    unfold jForm
    apply ContinuousAt.const_mul
    apply ContinuousAt.log
    · fun_prop
    · simpa using ha.ne'
  have hzero : jForm a 0 = 0 := by
    simp [jForm, ha.ne']
  simpa only [hzero] using hcont.mono_left inf_le_left

private theorem jValue_eq_jForm
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    jValue a b = jForm a b := by
  let G : ℝ → ℝ := fun t => jValue a t - jForm a t
  have hG (t : ℝ) (ht : 0 < t) :
      HasDerivAt G 0 t := by
    have h :=
      (jValue_hasDerivAt_formula a t ha ht).sub
        (jForm_hasDerivAt a t ha ht)
    simpa only [G, sub_self] using h
  have hconstant (c : ℝ) (hc : 0 < c) (hcb : c ≤ b) :
      G c = G b := by
    have hbound :=
      Convex.norm_image_sub_le_of_norm_deriv_le
        (f := G) (s := Icc c b) (C := 0)
        (fun t ht =>
          (hG t (hc.trans_le ht.1)).differentiableAt)
        (fun t ht => by
          rw [(hG t (hc.trans_le ht.1)).deriv, norm_zero])
        (convex_Icc c b)
        ⟨le_rfl, hcb⟩
        ⟨hcb, le_rfl⟩
    have hzero : ‖G b - G c‖ = 0 := by
      apply le_antisymm
      · simpa using hbound
      · exact norm_nonneg _
    exact (sub_eq_zero.mp (norm_eq_zero.mp hzero)).symm
  have hGlim :
      Tendsto G (𝓝[Set.Ioi (0 : ℝ)] (0 : ℝ)) (𝓝 0) := by
    simpa only [G, sub_zero] using
      (jValue_tendsto_zero a ha).sub (jForm_tendsto_zero a ha)
  have hevent :
      G =ᶠ[𝓝[Set.Ioi (0 : ℝ)] (0 : ℝ)] fun _ => G b := by
    have hlt :
        ∀ᶠ c in 𝓝[Set.Ioi (0 : ℝ)] (0 : ℝ), c < b := by
      have h : ∀ᶠ c in 𝓝 (0 : ℝ), c < b :=
        Iio_mem_nhds hb
      exact h.filter_mono inf_le_left
    filter_upwards [self_mem_nhdsWithin, hlt] with c hc hcb
    exact hconstant c hc hcb.le
  have hconstlim :
      Tendsto G (𝓝[Set.Ioi (0 : ℝ)] (0 : ℝ)) (𝓝 (G b)) :=
    tendsto_const_nhds.congr' hevent.symm
  have hGb : G b = 0 :=
    tendsto_nhds_unique hconstlim hGlim
  exact sub_eq_zero.mp hGb

private def angleProduct (a b x : ℝ) : ℝ :=
  Real.arctan (a * x) * Real.arctan (b * x)

private def angleProductDeriv (a b x : ℝ) : ℝ :=
  (a / (1 + a ^ 2 * x ^ 2)) * Real.arctan (b * x) +
    (b / (1 + b ^ 2 * x ^ 2)) * Real.arctan (a * x)

private def negInv (x : ℝ) : ℝ :=
  -1 / x

private def invSq (x : ℝ) : ℝ :=
  1 / x ^ 2

private def targetKernel (a b x : ℝ) : ℝ :=
  Real.arctan (a * x) * Real.arctan (b * x) / x ^ 2

private theorem targetKernel_continuousOn (a b : ℝ) :
    ContinuousOn (targetKernel a b) (Ioi (0 : ℝ)) := by
  intro x hx
  unfold targetKernel
  apply ContinuousAt.continuousWithinAt
  apply ContinuousAt.div
  · fun_prop
  · fun_prop
  · exact pow_ne_zero 2 hx.ne'

private theorem norm_targetKernel_le_head
    (a b x : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hx : x ∈ Ioc (0 : ℝ) 1) :
    ‖targetKernel a b x‖ ≤ a * b := by
  have hxpos : 0 < x := hx.1
  have hax : 0 ≤ a * x := mul_nonneg ha.le hxpos.le
  have hbx : 0 ≤ b * x := mul_nonneg hb.le hxpos.le
  have hA0 : 0 ≤ Real.arctan (a * x) :=
    Real.arctan_nonneg.mpr hax
  have hB0 : 0 ≤ Real.arctan (b * x) :=
    Real.arctan_nonneg.mpr hbx
  have hA : Real.arctan (a * x) ≤ a * x :=
    arctan_le_self_of_nonneg (a * x) hax
  have hB : Real.arctan (b * x) ≤ b * x :=
    arctan_le_self_of_nonneg (b * x) hbx
  have hprod :
      Real.arctan (a * x) * Real.arctan (b * x) ≤
        (a * x) * (b * x) :=
    mul_le_mul hA hB hB0 (mul_nonneg ha.le hxpos.le)
  rw [Real.norm_eq_abs]
  unfold targetKernel
  rw [abs_of_nonneg
    (div_nonneg (mul_nonneg hA0 hB0) (sq_nonneg x))]
  calc
    Real.arctan (a * x) * Real.arctan (b * x) / x ^ 2 ≤
        ((a * x) * (b * x)) / x ^ 2 :=
      div_le_div_of_nonneg_right hprod (sq_nonneg x)
    _ = a * b := by
      field_simp [hxpos.ne']

private theorem norm_targetKernel_le_tail
    (a b x : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hx : 1 < x) :
    ‖targetKernel a b x‖ ≤
      (Real.pi / 2) ^ 2 * x ^ (-2 : ℝ) := by
  have hxpos : 0 < x := zero_lt_one.trans hx
  have hax : 0 ≤ a * x := mul_nonneg ha.le hxpos.le
  have hbx : 0 ≤ b * x := mul_nonneg hb.le hxpos.le
  have hA0 : 0 ≤ Real.arctan (a * x) :=
    Real.arctan_nonneg.mpr hax
  have hB0 : 0 ≤ Real.arctan (b * x) :=
    Real.arctan_nonneg.mpr hbx
  have hA : Real.arctan (a * x) ≤ Real.pi / 2 :=
    (Real.arctan_lt_pi_div_two _).le
  have hB : Real.arctan (b * x) ≤ Real.pi / 2 :=
    (Real.arctan_lt_pi_div_two _).le
  have hprod :
      Real.arctan (a * x) * Real.arctan (b * x) ≤
        (Real.pi / 2) ^ 2 := by
    have hpi : 0 ≤ Real.pi / 2 := by positivity
    calc
      Real.arctan (a * x) * Real.arctan (b * x) ≤
          (Real.pi / 2) * (Real.pi / 2) :=
        mul_le_mul hA hB hB0 hpi
      _ = (Real.pi / 2) ^ 2 := by ring
  rw [Real.norm_eq_abs]
  unfold targetKernel
  rw [abs_of_nonneg
    (div_nonneg (mul_nonneg hA0 hB0) (sq_nonneg x))]
  calc
    Real.arctan (a * x) * Real.arctan (b * x) / x ^ 2 ≤
        (Real.pi / 2) ^ 2 / x ^ 2 :=
      div_le_div_of_nonneg_right hprod (sq_nonneg x)
    _ = (Real.pi / 2) ^ 2 * x ^ (-2 : ℝ) := by
      rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num,
        Real.rpow_neg hxpos.le, Real.rpow_two]
      simp [div_eq_mul_inv]

private theorem targetKernel_integrable
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    IntegrableOn (targetKernel a b) (Ioi (0 : ℝ)) volume := by
  have hheadMajor :
      IntegrableOn (fun _ : ℝ => a * b) (Ioc (0 : ℝ) 1) volume :=
    integrableOn_const measure_Ioc_lt_top.ne
  have hhead :
      IntegrableOn (targetKernel a b) (Ioc (0 : ℝ) 1) volume := by
    apply hheadMajor.mono'
    · exact
        ((targetKernel_continuousOn a b).mono
          Ioc_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioc
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      exact norm_targetKernel_le_head a b x ha hb hx
  have htailMajor :
      IntegrableOn
        (fun x : ℝ => (Real.pi / 2) ^ 2 * x ^ (-2 : ℝ))
        (Ioi (1 : ℝ)) volume :=
    (integrableOn_Ioi_rpow_of_lt
      (a := (-2 : ℝ)) (c := 1) (by norm_num) zero_lt_one).const_mul _
  have htail :
      IntegrableOn (targetKernel a b) (Ioi (1 : ℝ)) volume := by
    apply htailMajor.mono'
    · exact
        ((targetKernel_continuousOn a b).mono
          (Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1))).aestronglyMeasurable
          measurableSet_Ioi
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      exact norm_targetKernel_le_tail a b x ha hb hx
  rw [← Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 1)]
  exact hhead.union htail

private theorem angleProduct_hasDerivAt
    (a b x : ℝ) :
    HasDerivAt (angleProduct a b)
      (angleProductDeriv a b x) x := by
  have hinnerA :
      HasDerivAt (fun y : ℝ => a * y) a x := by
    simpa only [id_eq, mul_one] using
      (hasDerivAt_id x).const_mul a
  have hinnerB :
      HasDerivAt (fun y : ℝ => b * y) b x := by
    simpa only [id_eq, mul_one] using
      (hasDerivAt_id x).const_mul b
  have hA :=
    (Real.hasDerivAt_arctan (a * x)).comp x hinnerA
  have hB :=
    (Real.hasDerivAt_arctan (b * x)).comp x hinnerB
  unfold angleProduct angleProductDeriv
  convert hA.mul hB using 1 <;>
    simp only [Function.comp_apply] <;>
    ring

private theorem negInv_hasDerivAt
    (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt negInv (invSq x) x := by
  have h :=
    (hasDerivAt_const x (-1 : ℝ)).div
      (hasDerivAt_id x) hx
  unfold negInv invSq
  convert h using 1
  simp only [id_eq, zero_mul, one_mul, zero_sub]
  field_simp [hx]

private theorem angleProductDeriv_mul_negInv_eq
    (a b x : ℝ) (hx : x ≠ 0) :
    angleProductDeriv a b x * negInv x =
      -(a * jKernel a b x + b * jKernel b a x) := by
  have hA : 1 + a ^ 2 * x ^ 2 ≠ 0 := by positivity
  have hB : 1 + b ^ 2 * x ^ 2 ≠ 0 := by positivity
  unfold angleProductDeriv negInv jKernel
  field_simp [hx, hA, hB]

private theorem angleProductDeriv_mul_negInv_integrable
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    IntegrableOn (angleProductDeriv a b * negInv)
      (Ioi (0 : ℝ)) volume := by
  have hsum :
      IntegrableOn
        (fun x : ℝ =>
          a * jKernel a b x + b * jKernel b a x)
        (Ioi (0 : ℝ)) volume :=
    ((jKernel_integrable a b ha).const_mul _).add
      ((jKernel_integrable b a hb).const_mul _)
  have hneg :
      IntegrableOn
        (fun x : ℝ =>
          -(a * jKernel a b x + b * jKernel b a x))
        (Ioi (0 : ℝ)) volume :=
    hsum.neg
  exact hneg.congr_fun
    (fun x hx =>
      (angleProductDeriv_mul_negInv_eq a b x hx.ne').symm)
    measurableSet_Ioi

private theorem angleProduct_mul_negInv_tendsto_zero
    (a b : ℝ) :
    Tendsto (angleProduct a b * negInv)
      (𝓝[Set.Ioi (0 : ℝ)] (0 : ℝ)) (𝓝 0) := by
  have hinnerA :
      HasDerivAt (fun y : ℝ => a * y) a 0 := by
    simpa only [id_eq, mul_one] using
      (hasDerivAt_id (0 : ℝ)).const_mul a
  have hAderiv :
      HasDerivAt (fun x : ℝ => Real.arctan (a * x)) a 0 := by
    simpa using
      (Real.hasDerivAt_arctan (a * 0)).comp 0 hinnerA
  have hAslope :
      Tendsto
        (fun x : ℝ => x⁻¹ * Real.arctan (a * x))
        (𝓝[Set.Ioi (0 : ℝ)] (0 : ℝ)) (𝓝 a) := by
    simpa only [zero_add, mul_zero, Real.arctan_zero,
      sub_zero, smul_eq_mul] using
      hAderiv.tendsto_slope_zero_right
  have hBzero :
      Tendsto (fun x : ℝ => Real.arctan (b * x))
        (𝓝[Set.Ioi (0 : ℝ)] (0 : ℝ)) (𝓝 0) := by
    have hfull :
        Tendsto (fun x : ℝ => Real.arctan (b * x))
          (𝓝 (0 : ℝ)) (𝓝 0) := by
      have hc :
          ContinuousAt (fun x : ℝ => Real.arctan (b * x)) 0 := by
        fun_prop
      simpa using hc.tendsto
    exact hfull.mono_left inf_le_left
  have hlim :
      Tendsto
        (fun x : ℝ =>
          -(x⁻¹ * Real.arctan (a * x)) *
            Real.arctan (b * x))
        (𝓝[Set.Ioi (0 : ℝ)] (0 : ℝ)) (𝓝 0) := by
    simpa using hAslope.neg.mul hBzero
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : x ≠ 0 := hx.ne'
  unfold angleProduct negInv
  dsimp only [Pi.mul_apply]
  field_simp [hx0]

private theorem angleProduct_mul_negInv_tendsto_atTop_zero
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Tendsto (angleProduct a b * negInv)
      atTop (𝓝 0) := by
  have hargA :
      Tendsto (fun x : ℝ => a * x) atTop atTop :=
    tendsto_id.const_mul_atTop ha
  have hargB :
      Tendsto (fun x : ℝ => b * x) atTop atTop :=
    tendsto_id.const_mul_atTop hb
  have hA :
      Tendsto (fun x : ℝ => Real.arctan (a * x))
        atTop (𝓝 (Real.pi / 2)) :=
    tendsto_nhds_of_tendsto_nhdsWithin
      (Real.tendsto_arctan_atTop.comp hargA)
  have hB :
      Tendsto (fun x : ℝ => Real.arctan (b * x))
        atTop (𝓝 (Real.pi / 2)) :=
    tendsto_nhds_of_tendsto_nhdsWithin
      (Real.tendsto_arctan_atTop.comp hargB)
  have hInv :
      Tendsto (fun x : ℝ => (-1 : ℝ) / x)
        atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  simpa [angleProduct, negInv] using (hA.mul hB).mul hInv

private theorem targetKernel_integral_pos
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (∫ x in Ioi (0 : ℝ), targetKernel a b x ∂volume) =
      a * jValue a b + b * jValue b a := by
  have huv' :
      IntegrableOn (angleProduct a b * invSq)
        (Ioi (0 : ℝ)) volume := by
    exact (targetKernel_integrable a b ha hb).congr_fun
      (fun x _ => by
        simp [targetKernel, angleProduct, invSq, div_eq_mul_inv])
      measurableSet_Ioi
  have hu'v :=
    angleProductDeriv_mul_negInv_integrable a b ha hb
  have hibp :=
    integral_Ioi_mul_deriv_eq_deriv_mul
      (a := (0 : ℝ))
      (u := angleProduct a b)
      (u' := angleProductDeriv a b)
      (v := negInv)
      (v' := invSq)
      (fun x _ => angleProduct_hasDerivAt a b x)
      (fun x hx => negInv_hasDerivAt x hx.ne')
      huv' hu'v
      (angleProduct_mul_negInv_tendsto_zero a b)
      (angleProduct_mul_negInv_tendsto_atTop_zero a b ha hb)
  have hja : IntegrableOn (fun x : ℝ => a * jKernel a b x)
      (Ioi (0 : ℝ)) volume :=
    (jKernel_integrable a b ha).const_mul _
  have hjb : IntegrableOn (fun x : ℝ => b * jKernel b a x)
      (Ioi (0 : ℝ)) volume :=
    (jKernel_integrable b a hb).const_mul _
  have hderivIntegral :
      (∫ x in Ioi (0 : ℝ),
        angleProductDeriv a b x * negInv x ∂volume) =
        -(a * jValue a b + b * jValue b a) := by
    calc
      (∫ x in Ioi (0 : ℝ),
          angleProductDeriv a b x * negInv x ∂volume) =
          ∫ x in Ioi (0 : ℝ),
            -(a * jKernel a b x + b * jKernel b a x) ∂volume := by
            apply setIntegral_congr_fun measurableSet_Ioi
            intro x hx
            exact angleProductDeriv_mul_negInv_eq a b x hx.ne'
      _ = -(∫ x in Ioi (0 : ℝ),
            (a * jKernel a b x + b * jKernel b a x) ∂volume) := by
            rw [integral_neg]
      _ = -((∫ x in Ioi (0 : ℝ), a * jKernel a b x ∂volume) +
            ∫ x in Ioi (0 : ℝ), b * jKernel b a x ∂volume) := by
            rw [integral_add hja hjb]
      _ = -(a * jValue a b + b * jValue b a) := by
            rw [integral_const_mul, integral_const_mul]
            rfl
  have hibp' :
      (∫ x in Ioi (0 : ℝ), targetKernel a b x ∂volume) =
        0 - 0 -
          ∫ x in Ioi (0 : ℝ),
            angleProductDeriv a b x * negInv x ∂volume := by
    simpa [targetKernel, angleProduct, invSq, div_eq_mul_inv] using hibp
  rw [hibp', hderivIntegral]
  ring

private theorem targetKernel_integral_pos_logs
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (∫ x in Ioi (0 : ℝ), targetKernel a b x ∂volume) =
      (Real.pi / 2) *
        (a * Real.log ((a + b) / a) +
          b * Real.log ((a + b) / b)) := by
  rw [targetKernel_integral_pos a b ha hb,
    jValue_eq_jForm a b ha hb,
    jValue_eq_jForm b a hb ha]
  unfold jForm
  ring

private theorem realSign_mul_of_ne
    (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    Real.sign (a * b) = Real.sign a * Real.sign b := by
  rcases lt_or_gt_of_ne ha with haNeg | haPos
  · rcases lt_or_gt_of_ne hb with hbNeg | hbPos
    · rw [Real.sign_of_pos (mul_pos_of_neg_of_neg haNeg hbNeg),
        Real.sign_of_neg haNeg, Real.sign_of_neg hbNeg]
      norm_num
    · rw [Real.sign_of_neg (mul_neg_of_neg_of_pos haNeg hbPos),
        Real.sign_of_neg haNeg, Real.sign_of_pos hbPos]
      norm_num
  · rcases lt_or_gt_of_ne hb with hbNeg | hbPos
    · rw [Real.sign_of_neg (mul_neg_of_pos_of_neg haPos hbNeg),
        Real.sign_of_pos haPos, Real.sign_of_neg hbNeg]
      norm_num
    · rw [Real.sign_of_pos (mul_pos haPos hbPos),
        Real.sign_of_pos haPos, Real.sign_of_pos hbPos]
      norm_num

private theorem arctan_mul_eq_sign_mul_abs
    (a x : ℝ) (ha : a ≠ 0) :
    Real.arctan (a * x) =
      Real.sign a * Real.arctan (|a| * x) := by
  rcases lt_or_gt_of_ne ha with haNeg | haPos
  · rw [Real.sign_of_neg haNeg, abs_of_neg haNeg]
    have harg : a * x = -((-a) * x) := by ring
    rw [harg, Real.arctan_neg]
    ring
  · rw [Real.sign_of_pos haPos, abs_of_pos haPos, one_mul]

private theorem targetKernel_eq_sign_mul_abs
    (a b x : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    targetKernel a b x =
      Real.sign (a * b) * targetKernel |a| |b| x := by
  unfold targetKernel
  rw [realSign_mul_of_ne a b ha hb,
    arctan_mul_eq_sign_mul_abs a x ha,
    arctan_mul_eq_sign_mul_abs b x hb]
  ring

private theorem targetKernel_integral_eq_sign_abs
    (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    (∫ x in Ioi (0 : ℝ), targetKernel a b x ∂volume) =
      Real.sign (a * b) *
        ∫ x in Ioi (0 : ℝ), targetKernel |a| |b| x ∂volume := by
  calc
    (∫ x in Ioi (0 : ℝ), targetKernel a b x ∂volume) =
        ∫ x in Ioi (0 : ℝ),
          Real.sign (a * b) * targetKernel |a| |b| x ∂volume := by
          apply setIntegral_congr_fun measurableSet_Ioi
          intro x _
          exact targetKernel_eq_sign_mul_abs a b x ha hb
    _ = Real.sign (a * b) *
          ∫ x in Ioi (0 : ℝ), targetKernel |a| |b| x ∂volume := by
          rw [integral_const_mul]

private theorem I_eq_entropy_pos
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    I a b = Real.pi / 2 * entropyForm a b := by
  change
    (∫ x in Ioi (0 : ℝ), targetKernel a b x ∂volume) =
      Real.pi / 2 * entropyForm a b
  rw [targetKernel_integral_pos_logs a b ha hb,
    Real.log_div (add_pos ha hb).ne' ha.ne',
    Real.log_div (add_pos ha hb).ne' hb.ne']
  unfold entropyForm
  ring

private theorem I_eq_entropy_nonneg
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    I a b = Real.pi / 2 * entropyForm a b := by
  rcases ha.eq_or_lt with ha0 | ha
  · subst a
    simp [I, integrand, entropyForm]
  · rcases hb.eq_or_lt with hb0 | hb
    · subst b
      simp [I, integrand, entropyForm]
    · exact I_eq_entropy_pos a b ha hb

private theorem J_eq_log_formula
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    J a b = Real.pi / 2 * Real.log ((a + b) / a) := by
  change jValue a b = jForm a b
  exact jValue_eq_jForm a b ha hb

private theorem entropy_alpha_hasDerivAt
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    HasDerivAt
      (fun t : ℝ => Real.pi / 2 * entropyForm t b)
      (Real.pi / 2 * Real.log ((a + b) / a)) a := by
  have hsum :
      HasDerivAt
        (fun t : ℝ => (t + b) * Real.log (t + b))
        (Real.log (a + b) + 1) a := by
    simpa only [Function.comp_apply, one_mul, mul_one] using
      (Real.hasDerivAt_mul_log (add_pos ha hb).ne').comp a
        ((hasDerivAt_id a).add_const b)
  have hself :
      HasDerivAt
        (fun t : ℝ => t * Real.log t)
        (Real.log a + 1) a :=
    Real.hasDerivAt_mul_log ha.ne'
  have hcore :=
    (hsum.sub hself).sub_const (b * Real.log b)
  have hscaled := hcore.const_mul (Real.pi / 2)
  rw [Real.log_div (add_pos ha hb).ne' ha.ne']
  convert hscaled using 1 <;> ring

private theorem signType_sign_eq_realSign (x : ℝ) :
    (SignType.sign x : ℝ) = Real.sign x := by
  rcases lt_trichotomy x 0 with hx | hx | hx
  · rw [sign_neg hx, Real.sign_of_neg hx]
    norm_num
  · subst x
    simp
  · rw [sign_pos hx, Real.sign_of_pos hx]
    norm_num

-- Statement correction: the integrand is defined as 0 at x = 0, so the
-- intended limit is punctured rather than a full-neighborhood limit.
theorem gap1 (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    Tendsto (fun x : ℝ => integrand α β x)
      (nhdsWithin 0 ({0}ᶜ : Set ℝ)) (nhds (α * β)) := by
  have hinnerA :
      HasDerivAt (fun x : ℝ => α * x) α 0 := by
    simpa only [id_eq, mul_one] using
      (hasDerivAt_id (0 : ℝ)).const_mul α
  have hAderiv :
      HasDerivAt (fun x : ℝ => Real.arctan (α * x)) α 0 := by
    simpa using
      (Real.hasDerivAt_arctan (α * 0)).comp 0 hinnerA
  have hAslope :
      Tendsto
        (fun x : ℝ => x⁻¹ * Real.arctan (α * x))
        (nhdsWithin 0 ({0}ᶜ : Set ℝ)) (nhds α) := by
    simpa only [zero_add, mul_zero, Real.arctan_zero,
      sub_zero, smul_eq_mul] using hAderiv.tendsto_slope_zero
  have hinnerB :
      HasDerivAt (fun x : ℝ => β * x) β 0 := by
    simpa only [id_eq, mul_one] using
      (hasDerivAt_id (0 : ℝ)).const_mul β
  have hBderiv :
      HasDerivAt (fun x : ℝ => Real.arctan (β * x)) β 0 := by
    simpa using
      (Real.hasDerivAt_arctan (β * 0)).comp 0 hinnerB
  have hBslope :
      Tendsto
        (fun x : ℝ => x⁻¹ * Real.arctan (β * x))
        (nhdsWithin 0 ({0}ᶜ : Set ℝ)) (nhds β) := by
    simpa only [zero_add, mul_zero, Real.arctan_zero,
      sub_zero, smul_eq_mul] using hBderiv.tendsto_slope_zero
  apply (hAslope.mul hBslope).congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : x ≠ 0 := by simpa using hx
  unfold integrand
  field_simp [hx0]

theorem gap2 (α β x : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hx : x ≠ 0) :
    |integrand α β x| <
      Real.pi ^ 2 / 4 * (1 / x ^ 2) := by
  have hA :
      |Real.arctan (α * x)| < Real.pi / 2 :=
    abs_lt.2
      ⟨Real.neg_pi_div_two_lt_arctan (α * x),
        Real.arctan_lt_pi_div_two (α * x)⟩
  have hB :
      |Real.arctan (β * x)| < Real.pi / 2 :=
    abs_lt.2
      ⟨Real.neg_pi_div_two_lt_arctan (β * x),
        Real.arctan_lt_pi_div_two (β * x)⟩
  have hpi : 0 < Real.pi / 2 := by positivity
  have hprod :
      |Real.arctan (α * x)| * |Real.arctan (β * x)| <
        (Real.pi / 2) ^ 2 := by
    nlinarith [abs_nonneg (Real.arctan (α * x)),
      abs_nonneg (Real.arctan (β * x))]
  have hxsq : 0 < x ^ 2 := sq_pos_of_ne_zero hx
  unfold integrand
  rw [abs_div, abs_mul, abs_of_pos hxsq]
  have hdiv :=
    (div_lt_div_iff_of_pos_right hxsq).2 hprod
  convert hdiv using 1 <;>
    field_simp [hx] <;>
    ring

theorem gap3 :
    ContinuousOn (fun p : ℝ × ℝ => I p.1 p.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.Ici (0 : ℝ)) := by
  have hcont :
      Continuous
        (fun p : ℝ × ℝ =>
          Real.pi / 2 * entropyForm p.1 p.2) := by
    unfold entropyForm
    fun_prop
  apply hcont.continuousOn.congr
  intro p hp
  exact I_eq_entropy_nonneg p.1 p.2 hp.1 hp.2

theorem gap4 (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    deriv (fun a : ℝ => I a β) α = J α β := by
  have heq :
      (fun a : ℝ => I a β) =ᶠ[nhds α]
        fun a : ℝ => Real.pi / 2 * entropyForm a β := by
    filter_upwards [Ioi_mem_nhds hα] with a ha
    exact I_eq_entropy_pos a β ha hβ
  rw [heq.deriv_eq,
    (entropy_alpha_hasDerivAt α β hα hβ).deriv,
    J_eq_log_formula α β hα hβ]

theorem gap5 (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    deriv (fun b : ℝ => deriv (fun a : ℝ => I a b) α) β =
      deriv (fun b : ℝ => J α b) β := by
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [Ioi_mem_nhds hβ] with b hb
  exact gap4 α b hα hb

theorem gap6 (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    deriv (fun b : ℝ => J α b) β = K α β := by
  change
    deriv (jValue α) β =
      ∫ x in Ioi (0 : ℝ), mixedKernel α β x ∂volume
  exact (jValue_hasDerivAt α β hα).deriv

theorem gap7 (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    deriv (fun b : ℝ => deriv (fun a : ℝ => I a b) α) β =
      K α β := by
  rw [gap5 α β hα hβ, gap6 α β hα hβ]

theorem gap8 (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (hαβ : α ≠ β) :
    K α β =
      α ^ 2 / (α ^ 2 - β ^ 2) *
          (∫ x in Set.Ioi (0 : ℝ), 1 / (1 + α ^ 2 * x ^ 2)) -
        β ^ 2 / (α ^ 2 - β ^ 2) *
          ∫ x in Set.Ioi (0 : ℝ), 1 / (1 + β ^ 2 * x ^ 2) := by
  change
    (∫ x in Ioi (0 : ℝ), mixedKernel α β x ∂volume) =
      α ^ 2 / (α ^ 2 - β ^ 2) *
          (∫ x in Ioi (0 : ℝ), oneKernel α x ∂volume) -
        β ^ 2 / (α ^ 2 - β ^ 2) *
          ∫ x in Ioi (0 : ℝ), oneKernel β x ∂volume
  calc
    (∫ x in Ioi (0 : ℝ), mixedKernel α β x ∂volume) =
        ∫ x in Ioi (0 : ℝ),
          (α ^ 2 / (α ^ 2 - β ^ 2) * oneKernel α x -
            β ^ 2 / (α ^ 2 - β ^ 2) * oneKernel β x) ∂volume := by
          apply setIntegral_congr_fun measurableSet_Ioi
          intro x _
          exact mixedKernel_eq_partialFractions α β x hα hβ hαβ
    _ = α ^ 2 / (α ^ 2 - β ^ 2) *
          (∫ x in Ioi (0 : ℝ), oneKernel α x ∂volume) -
        β ^ 2 / (α ^ 2 - β ^ 2) *
          ∫ x in Ioi (0 : ℝ), oneKernel β x ∂volume := by
          rw [integral_sub
            ((oneKernel_integrable α hα).const_mul _)
            ((oneKernel_integrable β hβ).const_mul _),
            integral_const_mul, integral_const_mul]

theorem gap9 (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    K α β = Real.pi / (2 * (α + β)) := by
  change
    (∫ x in Ioi (0 : ℝ), mixedKernel α β x ∂volume) =
      Real.pi / (2 * (α + β))
  exact mixedKernel_integral α β hα hβ

theorem gap10 (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    deriv (fun b : ℝ => deriv (fun a : ℝ => I a b) α) β =
      Real.pi / (2 * (α + β)) := by
  rw [gap7 α β hα hβ, gap9 α β hα hβ]

theorem gap11 (α : ℝ) (hα : 0 < α) :
    ∃ C : ℝ, ∀ β : ℝ, 0 < β →
      deriv (fun a : ℝ => I a β) α =
        Real.pi / 2 * Real.log (α + β) + C := by
  refine ⟨-(Real.pi / 2 * Real.log α), ?_⟩
  intro β hβ
  rw [gap4 α β hα hβ, J_eq_log_formula α β hα hβ,
    Real.log_div (add_pos hα hβ).ne' hα.ne']
  ring

theorem gap12 (α : ℝ) (hα : 0 < α) :
    J α 0 = 0 := by
  unfold J
  simp

theorem gap13 (α : ℝ) (hα : 0 < α) :
    ∃ C : ℝ,
      (∀ β : ℝ, 0 < β →
        deriv (fun a : ℝ => I a β) α =
          Real.pi / 2 * Real.log (α + β) + C) ∧
      J α 0 = Real.pi / 2 * Real.log α + C := by
  refine ⟨-(Real.pi / 2 * Real.log α), ?_, ?_⟩
  · intro β hβ
    rw [gap4 α β hα hβ, J_eq_log_formula α β hα hβ,
      Real.log_div (add_pos hα hβ).ne' hα.ne']
    ring
  · rw [gap12 α hα]
    ring

theorem gap14 (α : ℝ) (hα : 0 < α) :
    ∃ C : ℝ,
      (∀ β : ℝ, 0 < β →
        deriv (fun a : ℝ => I a β) α =
          Real.pi / 2 * Real.log (α + β) + C) ∧
      0 = Real.pi / 2 * Real.log α + C := by
  rcases gap13 α hα with ⟨C, hC, h0⟩
  refine ⟨C, hC, ?_⟩
  simpa [gap12 α hα] using h0

theorem gap15 (α : ℝ) (hα : 0 < α) :
    ∃ C : ℝ,
      (∀ β : ℝ, 0 < β →
        deriv (fun a : ℝ => I a β) α =
          Real.pi / 2 * Real.log (α + β) + C) ∧
      C = -(Real.pi / 2 * Real.log α) := by
  rcases gap14 α hα with ⟨C, hC, h0⟩
  exact ⟨C, hC, by linarith⟩

theorem gap16 (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    deriv (fun a : ℝ => I a β) α =
      Real.pi / 2 * Real.log ((α + β) / α) := by
  rcases gap15 α hα with ⟨C, hC, hCeq⟩
  rw [hC β hβ, hCeq, Real.log_div (by positivity) hα.ne']
  ring

theorem gap17 (β : ℝ) (hβ : 0 < β) :
    ∃ C₁ : ℝ, ∀ α : ℝ, 0 < α →
      I α β = Real.pi / 2 * alphaPrimitive α β + C₁ := by
  refine ⟨-(Real.pi / 2 * β * Real.log β), ?_⟩
  intro α hα
  rw [I_eq_entropy_pos α β hα hβ]
  unfold entropyForm alphaPrimitive
  ring

theorem gap18 (β : ℝ) (hβ : 0 ≤ β) :
    I 0 β = 0 := by
  unfold I integrand
  simp

theorem gap19 (β : ℝ) (hβ : 0 < β) :
    ∃ C₁ : ℝ,
      (∀ α : ℝ, 0 < α →
        I α β = Real.pi / 2 * alphaPrimitive α β + C₁) ∧
      I 0 β = Real.pi / 2 * β * Real.log β + C₁ := by
  refine ⟨-(Real.pi / 2 * β * Real.log β), ?_, ?_⟩
  · intro α hα
    rw [I_eq_entropy_pos α β hα hβ]
    unfold entropyForm alphaPrimitive
    ring
  · rw [gap18 β hβ.le]
    ring

theorem gap20 (β : ℝ) (hβ : 0 < β) :
    ∃ C₁ : ℝ,
      (∀ α : ℝ, 0 < α →
        I α β = Real.pi / 2 * alphaPrimitive α β + C₁) ∧
      0 = Real.pi / 2 * β * Real.log β + C₁ := by
  rcases gap19 β hβ with ⟨C, hC, h0⟩
  refine ⟨C, hC, ?_⟩
  simpa [gap18 β hβ.le] using h0

theorem gap21 (β : ℝ) (hβ : 0 < β) :
    ∃ C₁ : ℝ,
      (∀ α : ℝ, 0 < α →
        I α β = Real.pi / 2 * alphaPrimitive α β + C₁) ∧
      C₁ = -(Real.pi / 2 * β * Real.log β) := by
  rcases gap20 β hβ with ⟨C, hC, h0⟩
  exact ⟨C, hC, by linarith⟩

theorem gap22 (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    I α β = Real.pi / 2 * entropyForm α β :=
  I_eq_entropy_pos α β hα hβ

theorem gap23 (α β : ℝ) :
    I α β =
      if α * β = 0 then 0
      else (SignType.sign (α * β) : ℝ) * Real.pi / 2 *
        entropyForm |α| |β| := by
  by_cases hprod : α * β = 0
  · rw [if_pos hprod]
    rcases mul_eq_zero.mp hprod with hα | hβ
    · subst α
      simp [I, integrand]
    · subst β
      simp [I, integrand]
  · rw [if_neg hprod]
    have hα : α ≠ 0 := by
      intro h
      apply hprod
      simp [h]
    have hβ : β ≠ 0 := by
      intro h
      apply hprod
      simp [h]
    have haPos : 0 < |α| := abs_pos.mpr hα
    have hbPos : 0 < |β| := abs_pos.mpr hβ
    change
      (∫ x in Ioi (0 : ℝ), targetKernel α β x ∂volume) =
        (SignType.sign (α * β) : ℝ) * Real.pi / 2 *
          entropyForm |α| |β|
    rw [targetKernel_integral_eq_sign_abs α β hα hβ]
    have hpos := I_eq_entropy_pos |α| |β| haPos hbPos
    change
      (∫ x in Ioi (0 : ℝ), targetKernel |α| |β| x ∂volume) =
        Real.pi / 2 * entropyForm |α| |β| at hpos
    rw [hpos, signType_sign_eq_realSign]
    ring

end

end ProofGap.Exercise3801
