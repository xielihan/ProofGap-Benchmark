import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3800

noncomputable section

open Filter MeasureTheory Set
open scoped Interval Topology

def baseIntegrand (β α x : ℝ) : ℝ :=
  Real.log (1 + α ^ 2 * x ^ 2) / (β ^ 2 + x ^ 2)

def Iβ (β α : ℝ) : ℝ :=
  ∫ x in Set.Ioi (0 : ℝ), baseIntegrand β α x

def logarithmicIntegrand (α β x : ℝ) : ℝ :=
  Real.log (α ^ 2 + x ^ 2) / (β ^ 2 + x ^ 2)

def J (β α : ℝ) : ℝ :=
  ∫ x in Set.Ioi (0 : ℝ), logarithmicIntegrand α β x

private def cauchyKernel (c x : ℝ) : ℝ :=
  1 / (c ^ 2 + x ^ 2)

private def cauchyPrimitive (c x : ℝ) : ℝ :=
  Real.arctan (x / c) / c

private theorem cauchyPrimitive_hasDerivAt
    (c x : ℝ) (hc : 0 < c) :
    HasDerivAt (cauchyPrimitive c) (cauchyKernel c x) x := by
  have hinner :
      HasDerivAt (fun y : ℝ => y / c) (1 / c) x := by
    simpa only [one_div] using (hasDerivAt_id x).div_const c
  have h := ((Real.hasDerivAt_arctan (x / c)).comp x hinner).div_const c
  unfold cauchyPrimitive cauchyKernel
  convert h using 1
  field_simp [hc.ne']

private theorem cauchyPrimitive_tendsto
    (c : ℝ) (hc : 0 < c) :
    Tendsto (cauchyPrimitive c) atTop
      (𝓝 (Real.pi / (2 * c))) := by
  have harg :
      Tendsto (fun x : ℝ => x / c) atTop atTop :=
    by
      simpa [div_eq_mul_inv, mul_comm] using
        tendsto_id.const_mul_atTop (one_div_pos.mpr hc)
  have hatan :
      Tendsto (fun x : ℝ => Real.arctan (x / c))
        atTop (𝓝 (Real.pi / 2)) :=
    tendsto_nhds_of_tendsto_nhdsWithin
      (Real.tendsto_arctan_atTop.comp harg)
  simpa only [cauchyPrimitive, div_div] using hatan.div_const c

private theorem cauchyKernel_nonneg
    (c x : ℝ) :
    0 ≤ cauchyKernel c x := by
  unfold cauchyKernel
  positivity

private theorem cauchyKernel_integrable
    (c : ℝ) (hc : 0 < c) :
    IntegrableOn (cauchyKernel c) (Ioi (0 : ℝ)) volume := by
  exact integrableOn_Ioi_deriv_of_nonneg
    (by
      unfold cauchyPrimitive
      fun_prop)
    (fun x _ => cauchyPrimitive_hasDerivAt c x hc)
    (fun x _ => cauchyKernel_nonneg c x)
    (cauchyPrimitive_tendsto c hc)

private theorem cauchyKernel_integral
    (c : ℝ) (hc : 0 < c) :
    (∫ x in Ioi (0 : ℝ), cauchyKernel c x ∂volume) =
      Real.pi / (2 * c) := by
  have h :=
    integral_Ioi_of_hasDerivAt_of_tendsto
      (by
        unfold cauchyPrimitive
        fun_prop)
      (fun x _ => cauchyPrimitive_hasDerivAt c x hc)
      (cauchyKernel_integrable c hc)
      (cauchyPrimitive_tendsto c hc)
  simpa [cauchyPrimitive] using h

private def logKernel (a b x : ℝ) : ℝ :=
  Real.log (1 + a ^ 2 * x ^ 2) / (b ^ 2 + x ^ 2)

private theorem logKernel_nonneg
    (a b x : ℝ) :
    0 ≤ logKernel a b x := by
  unfold logKernel
  exact div_nonneg
    (Real.log_nonneg (by nlinarith [mul_nonneg (sq_nonneg a) (sq_nonneg x)]))
    (by positivity)

private theorem logKernel_continuous
    (a b : ℝ) (hb : b ≠ 0) :
    Continuous (logKernel a b) := by
  unfold logKernel
  apply Continuous.div
  · apply Continuous.log
    · fun_prop
    · intro x
      positivity
  · fun_prop
  · intro x
    have : 0 < b ^ 2 + x ^ 2 := by positivity
    exact this.ne'

private theorem logKernel_integrable
    (a b : ℝ) (hb : b ≠ 0) :
    IntegrableOn (logKernel a b) (Ioi (0 : ℝ)) volume := by
  have hcompact :
      IntegrableOn (logKernel a b) (Ioc (0 : ℝ) 1) volume :=
    ((logKernel_continuous a b hb).intervalIntegrable (a := (0 : ℝ)) (b := 1)).1
  have htailMajor :
      IntegrableOn
        (fun x : ℝ => 4 * (1 + a ^ 2) ^ (1 / 4 : ℝ) *
          x ^ (-3 / 2 : ℝ))
        (Ioi (1 : ℝ)) volume :=
    (integrableOn_Ioi_rpow_of_lt
      (a := (-3 / 2 : ℝ)) (c := 1) (by norm_num) zero_lt_one).const_mul _
  have htail :
      IntegrableOn (logKernel a b) (Ioi (1 : ℝ)) volume := by
    apply htailMajor.mono'
    · exact (logKernel_continuous a b hb).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      change (1 : ℝ) < x at hx
      have hxpos : 0 < x := zero_lt_one.trans hx
      have harg : 0 ≤ 1 + a ^ 2 * x ^ 2 := by positivity
      have hlognon :
          0 ≤ Real.log (1 + a ^ 2 * x ^ 2) :=
        Real.log_nonneg (by nlinarith [mul_nonneg (sq_nonneg a) (sq_nonneg x)])
      have hden : 0 < b ^ 2 + x ^ 2 := by positivity
      have hdenLower : x ^ 2 ≤ b ^ 2 + x ^ 2 := by
        nlinarith [sq_nonneg b]
      have hxSquare : 1 ≤ x ^ 2 := by
        nlinarith [mul_nonneg
          (by linarith : 0 ≤ x - 1)
          (by linarith : 0 ≤ x + 1)]
      have hbase :
          1 + a ^ 2 * x ^ 2 ≤ (1 + a ^ 2) * x ^ 2 := by
        nlinarith
      have hrpow :
          (1 + a ^ 2 * x ^ 2) ^ (1 / 4 : ℝ) ≤
            (1 + a ^ 2) ^ (1 / 4 : ℝ) * x ^ (1 / 2 : ℝ) := by
        calc
          (1 + a ^ 2 * x ^ 2) ^ (1 / 4 : ℝ) ≤
              ((1 + a ^ 2) * x ^ 2) ^ (1 / 4 : ℝ) :=
            Real.rpow_le_rpow harg hbase (by norm_num)
          _ = (1 + a ^ 2) ^ (1 / 4 : ℝ) *
              x ^ (1 / 2 : ℝ) := by
            rw [Real.mul_rpow (by positivity) (sq_nonneg x)]
            rw [← Real.rpow_natCast x 2, ← Real.rpow_mul hxpos.le]
            norm_num
      have hlog :
          Real.log (1 + a ^ 2 * x ^ 2) ≤
            4 * (1 + a ^ 2) ^ (1 / 4 : ℝ) *
              x ^ (1 / 2 : ℝ) := by
        calc
          Real.log (1 + a ^ 2 * x ^ 2) ≤
              (1 + a ^ 2 * x ^ 2) ^ (1 / 4 : ℝ) /
                (1 / 4 : ℝ) :=
            Real.log_le_rpow_div harg (by norm_num)
          _ = 4 * (1 + a ^ 2 * x ^ 2) ^ (1 / 4 : ℝ) := by ring
          _ ≤ 4 * ((1 + a ^ 2) ^ (1 / 4 : ℝ) *
              x ^ (1 / 2 : ℝ)) := by gcongr
          _ = _ := by ring
      rw [Real.norm_eq_abs, abs_of_nonneg (logKernel_nonneg a b x)]
      unfold logKernel
      have hdiv :
          Real.log (1 + a ^ 2 * x ^ 2) / (b ^ 2 + x ^ 2) ≤
            (4 * (1 + a ^ 2) ^ (1 / 4 : ℝ) *
              x ^ (1 / 2 : ℝ)) / x ^ 2 := by
        exact div_le_div₀
          (by positivity) hlog (by positivity) hdenLower
      calc
        Real.log (1 + a ^ 2 * x ^ 2) / (b ^ 2 + x ^ 2) ≤
            (4 * (1 + a ^ 2) ^ (1 / 4 : ℝ) *
              x ^ (1 / 2 : ℝ)) / x ^ 2 := hdiv
        _ = 4 * (1 + a ^ 2) ^ (1 / 4 : ℝ) *
              x ^ (-3 / 2 : ℝ) := by
          calc
            4 * (1 + a ^ 2) ^ (1 / 4 : ℝ) *
                x ^ (1 / 2 : ℝ) / x ^ 2 =
                4 * (1 + a ^ 2) ^ (1 / 4 : ℝ) *
                  (x ^ (1 / 2 : ℝ) / x ^ (2 : ℝ)) := by
                    rw [← Real.rpow_natCast x 2]
                    ring
            _ = 4 * (1 + a ^ 2) ^ (1 / 4 : ℝ) *
                  x ^ ((1 / 2 : ℝ) - 2) := by
                    rw [Real.rpow_sub hxpos]
            _ = _ := by norm_num
  have hunion := hcompact.union htail
  refine hunion.mono_set ?_
  intro x hx
  by_cases hx1 : x ≤ 1
  · exact Or.inl ⟨hx, hx1⟩
  · exact Or.inr (lt_of_not_ge hx1)

private def squareMomentKernel (c x : ℝ) : ℝ :=
  x ^ 2 / (c ^ 2 + x ^ 2) ^ 2

private def squareMomentPrimitive (c x : ℝ) : ℝ :=
  Real.arctan (x / c) / (2 * c) -
    x / (2 * (c ^ 2 + x ^ 2))

private theorem squareMomentPrimitive_hasDerivAt
    (c x : ℝ) (hc : 0 < c) :
    HasDerivAt (squareMomentPrimitive c)
      (squareMomentKernel c x) x := by
  have hinner :
      HasDerivAt (fun y : ℝ => y / c) (1 / c) x := by
    simpa only [one_div] using (hasDerivAt_id x).div_const c
  have hatan :=
    ((Real.hasDerivAt_arctan (x / c)).comp x hinner).div_const (2 * c)
  have hden :
      HasDerivAt (fun y : ℝ => 2 * (c ^ 2 + y ^ 2))
        (4 * x) x := by
    convert
      ((hasDerivAt_const x (c ^ 2)).add
        ((hasDerivAt_id x).pow 2)).const_mul 2 using 1 <;>
      simp only [id_eq] <;> ring
  have hquot :=
    (hasDerivAt_id x).div hden
      (by positivity : 2 * (c ^ 2 + x ^ 2) ≠ 0)
  simp only [id_eq] at hquot
  unfold squareMomentPrimitive squareMomentKernel
  convert hatan.sub hquot using 1
  field_simp [hc.ne']
  ring

private theorem squareMomentPrimitive_tendsto
    (c : ℝ) (hc : 0 < c) :
    Tendsto (squareMomentPrimitive c) atTop
      (𝓝 (Real.pi / (4 * c))) := by
  have harg :
      Tendsto (fun x : ℝ => x / c) atTop atTop := by
    simpa [div_eq_mul_inv, mul_comm] using
      tendsto_id.const_mul_atTop (one_div_pos.mpr hc)
  have hatan :
      Tendsto (fun x : ℝ => Real.arctan (x / c) / (2 * c))
        atTop (𝓝 (Real.pi / (4 * c))) := by
    have h :=
      (tendsto_nhds_of_tendsto_nhdsWithin
        (Real.tendsto_arctan_atTop.comp harg)).div_const (2 * c)
    convert h using 1 <;> ring
  have hratio :
      Tendsto (fun x : ℝ => x / (c ^ 2 + x ^ 2))
        atTop (𝓝 0) := by
    have hden :
        Tendsto (fun x : ℝ => c ^ 2 / x + x) atTop atTop :=
      (tendsto_const_nhds.div_atTop tendsto_id).add_atTop tendsto_id
    have hbase :
        Tendsto (fun x : ℝ => 1 / (c ^ 2 / x + x))
          atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hden
    apply hbase.congr'
    filter_upwards [eventually_ne_atTop (0 : ℝ)] with x hx
    field_simp
  have hsecond :
      Tendsto (fun x : ℝ => x / (2 * (c ^ 2 + x ^ 2)))
        atTop (𝓝 0) := by
    have heq :
        (fun x : ℝ => x / (2 * (c ^ 2 + x ^ 2))) =
          (fun x : ℝ => (x / (c ^ 2 + x ^ 2)) / 2) := by
      funext x
      have hden : c ^ 2 + x ^ 2 ≠ 0 := by positivity
      field_simp [hden]
    rw [heq]
    simpa using hratio.div_const 2
  simpa only [squareMomentPrimitive, sub_zero] using hatan.sub hsecond

private theorem squareMomentPrimitive_continuous
    (c : ℝ) (hc : 0 < c) :
    Continuous (squareMomentPrimitive c) := by
  unfold squareMomentPrimitive
  apply Continuous.sub
  · apply Continuous.div_const
    apply Real.continuous_arctan.comp
    fun_prop
  · apply Continuous.div
    · fun_prop
    · fun_prop
    · intro x
      positivity

private theorem squareMomentKernel_nonneg
    (c x : ℝ) :
    0 ≤ squareMomentKernel c x := by
  unfold squareMomentKernel
  positivity

private theorem squareMomentKernel_integrable
    (c : ℝ) (hc : 0 < c) :
    IntegrableOn (squareMomentKernel c) (Ioi (0 : ℝ)) volume := by
  exact integrableOn_Ioi_deriv_of_nonneg
    (squareMomentPrimitive_continuous c hc).continuousAt.continuousWithinAt
    (fun x _ => squareMomentPrimitive_hasDerivAt c x hc)
    (fun x _ => squareMomentKernel_nonneg c x)
    (squareMomentPrimitive_tendsto c hc)

private theorem squareMomentKernel_integral
    (c : ℝ) (hc : 0 < c) :
    (∫ x in Ioi (0 : ℝ), squareMomentKernel c x ∂volume) =
      Real.pi / (4 * c) := by
  have h :=
    integral_Ioi_of_hasDerivAt_of_tendsto
      (squareMomentPrimitive_continuous c hc).continuousAt.continuousWithinAt
      (fun x _ => squareMomentPrimitive_hasDerivAt c x hc)
      (squareMomentKernel_integrable c hc)
      (squareMomentPrimitive_tendsto c hc)
  simpa [squareMomentPrimitive] using h

private def derivativeKernel (a b x : ℝ) : ℝ :=
  2 * a * x ^ 2 /
    ((b ^ 2 + x ^ 2) * (1 + a ^ 2 * x ^ 2))

private theorem derivativeKernel_nonneg
    (a b x : ℝ) (ha : 0 ≤ a) :
    0 ≤ derivativeKernel a b x := by
  unfold derivativeKernel
  positivity

private theorem derivativeKernel_continuous
    (a b : ℝ) (hb : b ≠ 0) :
    Continuous (derivativeKernel a b) := by
  unfold derivativeKernel
  apply Continuous.div
  · fun_prop
  · fun_prop
  · intro x
    have h₁ : 0 < b ^ 2 + x ^ 2 := by positivity
    have h₂ : 0 < 1 + a ^ 2 * x ^ 2 := by positivity
    exact mul_ne_zero h₁.ne' h₂.ne'

private theorem derivativeKernel_eq_partialFractions
    (a b x : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hab : a * b ≠ 1) :
    derivativeKernel a b x =
      (2 * a / (1 - a ^ 2 * b ^ 2)) *
        ((1 / a ^ 2) * cauchyKernel (1 / a) x -
          b ^ 2 * cauchyKernel b x) := by
  unfold derivativeKernel cauchyKernel
  have h₁ : b ^ 2 + x ^ 2 ≠ 0 := by positivity
  have h₂ : 1 + a ^ 2 * x ^ 2 ≠ 0 := by positivity
  have h₃ : (1 / a) ^ 2 + x ^ 2 ≠ 0 := by positivity
  have hfactor : 1 - a ^ 2 * b ^ 2 ≠ 0 := by
    intro h
    have hsquare : (a * b) ^ 2 = 1 := by nlinarith
    have hpos : 0 < a * b := mul_pos ha hb
    have : a * b = 1 := by nlinarith
    exact hab this
  field_simp [ha.ne', h₁, h₂, h₃, hfactor]
  ring

private theorem derivativeKernel_eq_squareMoment
    (a b x : ℝ) (ha : 0 < a) (hab : a * b = 1) :
    derivativeKernel a b x =
      (2 / a) * squareMomentKernel b x := by
  have hb : b = 1 / a := by
    apply (eq_div_iff ha.ne').2
    linarith
  unfold derivativeKernel squareMomentKernel
  rw [hb]
  have h₁ : (1 / a) ^ 2 + x ^ 2 ≠ 0 := by positivity
  have h₂ : 1 + a ^ 2 * x ^ 2 ≠ 0 := by positivity
  field_simp [ha.ne', h₁, h₂]

private theorem derivativeKernel_integrable
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    IntegrableOn (derivativeKernel a b) (Ioi (0 : ℝ)) volume := by
  by_cases hab : a * b = 1
  · have hmajor :
        IntegrableOn
          (fun x : ℝ => (2 / a) * squareMomentKernel b x)
          (Ioi (0 : ℝ)) volume :=
      (squareMomentKernel_integrable b hb).const_mul _
    exact hmajor.congr_fun
      (fun x _ => (derivativeKernel_eq_squareMoment a b x ha hab).symm)
      measurableSet_Ioi
  · have haInv : 0 < 1 / a := one_div_pos.mpr ha
    have hcomb :
        IntegrableOn
          (fun x : ℝ =>
            (2 * a / (1 - a ^ 2 * b ^ 2)) *
              ((1 / a ^ 2) * cauchyKernel (1 / a) x -
                b ^ 2 * cauchyKernel b x))
          (Ioi (0 : ℝ)) volume :=
      (((cauchyKernel_integrable (1 / a) haInv).const_mul
        (1 / a ^ 2)).sub
        ((cauchyKernel_integrable b hb).const_mul (b ^ 2))).const_mul _
    exact hcomb.congr_fun
      (fun x _ =>
        (derivativeKernel_eq_partialFractions a b x ha hb hab).symm)
      measurableSet_Ioi

private theorem derivativeKernel_integral
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (∫ x in Ioi (0 : ℝ), derivativeKernel a b x ∂volume) =
      Real.pi / (1 + a * b) := by
  by_cases hab : a * b = 1
  · calc
      (∫ x in Ioi (0 : ℝ), derivativeKernel a b x ∂volume) =
          ∫ x in Ioi (0 : ℝ),
            (2 / a) * squareMomentKernel b x ∂volume := by
            apply setIntegral_congr_fun measurableSet_Ioi
            intro x _
            exact derivativeKernel_eq_squareMoment a b x ha hab
      _ = (2 / a) *
          ∫ x in Ioi (0 : ℝ), squareMomentKernel b x ∂volume := by
            rw [integral_const_mul]
      _ = (2 / a) * (Real.pi / (4 * b)) := by
            rw [squareMomentKernel_integral b hb]
      _ = Real.pi / (1 + a * b) := by
            rw [hab]
            have habpos : 0 < a * b := mul_pos ha hb
            field_simp [ha.ne', hb.ne']
            nlinarith
  · have haInv : 0 < 1 / a := one_div_pos.mpr ha
    have hfactor : 1 - a ^ 2 * b ^ 2 ≠ 0 := by
      intro h
      have hsquare : (a * b) ^ 2 = 1 := by nlinarith
      have hpos : 0 < a * b := mul_pos ha hb
      have : a * b = 1 := by nlinarith
      exact hab this
    calc
      (∫ x in Ioi (0 : ℝ), derivativeKernel a b x ∂volume) =
          ∫ x in Ioi (0 : ℝ),
            (2 * a / (1 - a ^ 2 * b ^ 2)) *
              ((1 / a ^ 2) * cauchyKernel (1 / a) x -
                b ^ 2 * cauchyKernel b x) ∂volume := by
            apply setIntegral_congr_fun measurableSet_Ioi
            intro x _
            exact derivativeKernel_eq_partialFractions a b x ha hb hab
      _ = (2 * a / (1 - a ^ 2 * b ^ 2)) *
          ((1 / a ^ 2) *
              ∫ x in Ioi (0 : ℝ), cauchyKernel (1 / a) x ∂volume -
            b ^ 2 *
              ∫ x in Ioi (0 : ℝ), cauchyKernel b x ∂volume) := by
            rw [integral_const_mul]
            rw [integral_sub
              ((cauchyKernel_integrable (1 / a) haInv).const_mul _)
              ((cauchyKernel_integrable b hb).const_mul _)]
            rw [integral_const_mul, integral_const_mul]
      _ = (2 * a / (1 - a ^ 2 * b ^ 2)) *
          ((1 / a ^ 2) * (Real.pi / (2 * (1 / a))) -
            b ^ 2 * (Real.pi / (2 * b))) := by
            rw [cauchyKernel_integral (1 / a) haInv,
              cauchyKernel_integral b hb]
      _ = Real.pi / (1 + a * b) := by
            have hsum : 1 + a * b ≠ 0 := by positivity
            field_simp [ha.ne', hb.ne', hfactor, hsum]
            ring

private theorem logKernel_hasDerivAt
    (a b x : ℝ) (hb : b ≠ 0) :
    HasDerivAt (fun c : ℝ => logKernel c b x)
      (derivativeKernel a b x) a := by
  have hinner :
      HasDerivAt (fun c : ℝ => 1 + c ^ 2 * x ^ 2)
        (2 * a * x ^ 2) a := by
    convert
      (hasDerivAt_const a 1).add
        (((hasDerivAt_id a).pow 2).mul_const (x ^ 2)) using 1 <;>
      simp only [id_eq] <;> ring
  have hlog :=
    (Real.hasDerivAt_log
      (by positivity : 1 + a ^ 2 * x ^ 2 ≠ 0)).comp a hinner
  have h := hlog.div_const (b ^ 2 + x ^ 2)
  unfold logKernel derivativeKernel
  convert h using 1
  have h₁ : 1 + a ^ 2 * x ^ 2 ≠ 0 := by positivity
  have h₂ : b ^ 2 + x ^ 2 ≠ 0 := by positivity
  field_simp [h₁, h₂]

private theorem norm_derivativeKernel_le_local
    (a b c x : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hc : c ∈ Ioo (a / 2) (3 * a / 2)) :
    ‖derivativeKernel c b x‖ ≤
      (4 / a) * cauchyKernel b x := by
  have hcpos : 0 < c := by
    change a / 2 < c ∧ c < 3 * a / 2 at hc
    linarith
  have hB : 0 < b ^ 2 + x ^ 2 := by positivity
  have hQ : 0 < 1 + c ^ 2 * x ^ 2 := by positivity
  have hac : a * c ≤ 2 * c ^ 2 := by
    have : a ≤ 2 * c := by
      change a / 2 < c ∧ c < 3 * a / 2 at hc
      linarith
    nlinarith [mul_le_mul_of_nonneg_right this hcpos.le]
  have hacx :
      a * c * x ^ 2 ≤ 2 * c ^ 2 * x ^ 2 :=
    mul_le_mul_of_nonneg_right hac (sq_nonneg x)
  rw [Real.norm_eq_abs,
    abs_of_nonneg (derivativeKernel_nonneg c b x hcpos.le)]
  unfold derivativeKernel cauchyKernel
  apply (div_le_iff₀ (mul_pos hB hQ)).2
  field_simp [ha.ne', hB.ne', hQ.ne']
  nlinarith

private def auxValue (b a : ℝ) : ℝ :=
  ∫ x in Ioi (0 : ℝ), logKernel a b x ∂volume

private theorem auxValue_hasDerivAt
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    HasDerivAt (auxValue b)
      (Real.pi / (1 + a * b)) a := by
  let μ : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
  let s : Set ℝ := Ioo (a / 2) (3 * a / 2)
  have hs : s ∈ 𝓝 a := by
    apply Ioo_mem_nhds
    · dsimp [s]
      linarith
    · dsimp [s]
      linarith
  have hmeas :
      ∀ᶠ c in 𝓝 a,
        AEStronglyMeasurable (logKernel c b) μ :=
    Filter.Eventually.of_forall fun c =>
      (logKernel_continuous c b hb.ne').aestronglyMeasurable
  have hderivMeas :
      AEStronglyMeasurable (derivativeKernel a b) μ :=
    (derivativeKernel_continuous a b hb.ne').aestronglyMeasurable
  have hbound :
      ∀ᵐ x ∂μ, ∀ c ∈ s,
        ‖derivativeKernel c b x‖ ≤
          (4 / a) * cauchyKernel b x := by
    filter_upwards with x
    exact fun c hc =>
      norm_derivativeKernel_le_local a b c x ha hb hc
  have hdiff :
      ∀ᵐ x ∂μ, ∀ c ∈ s,
        HasDerivAt (fun d : ℝ => logKernel d b x)
          (derivativeKernel c b x) c := by
    filter_upwards with x
    exact fun c _ => logKernel_hasDerivAt c b x hb.ne'
  have hmajor :
      Integrable ((fun x : ℝ => (4 / a) * cauchyKernel b x)) μ := by
    change IntegrableOn
      (fun x : ℝ => (4 / a) * cauchyKernel b x)
      (Ioi (0 : ℝ)) volume
    exact (cauchyKernel_integrable b hb).const_mul _
  have hmain :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := μ) (F := fun c x => logKernel c b x)
      (F' := fun c x => derivativeKernel c b x)
      hs hmeas (logKernel_integrable a b hb.ne')
      hderivMeas hbound hmajor hdiff
  rw [derivativeKernel_integral a b ha hb] at hmain
  simpa only [auxValue, μ] using hmain.2

private theorem logKernel_param_continuous
    (b x : ℝ) (hb : b ≠ 0) :
    Continuous (fun a : ℝ => logKernel a b x) := by
  unfold logKernel
  apply Continuous.div_const
  apply Continuous.log
  · fun_prop
  · intro a
    positivity

private theorem auxValue_tendsto_zero
    (b : ℝ) (hb : 0 < b) :
    Tendsto (auxValue b)
      (𝓝[Set.Ici (0 : ℝ)] (0 : ℝ)) (𝓝 0) := by
  let μ : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
  have hmeas :
      ∀ᶠ a in 𝓝[Set.Ici (0 : ℝ)] (0 : ℝ),
        AEStronglyMeasurable (logKernel a b) μ :=
    Filter.Eventually.of_forall fun a =>
      (logKernel_continuous a b hb.ne').aestronglyMeasurable
  have haNonneg :
      ∀ᶠ a in 𝓝[Set.Ici (0 : ℝ)] (0 : ℝ), 0 ≤ a :=
    self_mem_nhdsWithin
  have haLt :
      ∀ᶠ a in 𝓝[Set.Ici (0 : ℝ)] (0 : ℝ), a < 1 :=
    by
      have h :
          ∀ᶠ a in 𝓝 (0 : ℝ), a < 1 :=
        Iio_mem_nhds (by norm_num : (0 : ℝ) < 1)
      exact h.filter_mono inf_le_left
  have hbound :
      ∀ᶠ a in 𝓝[Set.Ici (0 : ℝ)] (0 : ℝ),
        ∀ᵐ x ∂μ, ‖logKernel a b x‖ ≤ logKernel 1 b x := by
    filter_upwards [haNonneg, haLt] with a ha0 ha1
    filter_upwards with x
    have haSq : a ^ 2 ≤ 1 := by nlinarith [sq_nonneg (a + 1)]
    have hxSq : 0 ≤ x ^ 2 := sq_nonneg x
    have hargs :
        1 + a ^ 2 * x ^ 2 ≤ 1 + (1 : ℝ) ^ 2 * x ^ 2 := by
      nlinarith
    have hlog :
        Real.log (1 + a ^ 2 * x ^ 2) ≤
          Real.log (1 + (1 : ℝ) ^ 2 * x ^ 2) :=
      Real.strictMonoOn_log.monotoneOn
        (show 0 < 1 + a ^ 2 * x ^ 2 by positivity)
        (show 0 < 1 + (1 : ℝ) ^ 2 * x ^ 2 by positivity)
        hargs
    rw [Real.norm_eq_abs,
      abs_of_nonneg (logKernel_nonneg a b x)]
    unfold logKernel
    exact div_le_div_of_nonneg_right hlog (by positivity)
  have hmajor :
      Integrable (logKernel 1 b) μ := by
    change IntegrableOn (logKernel 1 b) (Ioi (0 : ℝ)) volume
    exact logKernel_integrable 1 b hb.ne'
  have hlim :
      ∀ᵐ x ∂μ,
        Tendsto (fun a : ℝ => logKernel a b x)
          (𝓝[Set.Ici (0 : ℝ)] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    filter_upwards with x
    have hfull :
        Tendsto (fun a : ℝ => logKernel a b x)
          (𝓝 (0 : ℝ)) (𝓝 (logKernel 0 b x)) :=
      (logKernel_param_continuous b x hb.ne').continuousAt
    have h :=
      hfull.mono_left
        (show 𝓝[Set.Ici (0 : ℝ)] (0 : ℝ) ≤ 𝓝 (0 : ℝ) from inf_le_left)
    simpa [logKernel] using h
  have hDCT :=
    tendsto_integral_filter_of_dominated_convergence
      (μ := μ) (bound := logKernel 1 b)
      hmeas hbound hmajor hlim
  simpa [auxValue, μ] using hDCT

private def auxForm (b a : ℝ) : ℝ :=
  (Real.pi / b) * Real.log (1 + a * b)

private theorem auxForm_hasDerivAt
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    HasDerivAt (auxForm b)
      (Real.pi / (1 + a * b)) a := by
  have hinner :
      HasDerivAt (fun c : ℝ => 1 + c * b) b a := by
    convert
      (hasDerivAt_const a 1).add ((hasDerivAt_id a).mul_const b)
      using 1 <;>
      simp only [id_eq, one_mul, zero_add]
  have hlog :=
    (Real.hasDerivAt_log
      (by positivity : 1 + a * b ≠ 0)).comp a hinner
  unfold auxForm
  convert hlog.const_mul (Real.pi / b) using 1
  field_simp [hb.ne']

private theorem auxForm_tendsto_zero
    (b : ℝ) (hb : 0 < b) :
    Tendsto (auxForm b)
      (𝓝[Set.Ioi (0 : ℝ)] (0 : ℝ)) (𝓝 0) := by
  have hinner :
      Tendsto (fun a : ℝ => 1 + a * b)
        (𝓝[Set.Ioi (0 : ℝ)] (0 : ℝ)) (𝓝 1) := by
    have hcont :
        Tendsto (fun a : ℝ => 1 + a * b) (𝓝 0) (𝓝 1) := by
      have hc :
          ContinuousAt (fun a : ℝ => 1 + a * b) 0 := by
        fun_prop
      simpa using hc.tendsto
    exact hcont.mono_left inf_le_left
  have hlog :
      Tendsto (fun a : ℝ => Real.log (1 + a * b))
        (𝓝[Set.Ioi (0 : ℝ)] (0 : ℝ)) (𝓝 0) := by
    simpa using hinner.log one_ne_zero
  unfold auxForm
  simpa using tendsto_const_nhds.mul hlog

private theorem auxValue_eq_auxForm
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    auxValue b a = auxForm b a := by
  let G : ℝ → ℝ := fun t => auxValue b t - auxForm b t
  have hG (t : ℝ) (ht : 0 < t) :
      HasDerivAt G 0 t := by
    have h :=
      (auxValue_hasDerivAt t b ht hb).sub
        (auxForm_hasDerivAt t b ht hb)
    simpa only [G, sub_self] using h
  have hconstant (c : ℝ) (hc : 0 < c) (hca : c ≤ a) :
      G c = G a := by
    have hbound :=
      Convex.norm_image_sub_le_of_norm_deriv_le
        (f := G) (s := Icc c a) (C := 0)
        (fun t ht =>
          (hG t (hc.trans_le ht.1)).differentiableAt)
        (fun t ht => by
          rw [(hG t (hc.trans_le ht.1)).deriv, norm_zero])
        (convex_Icc c a)
        ⟨le_rfl, hca⟩
        ⟨hca, le_rfl⟩
    have hzero : ‖G a - G c‖ = 0 := by
      apply le_antisymm
      · simpa using hbound
      · exact norm_nonneg _
    exact (sub_eq_zero.mp (norm_eq_zero.mp hzero)).symm
  have hGlim :
      Tendsto G (𝓝[Set.Ioi (0 : ℝ)] (0 : ℝ)) (𝓝 0) := by
    have haux :=
      (auxValue_tendsto_zero b hb).mono_left
        (nhdsWithin_mono (0 : ℝ) Ioi_subset_Ici_self)
    have hform := auxForm_tendsto_zero b hb
    simpa only [G, sub_zero] using haux.sub hform
  have hevent :
      G =ᶠ[𝓝[Set.Ioi (0 : ℝ)] (0 : ℝ)] fun _ => G a := by
    have hlt :
        ∀ᶠ c in 𝓝[Set.Ioi (0 : ℝ)] (0 : ℝ), c < a :=
      by
        have h : ∀ᶠ c in 𝓝 (0 : ℝ), c < a :=
          Iio_mem_nhds ha
        exact h.filter_mono inf_le_left
    filter_upwards [self_mem_nhdsWithin, hlt] with c hc hca
    exact hconstant c hc hca.le
  have hconstlim :
      Tendsto G (𝓝[Set.Ioi (0 : ℝ)] (0 : ℝ)) (𝓝 (G a)) :=
    tendsto_const_nhds.congr' hevent.symm
  have hGa : G a = 0 :=
    tendsto_nhds_unique hconstlim hGlim
  exact sub_eq_zero.mp hGa

private def targetKernel (a b x : ℝ) : ℝ :=
  Real.log (a ^ 2 + x ^ 2) / (b ^ 2 + x ^ 2)

private theorem targetKernel_eq_aux
    (a b x : ℝ) (ha : 0 < a) :
    targetKernel a b x =
      (2 * Real.log a) * cauchyKernel b x +
        logKernel (1 / a) b x := by
  have hfactor :
      a ^ 2 + x ^ 2 =
        a ^ 2 * (1 + (1 / a) ^ 2 * x ^ 2) := by
    field_simp [ha.ne']
  have h₁ : a ^ 2 ≠ 0 := pow_ne_zero 2 ha.ne'
  have h₂ : 1 + (1 / a) ^ 2 * x ^ 2 ≠ 0 := by positivity
  unfold targetKernel cauchyKernel logKernel
  rw [hfactor, Real.log_mul h₁ h₂, Real.log_pow]
  ring

private theorem targetKernel_integrable
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    IntegrableOn (targetKernel a b) (Ioi (0 : ℝ)) volume := by
  have hcomb :
      IntegrableOn
        (fun x : ℝ =>
          (2 * Real.log a) * cauchyKernel b x +
            logKernel (1 / a) b x)
        (Ioi (0 : ℝ)) volume :=
    ((cauchyKernel_integrable b hb).const_mul _).add
      (logKernel_integrable (1 / a) b hb.ne')
  exact hcomb.congr_fun
    (fun x _ => (targetKernel_eq_aux a b x ha).symm)
    measurableSet_Ioi

private theorem targetKernel_integral_pos
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (∫ x in Ioi (0 : ℝ), targetKernel a b x ∂volume) =
      (Real.pi / b) * Real.log (a + b) := by
  have haInv : 0 < 1 / a := one_div_pos.mpr ha
  have haux :=
    auxValue_eq_auxForm (1 / a) b haInv hb
  have hlog :
      Real.log a + Real.log (1 + b / a) =
        Real.log (a + b) := by
    have harg : 0 < 1 + b / a := by positivity
    have hmul : a * (1 + b / a) = a + b := by
      field_simp [ha.ne']
    rw [← Real.log_mul ha.ne' harg.ne', hmul]
  calc
    (∫ x in Ioi (0 : ℝ), targetKernel a b x ∂volume) =
        ∫ x in Ioi (0 : ℝ),
          ((2 * Real.log a) * cauchyKernel b x +
            logKernel (1 / a) b x) ∂volume := by
          apply setIntegral_congr_fun measurableSet_Ioi
          intro x _
          exact targetKernel_eq_aux a b x ha
    _ = (2 * Real.log a) *
          ∫ x in Ioi (0 : ℝ), cauchyKernel b x ∂volume +
        ∫ x in Ioi (0 : ℝ), logKernel (1 / a) b x ∂volume := by
          rw [integral_add
            ((cauchyKernel_integrable b hb).const_mul _)
            (logKernel_integrable (1 / a) b hb.ne')]
          rw [integral_const_mul]
    _ = (2 * Real.log a) * (Real.pi / (2 * b)) +
        auxValue b (1 / a) := by
          rw [cauchyKernel_integral b hb]
          rfl
    _ = (2 * Real.log a) * (Real.pi / (2 * b)) +
        auxForm b (1 / a) := by rw [haux]
    _ = (2 * Real.log a) * (Real.pi / (2 * b)) +
        (Real.pi / b) * Real.log (1 + b / a) := by
          unfold auxForm
          congr 2
          field_simp [ha.ne']
    _ = (Real.pi / b) *
        (Real.log a + Real.log (1 + b / a)) := by ring
    _ = (Real.pi / b) * Real.log (a + b) := by rw [hlog]

private def baseLogKernel (x : ℝ) : ℝ :=
  Real.log (x ^ 2) / (1 + x ^ 2)

private theorem baseLogKernel_continuousOn :
    ContinuousOn baseLogKernel (Ioi (0 : ℝ)) := by
  intro x hx
  have hx0 : x ≠ 0 := ne_of_gt hx
  unfold baseLogKernel
  apply ContinuousAt.continuousWithinAt
  apply ContinuousAt.div
  · apply ContinuousAt.log
    · fun_prop
    · exact pow_ne_zero 2 hx0
  · fun_prop
  · positivity

private theorem baseLogKernel_integrable :
    IntegrableOn baseLogKernel (Ioi (0 : ℝ)) volume := by
  have hlogIoc :
      IntegrableOn Real.log (Ioc (0 : ℝ) 1) volume :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le
      (by norm_num : (0 : ℝ) ≤ 1)).mp
      (intervalIntegral.intervalIntegrable_log'
        (a := (0 : ℝ)) (b := 1))
  have hnearMajor :
      IntegrableOn (fun x : ℝ => 2 * ‖Real.log x‖)
        (Ioc (0 : ℝ) 1) volume :=
    hlogIoc.norm.const_mul 2
  have hnear :
      IntegrableOn baseLogKernel (Ioc (0 : ℝ) 1) volume := by
    apply hnearMajor.mono'
    · exact
        (baseLogKernel_continuousOn.mono
          (fun _ hx => hx.1)).aestronglyMeasurable measurableSet_Ioc
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      have hxpos : 0 < x := hx.1
      have hden : 1 ≤ 1 + x ^ 2 := by
        nlinarith [sq_nonneg x]
      have hdenpos : 0 < 1 + x ^ 2 := by positivity
      unfold baseLogKernel
      rw [Real.norm_eq_abs, abs_div, abs_of_pos hdenpos]
      rw [Real.log_pow, abs_mul]
      norm_num [Real.norm_eq_abs]
      exact div_le_self (mul_nonneg (by norm_num) (abs_nonneg _)) hden
  have htailMajor :
      IntegrableOn (fun x : ℝ => 4 * x ^ (-3 / 2 : ℝ))
        (Ioi (1 : ℝ)) volume :=
    (integrableOn_Ioi_rpow_of_lt
      (a := (-3 / 2 : ℝ)) (c := 1)
      (by norm_num) zero_lt_one).const_mul 4
  have htail :
      IntegrableOn baseLogKernel (Ioi (1 : ℝ)) volume := by
    apply htailMajor.mono'
    · have hc :
          ContinuousOn baseLogKernel (Ioi (1 : ℝ)) :=
        baseLogKernel_continuousOn.mono
          (Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1))
      exact hc.aestronglyMeasurable measurableSet_Ioi
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      change (1 : ℝ) < x at hx
      have hxpos : 0 < x := zero_lt_one.trans hx
      have hlognon : 0 ≤ Real.log x := Real.log_nonneg hx.le
      have hlog :
          Real.log x ≤ 2 * x ^ (1 / 2 : ℝ) := by
        calc
          Real.log x ≤ x ^ (1 / 2 : ℝ) / (1 / 2 : ℝ) :=
            Real.log_le_rpow_div hxpos.le (by norm_num)
          _ = 2 * x ^ (1 / 2 : ℝ) := by ring
      have hden : x ^ 2 ≤ 1 + x ^ 2 := by linarith
      unfold baseLogKernel
      rw [Real.norm_eq_abs, abs_div,
        Real.log_pow, abs_of_nonneg (by positivity),
        abs_of_nonneg (by positivity)]
      have hdiv :
          2 * Real.log x / (1 + x ^ 2) ≤
            (4 * x ^ (1 / 2 : ℝ)) / x ^ 2 := by
        apply div_le_div₀
        · positivity
        · nlinarith
        · positivity
        · exact hden
      calc
        2 * Real.log x / (1 + x ^ 2) ≤
            (4 * x ^ (1 / 2 : ℝ)) / x ^ 2 := hdiv
        _ = 4 * x ^ (-3 / 2 : ℝ) := by
          calc
            (4 * x ^ (1 / 2 : ℝ)) / x ^ 2 =
                4 * (x ^ (1 / 2 : ℝ) / x ^ (2 : ℝ)) := by
                  rw [← Real.rpow_natCast x 2]
                  ring
            _ = 4 * x ^ ((1 / 2 : ℝ) - 2) := by
                  rw [Real.rpow_sub hxpos]
            _ = _ := by norm_num
  have hunion := hnear.union htail
  refine hunion.mono_set ?_
  intro x hx
  by_cases hx1 : x ≤ 1
  · exact Or.inl ⟨hx, hx1⟩
  · exact Or.inr (lt_of_not_ge hx1)

private theorem baseLogKernel_integral :
    (∫ x in Ioi (0 : ℝ), baseLogKernel x ∂volume) = 0 := by
  have hchange :=
    integral_comp_rpow_Ioi (g := baseLogKernel)
      (p := (-1 : ℝ)) (by norm_num)
  have hpoint :
      ∀ x ∈ Ioi (0 : ℝ),
        ((|(-1 : ℝ)| * x ^ ((-1 : ℝ) - 1)) •
          baseLogKernel (x ^ (-1 : ℝ))) =
            -baseLogKernel x := by
    intro x hx
    have hxpos : 0 < x := hx
    have hx0 : x ≠ 0 := hxpos.ne'
    simp only [abs_neg, abs_one, one_mul, smul_eq_mul]
    rw [show (-1 : ℝ) - 1 = -2 by norm_num]
    rw [Real.rpow_neg hxpos.le, Real.rpow_two,
      Real.rpow_neg_one]
    unfold baseLogKernel
    simp_rw [Real.log_pow]
    rw [Real.log_inv]
    field_simp [hx0]
    ring
  have heq :
      (∫ x in Ioi (0 : ℝ),
          ((|(-1 : ℝ)| * x ^ ((-1 : ℝ) - 1)) •
            baseLogKernel (x ^ (-1 : ℝ))) ∂volume) =
        ∫ x in Ioi (0 : ℝ), -baseLogKernel x ∂volume := by
    apply setIntegral_congr_fun measurableSet_Ioi
    exact hpoint
  have hneg :
      (∫ x in Ioi (0 : ℝ), -baseLogKernel x ∂volume) =
        -(∫ x in Ioi (0 : ℝ), baseLogKernel x ∂volume) := by
    rw [integral_neg]
  have hself :
      -(∫ x in Ioi (0 : ℝ), baseLogKernel x ∂volume) =
        ∫ x in Ioi (0 : ℝ), baseLogKernel x ∂volume := by
    rw [← hneg, ← heq]
    exact hchange
  linarith

private theorem targetKernel_scaled_zero
    (b t : ℝ) (hb : 0 < b) (ht : 0 < t) :
    targetKernel 0 b (b * t) =
      (2 * Real.log b / b ^ 2) * cauchyKernel 1 t +
        (1 / b ^ 2) * baseLogKernel t := by
  have hbSq : b ^ 2 ≠ 0 := pow_ne_zero 2 hb.ne'
  have htSq : t ^ 2 ≠ 0 := pow_ne_zero 2 ht.ne'
  have hnum : (b * t) ^ 2 = b ^ 2 * t ^ 2 := by ring
  have hden :
      b ^ 2 + (b * t) ^ 2 = b ^ 2 * (1 + t ^ 2) := by ring
  unfold targetKernel cauchyKernel baseLogKernel
  norm_num only [zero_pow, zero_add, one_pow]
  rw [hnum, Real.log_mul hbSq htSq, Real.log_pow]
  field_simp [hb.ne']
  ring

private theorem targetKernel_integral_zero
    (b : ℝ) (hb : 0 < b) :
    (∫ x in Ioi (0 : ℝ), targetKernel 0 b x ∂volume) =
      (Real.pi / b) * Real.log b := by
  have hscaled :
      (∫ t in Ioi (0 : ℝ), targetKernel 0 b (b * t) ∂volume) =
        b⁻¹ •
          ∫ x in Ioi (0 : ℝ), targetKernel 0 b x ∂volume :=
    by
      simpa only [mul_zero] using
        integral_comp_mul_left_Ioi (targetKernel 0 b) 0 hb
  have hlhs :
      (∫ t in Ioi (0 : ℝ), targetKernel 0 b (b * t) ∂volume) =
        Real.pi * Real.log b / b ^ 2 := by
    calc
      (∫ t in Ioi (0 : ℝ), targetKernel 0 b (b * t) ∂volume) =
          ∫ t in Ioi (0 : ℝ),
            ((2 * Real.log b / b ^ 2) * cauchyKernel 1 t +
              (1 / b ^ 2) * baseLogKernel t) ∂volume := by
            apply setIntegral_congr_fun measurableSet_Ioi
            intro t ht
            exact targetKernel_scaled_zero b t hb ht
      _ = (2 * Real.log b / b ^ 2) *
            ∫ t in Ioi (0 : ℝ), cauchyKernel 1 t ∂volume +
          (1 / b ^ 2) *
            ∫ t in Ioi (0 : ℝ), baseLogKernel t ∂volume := by
            rw [integral_add
              ((cauchyKernel_integrable 1 zero_lt_one).const_mul _)
              (baseLogKernel_integrable.const_mul _)]
            rw [integral_const_mul, integral_const_mul]
      _ = (2 * Real.log b / b ^ 2) * (Real.pi / 2) +
          (1 / b ^ 2) * 0 := by
            rw [cauchyKernel_integral 1 zero_lt_one,
              baseLogKernel_integral]
            norm_num
      _ = Real.pi * Real.log b / b ^ 2 := by ring
  rw [hlhs] at hscaled
  simp only [smul_eq_mul] at hscaled
  have hb0 : b ≠ 0 := hb.ne'
  calc
    (∫ x in Ioi (0 : ℝ), targetKernel 0 b x ∂volume) =
        b * (b⁻¹ *
          ∫ x in Ioi (0 : ℝ), targetKernel 0 b x ∂volume) := by
            field_simp
    _ = b * (Real.pi * Real.log b / b ^ 2) := by rw [← hscaled]
    _ = (Real.pi / b) * Real.log b := by
          field_simp [hb0]


theorem gap1 (β α₁ : ℝ) (hβ : 0 < β) (hα₁ : 0 ≤ α₁) :
    ContinuousOn (Iβ β) (Set.Icc 0 α₁) := by
  change ContinuousOn (auxValue β) (Set.Icc 0 α₁)
  have hform : ContinuousOn (auxForm β) (Set.Icc 0 α₁) := by
    intro α hα
    have harg : 0 < 1 + α * β := by
      nlinarith [hα.1, hβ]
    have hinner : ContinuousAt (fun a : ℝ => 1 + a * β) α := by
      fun_prop
    unfold auxForm
    exact (continuousAt_const.mul (hinner.log harg.ne')).continuousWithinAt
  apply hform.congr
  intro α hα
  rcases hα.1.eq_or_lt with rfl | hαpos
  · simp [auxValue, auxForm, logKernel]
  · exact auxValue_eq_auxForm α β hαpos hβ

theorem gap2 (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    (∫ x in Set.Ioi (0 : ℝ),
      deriv (fun a : ℝ => Real.log (1 + a ^ 2 * x ^ 2)) α /
        (β ^ 2 + x ^ 2)) =
      ∫ x in Set.Ioi (0 : ℝ),
        2 * α * x ^ 2 /
          ((β ^ 2 + x ^ 2) * (1 + α ^ 2 * x ^ 2)) := by
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  dsimp only
  have hinner :
      HasDerivAt (fun a : ℝ => 1 + a ^ 2 * x ^ 2)
        (2 * α * x ^ 2) α := by
    convert
      (hasDerivAt_const α 1).add
        (((hasDerivAt_id α).pow 2).mul_const (x ^ 2)) using 1
    simp only [id_eq, Nat.cast_ofNat, Nat.reduceSubDiff, pow_one]
    ring
  have hlog :=
    (Real.hasDerivAt_log
      (show 1 + α ^ 2 * x ^ 2 ≠ 0 by positivity)).comp α hinner
  have hderiv :
      deriv (fun a : ℝ => Real.log (1 + a ^ 2 * x ^ 2)) α =
        (1 + α ^ 2 * x ^ 2)⁻¹ * (2 * α * x ^ 2) := by
    simpa only [Function.comp_apply] using hlog.deriv
  rw [hderiv]
  field_simp [show β ^ 2 + x ^ 2 ≠ 0 by positivity,
    show 1 + α ^ 2 * x ^ 2 ≠ 0 by positivity]

theorem gap3 (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    (∫ x in Set.Ioi (0 : ℝ),
      2 * α * x ^ 2 /
        ((β ^ 2 + x ^ 2) * (1 + α ^ 2 * x ^ 2))) =
      Real.pi / (α * β + 1) := by
  change (∫ x in Set.Ioi (0 : ℝ), derivativeKernel α β x) =
    Real.pi / (α * β + 1)
  simpa [add_comm] using derivativeKernel_integral α β hα hβ

theorem gap4 (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    deriv (Iβ β) α = Real.pi / (α * β + 1) := by
  change deriv (auxValue β) α = _
  simpa [add_comm] using (auxValue_hasDerivAt α β hα hβ).deriv

theorem gap5 (β : ℝ) (hβ : 0 < β) :
    ∃ C : ℝ, ∀ α : ℝ, 0 < α →
      Iβ β α = Real.pi / β * Real.log (1 + α * β) + C := by
  refine ⟨0, ?_⟩
  intro α hα
  change auxValue β α = _
  rw [auxValue_eq_auxForm α β hα hβ]
  simp [auxForm]

theorem gap6 (β : ℝ) (hβ : β ≠ 0) :
    Iβ β 0 = 0 := by
  unfold Iβ baseIntegrand
  simp

theorem gap7 (β : ℝ) (hβ : 0 < β) :
    ∃ C : ℝ,
      (∀ α : ℝ, 0 < α →
        Iβ β α = Real.pi / β * Real.log (1 + α * β) + C) ∧
      Iβ β 0 = 0 + C := by
  refine ⟨0, ?_, ?_⟩
  · intro α hα
    change auxValue β α =
      Real.pi / β * Real.log (1 + α * β) + 0
    rw [auxValue_eq_auxForm α β hα hβ]
    simp [auxForm]
  · simp [gap6 β hβ.ne']

theorem gap8 (β : ℝ) (hβ : 0 < β) :
    ∃ C : ℝ,
      (∀ α : ℝ, 0 < α →
        Iβ β α = Real.pi / β * Real.log (1 + α * β) + C) ∧
      0 = 0 + C := by
  rcases gap7 β hβ with ⟨C, hC, h0⟩
  refine ⟨C, hC, ?_⟩
  simpa [gap6 β hβ.ne'] using h0

theorem gap9 (β : ℝ) (hβ : 0 < β) :
    ∃ C : ℝ,
      (∀ α : ℝ, 0 < α →
        Iβ β α = Real.pi / β * Real.log (1 + α * β) + C) ∧
      C = 0 := by
  rcases gap8 β hβ with ⟨C, hC, h0⟩
  exact ⟨C, hC, by linarith⟩

theorem gap10 (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 < β) :
    Iβ β α = Real.pi / β * Real.log (1 + α * β) := by
  rcases gap9 β hβ with ⟨C, hC, hC0⟩
  subst C
  rcases hα.eq_or_lt with rfl | hαpos
  · simp [gap6 β hβ.ne']
  · simpa using hC α hαpos

theorem gap11 (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    (∫ x in Set.Ioi (0 : ℝ), logarithmicIntegrand α β x) =
      ∫ x in Set.Ioi (0 : ℝ),
        (2 * Real.log α + Real.log (1 + x ^ 2 / α ^ 2)) /
          (β ^ 2 + x ^ 2) := by
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  have h := targetKernel_eq_aux α β x hα
  unfold targetKernel cauchyKernel logKernel at h
  unfold logarithmicIntegrand
  rw [h]
  congr 2
  congr 1
  field_simp [hα.ne']

theorem gap12 (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    (∫ x in Set.Ioi (0 : ℝ), logarithmicIntegrand α β x) =
      2 * Real.log α *
          (∫ x in Set.Ioi (0 : ℝ), 1 / (β ^ 2 + x ^ 2)) +
        ∫ x in Set.Ioi (0 : ℝ),
          Real.log (1 + x ^ 2 / α ^ 2) / (β ^ 2 + x ^ 2) := by
  rw [gap11 α β hα hβ]
  have hf :
      IntegrableOn
        (fun x : ℝ => (2 * Real.log α) * (1 / (β ^ 2 + x ^ 2)))
        (Set.Ioi (0 : ℝ)) :=
    (cauchyKernel_integrable β hβ).const_mul _
  have hg :
      IntegrableOn
        (fun x : ℝ =>
          Real.log (1 + x ^ 2 / α ^ 2) / (β ^ 2 + x ^ 2))
        (Set.Ioi (0 : ℝ)) := by
    have h := logKernel_integrable (1 / α) β hβ.ne'
    apply h.congr_fun
    · intro x hx
      unfold logKernel
      congr 2
      congr 1
      field_simp [hα.ne']
    · exact measurableSet_Ioi
  rw [show
      (fun x : ℝ =>
        (2 * Real.log α + Real.log (1 + x ^ 2 / α ^ 2)) /
          (β ^ 2 + x ^ 2)) =
      fun x : ℝ =>
        (2 * Real.log α) * (1 / (β ^ 2 + x ^ 2)) +
          Real.log (1 + x ^ 2 / α ^ 2) / (β ^ 2 + x ^ 2) by
    funext x
    ring]
  rw [integral_add hf hg, integral_const_mul]

theorem gap13 (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    (∫ x in Set.Ioi (0 : ℝ), logarithmicIntegrand α β x) =
      Real.pi * Real.log α / β +
        Real.pi / β * Real.log (1 + β / α) := by
  rw [gap12 α β hα hβ]
  have hc :
      (∫ x in Set.Ioi (0 : ℝ), 1 / (β ^ 2 + x ^ 2)) =
        Real.pi / (2 * β) := by
    exact cauchyKernel_integral β hβ
  have hi :
      (∫ x in Set.Ioi (0 : ℝ),
        Real.log (1 + x ^ 2 / α ^ 2) / (β ^ 2 + x ^ 2)) =
        Iβ β (1 / α) := by
    unfold Iβ baseIntegrand
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    congr 2
    congr 1
    field_simp [hα.ne']
  rw [hc, hi, gap10 (1 / α) β (by positivity) hβ]
  congr 1
  · ring
  · congr 2
    ring

theorem gap14 (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    Real.pi * Real.log α / β +
        Real.pi / β * Real.log (1 + β / α) =
      Real.pi / β * Real.log (α + β) := by
  have hα0 : α ≠ 0 := hα.ne'
  have hsum : 0 < α + β := add_pos hα hβ
  rw [show 1 + β / α = (α + β) / α by field_simp]
  rw [Real.log_div hsum.ne' hα0]
  ring

theorem gap15 (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    (∫ x in Set.Ioi (0 : ℝ), logarithmicIntegrand α β x) =
      Real.pi / β * Real.log (α + β) := by
  exact (gap13 α β hα hβ).trans (gap14 α β hα hβ)

theorem gap16 (α β : ℝ) (hα : α = 0) :
    J β α =
      ∫ x in Set.Ioi (0 : ℝ), logarithmicIntegrand α β x := by
  rfl

private theorem targetKernel_integral_all (α β : ℝ) (hβ : β ≠ 0) :
    (∫ x in Ioi (0 : ℝ), targetKernel α β x ∂volume) =
      Real.pi / |β| * Real.log (|α| + |β|) := by
  have hβpos : 0 < |β| := abs_pos.mpr hβ
  have hleft :
      (∫ x in Ioi (0 : ℝ), targetKernel α β x ∂volume) =
        ∫ x in Ioi (0 : ℝ), targetKernel |α| |β| x ∂volume := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    unfold targetKernel
    rw [sq_abs, sq_abs]
  rw [hleft]
  by_cases hα : α = 0
  · subst α
    simpa using targetKernel_integral_zero |β| hβpos
  · exact targetKernel_integral_pos |α| |β|
      (abs_pos.mpr hα) hβpos

theorem gap17 (β : ℝ) (hβ : β ≠ 0) :
    ContinuousAt (J β) 0 := by
  have hJ :
      J β =
        fun α : ℝ =>
          Real.pi / |β| * Real.log (|α| + |β|) := by
    funext α
    unfold J logarithmicIntegrand
    exact targetKernel_integral_all α β hβ
  rw [hJ]
  have harg :
      ContinuousAt (fun α : ℝ => |α| + |β|) 0 := by
    fun_prop
  have harg0 : |(0 : ℝ)| + |β| ≠ 0 := by
    simpa using (abs_pos.mpr hβ).ne'
  exact continuousAt_const.mul (harg.log harg0)

theorem gap18 (α β : ℝ) (hα : α = 0) (hβ : 0 < β) :
    (∫ x in Set.Ioi (0 : ℝ),
      Real.log (x ^ 2) / (β ^ 2 + x ^ 2)) =
        Real.pi / β * Real.log β := by
  simpa [targetKernel] using targetKernel_integral_zero β hβ

theorem gap19 (α β : ℝ) (hβ : β ≠ 0) :
    (∫ x in Set.Ioi (0 : ℝ), logarithmicIntegrand α β x) =
      Real.pi / |β| * Real.log (|α| + |β|) := by
  unfold logarithmicIntegrand
  exact targetKernel_integral_all α β hβ

private theorem rpow_neg_two_integrable_of_log_lower
    (α c d : ℝ) (hc : 0 < c)
    (hlog : ∀ x ∈ Ioo (0 : ℝ) d,
      c ≤ |Real.log (α ^ 2 + x ^ 2)|)
    (hf : IntegrableOn
      (fun x : ℝ => Real.log (α ^ 2 + x ^ 2) / x ^ 2)
      (Ioi (0 : ℝ))) :
    IntegrableOn (fun x : ℝ => x ^ (-2 : ℝ))
      (Ioo (0 : ℝ) d) := by
  have hmajor :
      IntegrableOn
        (fun x : ℝ =>
          c⁻¹ * ‖Real.log (α ^ 2 + x ^ 2) / x ^ 2‖)
        (Ioo (0 : ℝ) d) := by
    exact IntegrableOn.mono_set (hf.norm.const_mul c⁻¹)
      Ioo_subset_Ioi_self
  apply hmajor.mono'
  · exact
      (continuousOn_id.rpow_const
        (fun x hx => Or.inl hx.1.ne')).aestronglyMeasurable
        measurableSet_Ioo
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    have hxpos : 0 < x := hx.1
    have hxsq : 0 < x ^ 2 := sq_pos_of_pos hxpos
    have hquot :
        (1 : ℝ) / x ^ 2 ≤
          (|Real.log (α ^ 2 + x ^ 2)| / c) / x ^ 2 := by
      apply (div_le_div_iff_of_pos_right hxsq).2
      exact (le_div_iff₀ hc).2 (by simpa using hlog x hx)
    rw [Real.norm_eq_abs,
      abs_of_pos (Real.rpow_pos_of_pos hxpos (-2 : ℝ)),
      Real.rpow_neg hxpos.le, Real.rpow_two]
    calc
      (x ^ 2)⁻¹ = (1 : ℝ) / x ^ 2 := by simp [one_div]
      _ ≤ (|Real.log (α ^ 2 + x ^ 2)| / c) / x ^ 2 := hquot
      _ = c⁻¹ * ‖Real.log (α ^ 2 + x ^ 2) / x ^ 2‖ := by
        rw [Real.norm_eq_abs, abs_div, abs_of_pos hxsq]
        field_simp [hc.ne', hxsq.ne']

theorem gap20 (α : ℝ) (hα : α ^ 2 ≠ 1) :
    ¬ IntegrableOn
      (fun x : ℝ => Real.log (α ^ 2 + x ^ 2) / x ^ 2)
      (Set.Ioi (0 : ℝ)) := by
  intro hf
  rcases lt_or_gt_of_ne hα with hlt | hgt
  · let m : ℝ := (1 + α ^ 2) / 2
    let c : ℝ := -Real.log m
    let d : ℝ := Real.sqrt ((1 - α ^ 2) / 2)
    have hmpos : 0 < m := by
      dsimp [m]
      positivity
    have hmlt : m < 1 := by
      dsimp [m]
      linarith
    have hc : 0 < c := by
      dsimp [c]
      exact neg_pos.mpr (Real.log_neg hmpos hmlt)
    have hdarg : 0 < (1 - α ^ 2) / 2 := by linarith
    have hd : 0 < d := Real.sqrt_pos.2 hdarg
    have hlog :
        ∀ x ∈ Ioo (0 : ℝ) d,
          c ≤ |Real.log (α ^ 2 + x ^ 2)| := by
      intro x hx
      have hdsq : d ^ 2 = (1 - α ^ 2) / 2 := by
        dsimp [d]
        exact Real.sq_sqrt hdarg.le
      have hxsq : x ^ 2 < d ^ 2 :=
        (sq_lt_sq₀ hx.1.le hd.le).2 hx.2
      have hsumpos : 0 < α ^ 2 + x ^ 2 := by
        nlinarith [sq_nonneg α, sq_pos_of_pos hx.1]
      have hsumm : α ^ 2 + x ^ 2 < m := by
        dsimp [m]
        nlinarith
      have hsumlt : α ^ 2 + x ^ 2 < 1 := hsumm.trans hmlt
      have hmono :
          Real.log (α ^ 2 + x ^ 2) ≤ Real.log m :=
        Real.strictMonoOn_log.monotoneOn hsumpos hmpos hsumm.le
      rw [abs_of_neg (Real.log_neg hsumpos hsumlt)]
      dsimp [c]
      linarith
    have hp := rpow_neg_two_integrable_of_log_lower
      α c d hc hlog hf
    have hcontra :=
      (intervalIntegral.integrableOn_Ioo_rpow_iff hd).mp hp
    norm_num at hcontra
  · let c : ℝ := Real.log (α ^ 2)
    have hc : 0 < c := by
      dsimp [c]
      exact Real.log_pos hgt
    have hlog :
        ∀ x ∈ Ioo (0 : ℝ) 1,
          c ≤ |Real.log (α ^ 2 + x ^ 2)| := by
      intro x hx
      have hapos : 0 < α ^ 2 := zero_lt_one.trans hgt
      have hsumpos : 0 < α ^ 2 + x ^ 2 := by positivity
      have hmono :
          Real.log (α ^ 2) ≤ Real.log (α ^ 2 + x ^ 2) :=
        Real.strictMonoOn_log.monotoneOn hapos hsumpos
          (le_add_of_nonneg_right (sq_nonneg x))
      rw [abs_of_pos (hc.trans_le hmono)]
      exact hmono
    have hp := rpow_neg_two_integrable_of_log_lower
      α c 1 hc hlog hf
    have hcontra :=
      (intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).mp hp
    norm_num at hcontra

end

end ProofGap.Exercise3800
