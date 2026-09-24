import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3738_1

noncomputable section

open Filter
open scoped Interval Topology

def quotient (a b x : ℝ) : ℝ :=
  (Real.rpow x b - Real.rpow x a) / Real.log x

def originalIntegral (a b : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..1,
    Real.sin (Real.log (1 / x)) * quotient a b x

def innerIntegral (y : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..1,
    Real.sin (Real.log (1 / x)) * Real.rpow x y

def laplaceIntegral (y : ℝ) : ℝ :=
  ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(y + 1) * t) * Real.sin t

def laplaceAntiderivative (y t : ℝ) : ℝ :=
  (-((y + 1) * Real.sin t) - Real.cos t) *
      Real.exp (-(y + 1) * t) /
    (1 + (1 + y) ^ 2)

def arctanPrimitive (y : ℝ) : ℝ :=
  Real.arctan (1 + y)

private def powerIntegral (a b x : ℝ) : ℝ :=
  ∫ y in a..b, Real.rpow x y

private def sinXPrimitive (y x : ℝ) : ℝ :=
  Real.rpow x (y + 1) *
      (Real.cos (Real.log x) - (y + 1) * Real.sin (Real.log x)) /
    (1 + (y + 1) ^ 2)

private theorem quotient_eq_powerIntegral (a b x : ℝ)
    (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    quotient a b x = powerIntegral a b x := by
  have hloglt : Real.log x < 0 := Real.log_neg hx.1 hx.2
  have hlog : Real.log x ≠ 0 := ne_of_lt hloglt
  have hrpow (y : ℝ) :
      Real.rpow x y = Real.exp (y * Real.log x) := by
    simpa only [mul_comm] using Real.rpow_def_of_pos hx.1 y
  have hcont : Continuous (fun y : ℝ => Real.rpow x y) := by
    have heq : (fun y : ℝ => Real.rpow x y) =
        fun y : ℝ => Real.exp (y * Real.log x) := by
      funext y
      exact hrpow y
    rw [heq]
    exact Real.continuous_exp.comp (continuous_id.mul continuous_const)
  have hderiv : ∀ y : ℝ,
      HasDerivAt (fun z : ℝ => Real.exp (z * Real.log x) / Real.log x)
        (Real.rpow x y) y := by
    intro y
    have hd :=
      (((hasDerivAt_id y).mul_const (Real.log x)).exp.div_const
        (Real.log x))
    convert hd using 1
    simp only [id_eq]
    rw [hrpow y]
    field_simp [hlog]
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun y _ => hderiv y) (hcont.intervalIntegrable a b)
  unfold quotient powerIntegral
  rw [hrpow b, hrpow a]
  calc
    (Real.exp (b * Real.log x) - Real.exp (a * Real.log x)) /
        Real.log x =
      Real.exp (b * Real.log x) / Real.log x -
        Real.exp (a * Real.log x) / Real.log x := by ring
    _ = ∫ y in a..b, Real.rpow x y := hi.symm

private theorem sinXPrimitive_deriv (y x : ℝ) (hx : 0 < x) :
    HasDerivAt (sinXPrimitive y)
      (Real.sin (Real.log (1 / x)) * Real.rpow x y) x := by
  have hpow := Real.hasDerivAt_rpow_const
    (x := x) (p := y + 1) (Or.inl hx.ne')
  have hlog := Real.hasDerivAt_log hx.ne'
  have hcos := (Real.hasDerivAt_cos (Real.log x)).comp x hlog
  have hsin := (Real.hasDerivAt_sin (Real.log x)).comp x hlog
  have hbracket := hcos.sub (hsin.const_mul (y + 1))
  have h := (hpow.mul hbracket).div_const (1 + (y + 1) ^ 2)
  convert h using 1
  have hden : 1 + (y + 1) ^ 2 ≠ 0 := by positivity
  simp only [Pi.sub_apply, Function.comp_apply]
  rw [one_div, Real.log_inv, Real.sin_neg]
  rw [show y + 1 - 1 = y by ring]
  field_simp [hden, hx.ne']
  rw [Real.rpow_add_one hx.ne' y]
  rw [show Real.rpow x y = x ^ y by rfl]
  simp only [Real.rpow_def_of_pos hx]
  ring

private theorem sinIntegrand_intervalIntegrable (y : ℝ) (hy : -1 < y) :
    IntervalIntegrable
      (fun x : ℝ => Real.sin (Real.log (1 / x)) * Real.rpow x y)
      MeasureTheory.volume 0 1 := by
  have hpow := intervalIntegral.intervalIntegrable_rpow'
    (a := (0 : ℝ)) (b := 1) hy
  have hmeas : Measurable
      (fun x : ℝ => Real.sin (Real.log (1 / x))) :=
    Real.measurable_sin.comp
      (Real.measurable_log.comp (measurable_const.div measurable_id))
  have hbound : ∀ x : ℝ,
      ‖Real.sin (Real.log (1 / x))‖ ≤ (1 : ℝ) := by
    intro x
    rw [Real.norm_eq_abs]
    exact Real.abs_sin_le_one _
  constructor
  · exact hpow.1.bdd_mul hmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall hbound)
  · exact hpow.2.bdd_mul hmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall hbound)

private theorem sinXPrimitive_tendsto_zero (y : ℝ) (hy : 0 < y + 1) :
    Tendsto (sinXPrimitive y) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hpowCont :
      ContinuousAt (fun x : ℝ => Real.rpow x (y + 1)) 0 :=
    continuousAt_id.rpow continuousAt_const (Or.inr hy)
  have hpowZero : Real.rpow 0 (y + 1) = 0 :=
    Real.zero_rpow hy.ne'
  have hpow :
      Tendsto (fun x : ℝ => Real.rpow x (y + 1))
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [hpowZero] using hpowCont.tendsto.mono_left inf_le_left
  let C : ℝ := (1 + |y + 1|) / (1 + (y + 1) ^ 2)
  have hmajor :
      Tendsto (fun x : ℝ => Real.rpow x (y + 1) * C)
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using hpow.mul_const C
  have hbound : ∀ᶠ x : ℝ in 𝓝[>] (0 : ℝ),
      |sinXPrimitive y x| ≤ Real.rpow x (y + 1) * C := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hxpos : 0 < x := hx
    have hpowNonneg : 0 ≤ Real.rpow x (y + 1) :=
      Real.rpow_nonneg hxpos.le _
    have hdenpos : 0 < 1 + (y + 1) ^ 2 := by positivity
    have htrig :
        |Real.cos (Real.log x) - (y + 1) * Real.sin (Real.log x)| ≤
          1 + |y + 1| := by
      calc
        |Real.cos (Real.log x) - (y + 1) * Real.sin (Real.log x)| ≤
            |Real.cos (Real.log x)| +
              |(y + 1) * Real.sin (Real.log x)| := abs_sub _ _
        _ = |Real.cos (Real.log x)| +
              |y + 1| * |Real.sin (Real.log x)| := by rw [abs_mul]
        _ ≤ 1 + |y + 1| * 1 := by
          gcongr
          · exact Real.abs_cos_le_one _
          · exact Real.abs_sin_le_one _
        _ = 1 + |y + 1| := by ring
    dsimp [sinXPrimitive, C]
    have hpowNonneg' : 0 ≤ x ^ (y + 1) := by exact hpowNonneg
    rw [abs_div, abs_mul, abs_of_nonneg hpowNonneg',
      abs_of_pos hdenpos]
    calc
      x ^ (y + 1) *
            |Real.cos (Real.log x) - (y + 1) * Real.sin (Real.log x)| /
          (1 + (y + 1) ^ 2) ≤
          Real.rpow x (y + 1) * (1 + |y + 1|) /
            (1 + (y + 1) ^ 2) := by
        rw [show x ^ (y + 1) = Real.rpow x (y + 1) by rfl]
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left htrig hpowNonneg) hdenpos.le
      _ = x ^ (y + 1) *
          ((1 + |y + 1|) / (1 + (y + 1) ^ 2)) := by
        rw [show Real.rpow x (y + 1) = x ^ (y + 1) by rfl]
        ring
  apply (tendsto_zero_iff_abs_tendsto_zero (sinXPrimitive y)).2
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun x => abs_nonneg _
  · simpa only [Function.comp_apply] using hbound
  · exact hmajor

private theorem innerIntegral_value (y : ℝ) (hy : -1 < y) :
    innerIntegral y = 1 / (1 + (1 + y) ^ 2) := by
  have hint := sinIntegrand_intervalIntegrable y hy
  have hzero : Tendsto (sinXPrimitive y) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    sinXPrimitive_tendsto_zero y (by linarith)
  have hone :
      Tendsto (sinXPrimitive y) (𝓝[<] (1 : ℝ))
        (𝓝 (1 / (1 + (1 + y) ^ 2))) := by
    have hc := (sinXPrimitive_deriv y 1 zero_lt_one).continuousAt.tendsto
    convert hc.mono_left inf_le_left using 1
    simp [sinXPrimitive]
    ring
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto
    (a := (0 : ℝ)) (b := 1) zero_lt_one
    (fun x hx => sinXPrimitive_deriv y x hx.1) hint hzero hone
  simpa [innerIntegral] using hi

private theorem laplaceAntiderivative_deriv (y t : ℝ) :
    HasDerivAt (laplaceAntiderivative y)
      (Real.exp (-(y + 1) * t) * Real.sin t) t := by
  have hsin := Real.hasDerivAt_sin t
  have hcos := Real.hasDerivAt_cos t
  have hlin : HasDerivAt (fun s : ℝ => -(y + 1) * s) (-(y + 1)) t :=
    by
      convert (hasDerivAt_id t).const_mul (-(y + 1)) using 1 <;>
        simp
  have hexp := (Real.hasDerivAt_exp (-(y + 1) * t)).comp t hlin
  have hfront :=
    (hsin.const_mul (-(y + 1))).sub hcos
  have h := (hfront.mul hexp).div_const (1 + (1 + y) ^ 2)
  unfold laplaceAntiderivative
  convert h using 1
  · funext s
    simp only [Pi.sub_apply, Pi.mul_apply, Function.comp_apply]
    ring
  · have hden : 1 + (1 + y) ^ 2 ≠ 0 := by positivity
    simp only [Pi.sub_apply, Pi.mul_apply, Function.comp_apply]
    field_simp [hden]
    ring

private theorem laplaceIntegrand_integrable (y : ℝ) (hy : 0 < y + 1) :
    MeasureTheory.IntegrableOn
      (fun t : ℝ => Real.exp (-(y + 1) * t) * Real.sin t)
      (Set.Ioi (0 : ℝ)) := by
  have hexp : MeasureTheory.IntegrableOn
      (fun t : ℝ => Real.exp (-(y + 1) * t))
      (Set.Ioi (0 : ℝ)) := by
    apply integrableOn_exp_mul_Ioi
    linarith
  have hsinMeas : Measurable Real.sin := Real.measurable_sin
  have hbound : ∀ t : ℝ, ‖Real.sin t‖ ≤ (1 : ℝ) := by
    intro t
    rw [Real.norm_eq_abs]
    exact Real.abs_sin_le_one _
  have h := hexp.bdd_mul hsinMeas.aestronglyMeasurable
    (Filter.Eventually.of_forall hbound)
  simpa only [mul_comm] using h

private theorem laplaceAntiderivative_tendsto_zero
    (y : ℝ) (hy : 0 < y + 1) :
    Tendsto (laplaceAntiderivative y) atTop (𝓝 0) := by
  have hlin : Tendsto (fun t : ℝ => -(y + 1) * t) atTop atBot :=
    tendsto_const_nhds.neg_mul_atTop (by linarith) tendsto_id
  have hexp : Tendsto (fun t : ℝ => Real.exp (-(y + 1) * t))
      atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp hlin
  let C : ℝ := (|y + 1| + 1) / (1 + (1 + y) ^ 2)
  have hmajor :
      Tendsto (fun t : ℝ => Real.exp (-(y + 1) * t) * C)
        atTop (𝓝 0) := by
    simpa using hexp.mul_const C
  have hbound : ∀ t : ℝ,
      |laplaceAntiderivative y t| ≤
        Real.exp (-(y + 1) * t) * C := by
    intro t
    have hexpNonneg : 0 ≤ Real.exp (-(y + 1) * t) := Real.exp_nonneg _
    have hdenpos : 0 < 1 + (1 + y) ^ 2 := by positivity
    have hfront :
        |-((y + 1) * Real.sin t) - Real.cos t| ≤ |y + 1| + 1 := by
      calc
        |-((y + 1) * Real.sin t) - Real.cos t| ≤
            |-((y + 1) * Real.sin t)| + |Real.cos t| := abs_sub _ _
        _ = |y + 1| * |Real.sin t| + |Real.cos t| := by
          rw [abs_neg, abs_mul]
        _ ≤ |y + 1| * 1 + 1 := by
          gcongr
          · exact Real.abs_sin_le_one _
          · exact Real.abs_cos_le_one _
        _ = |y + 1| + 1 := by ring
    dsimp [laplaceAntiderivative, C]
    rw [abs_div, abs_mul, abs_of_nonneg hexpNonneg,
      abs_of_pos hdenpos]
    calc
      |-((y + 1) * Real.sin t) - Real.cos t| *
            Real.exp (-(y + 1) * t) / (1 + (1 + y) ^ 2) ≤
          (|y + 1| + 1) * Real.exp (-(y + 1) * t) /
            (1 + (1 + y) ^ 2) := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right hfront hexpNonneg) hdenpos.le
      _ = Real.exp (-(y + 1) * t) *
          ((|y + 1| + 1) / (1 + (1 + y) ^ 2)) := by ring
  apply (tendsto_zero_iff_abs_tendsto_zero
    (laplaceAntiderivative y)).2
  apply squeeze_zero
  · exact fun t => abs_nonneg _
  · exact hbound
  · exact hmajor

private theorem laplace_fundamental (y : ℝ) (hy : -1 < y) :
    Tendsto (laplaceAntiderivative y) atTop (𝓝 0) ∧
      laplaceIntegral y = 0 - laplaceAntiderivative y 0 := by
  have htend := laplaceAntiderivative_tendsto_zero y (by linarith)
  refine ⟨htend, ?_⟩
  unfold laplaceIntegral
  exact MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun t _ => laplaceAntiderivative_deriv y t)
    (laplaceIntegrand_integrable y (by linarith)) htend

private theorem laplaceIntegral_value (y : ℝ) (hy : -1 < y) :
    laplaceIntegral y = 1 / (1 + (1 + y) ^ 2) := by
  rw [(laplace_fundamental y hy).2]
  simp [laplaceAntiderivative]
  ring

theorem gap4 (a b y : ℝ) (ha : -1 < a) (hab : a < b)
    (hy : y ∈ Set.Icc a b) :
    innerIntegral y = laplaceIntegral y := by
  have hy' : -1 < y := lt_of_lt_of_le ha hy.1
  rw [innerIntegral_value y hy', laplaceIntegral_value y hy']

theorem gap5 (a b y : ℝ) (ha : -1 < a) (hab : a < b)
    (hy : y ∈ Set.Icc a b) :
    Tendsto (laplaceAntiderivative y) atTop (𝓝 0) ∧
      laplaceIntegral y = 0 - laplaceAntiderivative y 0 := by
  exact laplace_fundamental y (lt_of_lt_of_le ha hy.1)

theorem gap6 (a b y : ℝ) (ha : -1 < a) (hab : a < b)
    (hy : y ∈ Set.Icc a b) :
    laplaceIntegral y = 1 / (1 + (1 + y) ^ 2) := by
  exact laplaceIntegral_value y (lt_of_lt_of_le ha hy.1)

theorem gap7 (a b y : ℝ) (ha : -1 < a) (hab : a < b)
    (hy : y ∈ Set.Icc a b) :
    innerIntegral y = 1 / (1 + (1 + y) ^ 2) := by
  exact innerIntegral_value y (lt_of_lt_of_le ha hy.1)

private theorem weightedIntegrableOnRectangle
    (a b : ℝ) (ha : -1 < a) (hab : a < b) :
    MeasureTheory.IntegrableOn
      (fun p : ℝ × ℝ =>
        Real.sin (Real.log (1 / p.1)) * Real.rpow p.1 p.2)
      (Set.Ioc (0 : ℝ) 1 ×ˢ Set.Ioc a b)
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod
        (MeasureTheory.volume : MeasureTheory.Measure ℝ)) := by
  have hxint : MeasureTheory.IntegrableOn
      (fun x : ℝ => Real.rpow x a) (Set.Ioc (0 : ℝ) 1) :=
    (intervalIntegral.intervalIntegrable_rpow'
      (a := (0 : ℝ)) (b := 1) ha).1
  have hyint : MeasureTheory.IntegrableOn
      (fun _y : ℝ => (1 : ℝ)) (Set.Ioc a b) :=
    MeasureTheory.integrableOn_const measure_Ioc_lt_top.ne
  have hdom : MeasureTheory.IntegrableOn
      (fun p : ℝ × ℝ => Real.rpow p.1 a)
      (Set.Ioc (0 : ℝ) 1 ×ˢ Set.Ioc a b)
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod
        (MeasureTheory.volume : MeasureTheory.Measure ℝ)) := by
    unfold MeasureTheory.IntegrableOn at hxint hyint ⊢
    rw [← MeasureTheory.Measure.prod_restrict]
    simpa using hxint.mul_prod hyint
  have hrectMeas :
      MeasurableSet (Set.Ioc (0 : ℝ) 1 ×ˢ Set.Ioc a b) :=
    measurableSet_Ioc.prod measurableSet_Ioc
  have hrpowCont : ContinuousOn
      (fun p : ℝ × ℝ => Real.rpow p.1 p.2)
      (Set.Ioc (0 : ℝ) 1 ×ˢ Set.Ioc a b) := by
    apply continuousOn_fst.rpow continuousOn_snd
    intro p hp
    exact Or.inl (ne_of_gt hp.1.1)
  have hrpowInt : MeasureTheory.IntegrableOn
      (fun p : ℝ × ℝ => Real.rpow p.1 p.2)
      (Set.Ioc (0 : ℝ) 1 ×ˢ Set.Ioc a b)
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod
        (MeasureTheory.volume : MeasureTheory.Measure ℝ)) := by
    apply hdom.mono'
    · exact hrpowCont.aestronglyMeasurable hrectMeas
    · filter_upwards
        [MeasureTheory.ae_restrict_mem hrectMeas] with p hp
      have hnonneg : 0 ≤ Real.rpow p.1 p.2 :=
        Real.rpow_nonneg (le_of_lt hp.1.1) _
      rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
      exact Real.rpow_le_rpow_of_exponent_ge hp.1.1 hp.1.2 hp.2.1.le
  have hsinMeas : Measurable (fun p : ℝ × ℝ =>
      Real.sin (Real.log (1 / p.1))) :=
    Real.measurable_sin.comp
      (Real.measurable_log.comp (measurable_const.div measurable_fst))
  have hsinBound : ∀ p : ℝ × ℝ,
      ‖Real.sin (Real.log (1 / p.1))‖ ≤ (1 : ℝ) := by
    intro p
    rw [Real.norm_eq_abs]
    exact Real.abs_sin_le_one _
  exact hrpowInt.bdd_mul hsinMeas.aestronglyMeasurable
    (Filter.Eventually.of_forall hsinBound)

private theorem original_eq_weightedPowerIntegral (a b : ℝ) :
    originalIntegral a b =
      ∫ x in (0 : ℝ)..1,
        Real.sin (Real.log (1 / x)) * powerIntegral a b x := by
  have hne : ∀ᵐ x : ℝ
      ∂((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict
        (Set.Ioc (0 : ℝ) 1)), x ≠ (1 : ℝ) := by
    rw [MeasureTheory.ae_iff]
    simp
  rw [originalIntegral,
    intervalIntegral.integral_of_le (le_of_lt zero_lt_one),
    intervalIntegral.integral_of_le (le_of_lt zero_lt_one)]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc,
    hne] with x hx hx1
  congr 1
  exact quotient_eq_powerIntegral a b x
    ⟨hx.1, lt_of_le_of_ne hx.2 hx1⟩

private theorem weighted_fubini_ordered
    (a b : ℝ) (ha : -1 < a) (hab : a < b) :
    (∫ x in (0 : ℝ)..1,
      Real.sin (Real.log (1 / x)) * powerIntegral a b x) =
        ∫ y in a..b, innerIntegral y := by
  let f : ℝ × ℝ → ℝ := fun p =>
    Real.sin (Real.log (1 / p.1)) * Real.rpow p.1 p.2
  have hintOpen : MeasureTheory.IntegrableOn f
      (Set.Ioc (0 : ℝ) 1 ×ˢ Set.Ioc a b)
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod
        (MeasureTheory.volume : MeasureTheory.Measure ℝ)) := by
    exact weightedIntegrableOnRectangle a b ha hab
  have hmeas :
      MeasurableSet (Set.Ioc (0 : ℝ) 1 ×ˢ Set.Ioc a b) :=
    measurableSet_Ioc.prod measurableSet_Ioc
  have hind : MeasureTheory.Integrable
      ((Set.Ioc (0 : ℝ) 1 ×ˢ Set.Ioc a b).indicator f)
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod
        (MeasureTheory.volume : MeasureTheory.Measure ℝ)) := by
    rw [MeasureTheory.integrable_indicator_iff hmeas]
    exact hintOpen
  let g : ℝ → ℝ → ℝ := fun x y =>
    (Set.Ioc (0 : ℝ) 1).indicator
      (fun x => (Set.Ioc a b).indicator
        (fun y => Real.sin (Real.log (1 / x)) * Real.rpow x y) y) x
  have huncurry : Function.uncurry g =
      (Set.Ioc (0 : ℝ) 1 ×ˢ Set.Ioc a b).indicator f := by
    funext p
    by_cases hx : p.1 ∈ Set.Ioc (0 : ℝ) 1
    · by_cases hy : p.2 ∈ Set.Ioc a b
      · simp [Function.uncurry, g, f, hx, hy]
      · simp [Function.uncurry, g, f, hx, hy]
    · simp [Function.uncurry, g, f, hx]
  have hg : MeasureTheory.Integrable (Function.uncurry g)
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod
        (MeasureTheory.volume : MeasureTheory.Measure ℝ)) := by
    rw [huncurry]
    exact hind
  have hswap :
      (∫ x : ℝ, ∫ y : ℝ, g x y
        ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ)
        ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ)) =
        ∫ y : ℝ, ∫ x : ℝ, g x y
          ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ)
          ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ) :=
    MeasureTheory.integral_integral_swap hg
  have hleft :
      (∫ x : ℝ, ∫ y : ℝ, g x y
        ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ)
        ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ)) =
        ∫ x in Set.Ioc (0 : ℝ) 1,
          ∫ y in Set.Ioc a b,
            Real.sin (Real.log (1 / x)) * Real.rpow x y := by
    calc
      (∫ x : ℝ, ∫ y : ℝ, g x y
        ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ)
        ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ)) =
          ∫ x : ℝ, (Set.Ioc (0 : ℝ) 1).indicator
            (fun x => ∫ y : ℝ, (Set.Ioc a b).indicator
              (fun y => Real.sin (Real.log (1 / x)) * Real.rpow x y) y
              ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ)) x
            ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards [] with x
        by_cases hx : x ∈ Set.Ioc (0 : ℝ) 1
        · simp [g, hx]
        · simp [g, hx]
      _ = ∫ x in Set.Ioc (0 : ℝ) 1,
            ∫ y : ℝ, (Set.Ioc a b).indicator
              (fun y => Real.sin (Real.log (1 / x)) * Real.rpow x y) y
              ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
        exact MeasureTheory.integral_indicator measurableSet_Ioc
      _ = ∫ x in Set.Ioc (0 : ℝ) 1,
            ∫ y in Set.Ioc a b,
              Real.sin (Real.log (1 / x)) * Real.rpow x y := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards [] with x
        exact MeasureTheory.integral_indicator measurableSet_Ioc
  have hright :
      (∫ y : ℝ, ∫ x : ℝ, g x y
        ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ)
        ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ)) =
        ∫ y in Set.Ioc a b,
          ∫ x in Set.Ioc (0 : ℝ) 1,
            Real.sin (Real.log (1 / x)) * Real.rpow x y := by
    calc
      (∫ y : ℝ, ∫ x : ℝ, g x y
        ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ)
        ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ)) =
          ∫ y : ℝ, (Set.Ioc a b).indicator
            (fun y => ∫ x : ℝ, (Set.Ioc (0 : ℝ) 1).indicator
              (fun x => Real.sin (Real.log (1 / x)) * Real.rpow x y) x
              ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ)) y
            ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards [] with y
        by_cases hy : y ∈ Set.Ioc a b
        · simp [g, hy]
        · simp [g, hy]
      _ = ∫ y in Set.Ioc a b,
            ∫ x : ℝ, (Set.Ioc (0 : ℝ) 1).indicator
              (fun x => Real.sin (Real.log (1 / x)) * Real.rpow x y) x
              ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
        exact MeasureTheory.integral_indicator measurableSet_Ioc
      _ = ∫ y in Set.Ioc a b,
            ∫ x in Set.Ioc (0 : ℝ) 1,
              Real.sin (Real.log (1 / x)) * Real.rpow x y := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards [] with y
        exact MeasureTheory.integral_indicator measurableSet_Ioc
  rw [intervalIntegral.integral_of_le (le_of_lt zero_lt_one),
    intervalIntegral.integral_of_le hab.le]
  calc
    (∫ x in Set.Ioc (0 : ℝ) 1,
      Real.sin (Real.log (1 / x)) * powerIntegral a b x) =
        ∫ x in Set.Ioc (0 : ℝ) 1,
          ∫ y in Set.Ioc a b,
            Real.sin (Real.log (1 / x)) * Real.rpow x y := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [] with x
      unfold powerIntegral
      rw [intervalIntegral.integral_of_le hab.le,
        MeasureTheory.integral_const_mul]
    _ = ∫ y in Set.Ioc a b,
          ∫ x in Set.Ioc (0 : ℝ) 1,
            Real.sin (Real.log (1 / x)) * Real.rpow x y :=
      hleft.symm.trans (hswap.trans hright)
    _ = ∫ y in Set.Ioc a b, innerIntegral y := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [] with y
      unfold innerIntegral
      rw [intervalIntegral.integral_of_le (le_of_lt zero_lt_one)]

theorem gap1 (a b : ℝ) (ha : -1 < a) (hab : a < b) :
    originalIntegral a b =
      ∫ x in (0 : ℝ)..1,
        Real.sin (Real.log (1 / x)) *
          (∫ y in a..b, Real.rpow x y) := by
  simpa [powerIntegral] using original_eq_weightedPowerIntegral a b

theorem gap2 (a b : ℝ) (ha : -1 < a) (hab : a < b) :
    (∫ x in (0 : ℝ)..1,
        Real.sin (Real.log (1 / x)) *
          (∫ y in a..b, Real.rpow x y)) =
      ∫ y in a..b, innerIntegral y := by
  simpa [powerIntegral] using weighted_fubini_ordered a b ha hab

theorem gap3 (a b : ℝ) (ha : -1 < a) (hab : a < b) :
    originalIntegral a b = ∫ y in a..b, innerIntegral y :=
  (gap1 a b ha hab).trans (gap2 a b ha hab)

theorem gap8 (a b : ℝ) (ha : -1 < a) (hab : a < b) :
    originalIntegral a b =
      ∫ y in a..b, 1 / (1 + (1 + y) ^ 2) := by
  rw [gap3 a b ha hab]
  apply intervalIntegral.integral_congr
  intro y hy
  rw [Set.uIcc_of_le hab.le] at hy
  exact innerIntegral_value y (lt_of_lt_of_le ha hy.1)

private theorem arctanPrimitive_deriv (y : ℝ) :
    HasDerivAt arctanPrimitive (1 / (1 + (1 + y) ^ 2)) y := by
  have hlin : HasDerivAt (fun t : ℝ => 1 + t) 1 y := by
    convert (hasDerivAt_const y 1).add (hasDerivAt_id y) using 1 <;>
      simp
  unfold arctanPrimitive
  convert (Real.hasDerivAt_arctan (1 + y)).comp y hlin using 1 <;>
    simp

theorem gap9 (a b : ℝ) (ha : -1 < a) (hab : a < b) :
    (∫ y in a..b, 1 / (1 + (1 + y) ^ 2)) =
      arctanPrimitive b - arctanPrimitive a := by
  have hcont : Continuous
      (fun y : ℝ => 1 / (1 + (1 + y) ^ 2)) := by
    exact continuous_const.div
      (continuous_const.add ((continuous_const.add continuous_id).pow 2))
      (fun y => by positivity)
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun y _ => arctanPrimitive_deriv y) (hcont.intervalIntegrable a b)

theorem gap10 (a b : ℝ) (ha : -1 < a) (hab : a < b) :
    arctanPrimitive b - arctanPrimitive a =
      Real.arctan (1 + b) - Real.arctan (1 + a) :=
  rfl

theorem gap11 (a b : ℝ) (ha : -1 < a) (hab : a < b) :
    Real.arctan (1 + b) - Real.arctan (1 + a) =
      Real.arctan ((b - a) / (1 + (1 + b) * (1 + a))) := by
  have hapos : 0 < 1 + a := by linarith
  have hbpos : 0 < 1 + b := by linarith
  have hmul : (1 + b) * (-(1 + a)) < 1 := by
    have hneg : (1 + b) * (-(1 + a)) < 0 :=
      mul_neg_of_pos_of_neg hbpos (neg_neg_of_pos hapos)
    linarith
  have h := Real.arctan_add hmul
  rw [Real.arctan_neg] at h
  convert h using 1 <;> ring

theorem gap12 (a b : ℝ) (ha : -1 < a) (hab : a < b) :
    originalIntegral a b =
      Real.arctan ((b - a) / (1 + (1 + b) * (1 + a))) := by
  calc
    originalIntegral a b =
        ∫ y in a..b, 1 / (1 + (1 + y) ^ 2) := gap8 a b ha hab
    _ = arctanPrimitive b - arctanPrimitive a := gap9 a b ha hab
    _ = Real.arctan (1 + b) - Real.arctan (1 + a) := gap10 a b ha hab
    _ = Real.arctan ((b - a) / (1 + (1 + b) * (1 + a))) :=
      gap11 a b ha hab

end

end ProofGap.Exercise3738_1
