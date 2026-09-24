import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3738_2

noncomputable section

open Filter
open scoped Interval Topology

def quotient (a b x : ℝ) : ℝ :=
  (Real.rpow x b - Real.rpow x a) / Real.log x

def originalIntegral (a b : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..1,
    Real.cos (Real.log (1 / x)) * quotient a b x

def innerIntegral (y : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..1,
    Real.cos (Real.log (1 / x)) * Real.rpow x y

def rationalIntegral (a b : ℝ) : ℝ :=
  ∫ y in a..b, (1 + y) / (1 + (1 + y) ^ 2)

def logarithmicPrimitive (y : ℝ) : ℝ :=
  (1 / 2 : ℝ) * Real.log (1 + (1 + y) ^ 2)

private def powerIntegral (a b x : ℝ) : ℝ :=
  ∫ y in a..b, Real.rpow x y

private def cosPrimitive (y x : ℝ) : ℝ :=
  Real.rpow x (y + 1) *
      ((y + 1) * Real.cos (Real.log x) + Real.sin (Real.log x)) /
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

private theorem cosPrimitive_deriv (y x : ℝ) (hx : 0 < x) :
    HasDerivAt (cosPrimitive y)
      (Real.cos (Real.log (1 / x)) * Real.rpow x y) x := by
  have hpow := Real.hasDerivAt_rpow_const
    (x := x) (p := y + 1) (Or.inl hx.ne')
  have hlog := Real.hasDerivAt_log hx.ne'
  have hcos := (Real.hasDerivAt_cos (Real.log x)).comp x hlog
  have hsin := (Real.hasDerivAt_sin (Real.log x)).comp x hlog
  have hbracket := (hcos.const_mul (y + 1)).add hsin
  have h := (hpow.mul hbracket).div_const (1 + (y + 1) ^ 2)
  convert h using 1
  have hden : 1 + (y + 1) ^ 2 ≠ 0 := by positivity
  simp only [Pi.add_apply, Function.comp_apply]
  rw [one_div, Real.log_inv, Real.cos_neg]
  rw [show y + 1 - 1 = y by ring]
  field_simp [hden, hx.ne']
  rw [Real.rpow_add_one hx.ne' y]
  rw [show Real.rpow x y = x ^ y by rfl]
  simp only [Real.rpow_def_of_pos hx]
  ring

private theorem cosIntegrand_intervalIntegrable (y : ℝ) (hy : 0 ≤ y) :
    IntervalIntegrable
      (fun x : ℝ => Real.cos (Real.log (1 / x)) * Real.rpow x y)
      MeasureTheory.volume 0 1 := by
  have hpow := intervalIntegral.intervalIntegrable_rpow
    (a := (0 : ℝ)) (b := 1) (μ := MeasureTheory.volume) (Or.inl hy)
  have hmeas : Measurable
      (fun x : ℝ => Real.cos (Real.log (1 / x))) :=
    Real.measurable_cos.comp
      (Real.measurable_log.comp (measurable_const.div measurable_id))
  have hbound : ∀ x : ℝ,
      ‖Real.cos (Real.log (1 / x))‖ ≤ (1 : ℝ) := by
    intro x
    rw [Real.norm_eq_abs]
    exact abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
  constructor
  · exact hpow.1.bdd_mul hmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall hbound)
  · exact hpow.2.bdd_mul hmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall hbound)

private theorem cosPrimitive_tendsto_zero (y : ℝ) (hy : 0 < y + 1) :
    Tendsto (cosPrimitive y) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hpowCont :
      ContinuousAt (fun x : ℝ => Real.rpow x (y + 1)) 0 :=
    continuousAt_id.rpow continuousAt_const (Or.inr hy)
  have hpowZero : Real.rpow 0 (y + 1) = 0 :=
    Real.zero_rpow hy.ne'
  have hpow :
      Tendsto (fun x : ℝ => Real.rpow x (y + 1))
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [hpowZero] using hpowCont.tendsto.mono_left inf_le_left
  let C : ℝ := (|y + 1| + 1) / (1 + (y + 1) ^ 2)
  have hmajor :
      Tendsto (fun x : ℝ => Real.rpow x (y + 1) * C)
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using hpow.mul_const C
  have hbound : ∀ᶠ x : ℝ in 𝓝[>] (0 : ℝ),
      |cosPrimitive y x| ≤ Real.rpow x (y + 1) * C := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hxpos : 0 < x := hx
    have hpowNonneg : 0 ≤ Real.rpow x (y + 1) :=
      Real.rpow_nonneg hxpos.le _
    have hdenpos : 0 < 1 + (y + 1) ^ 2 := by positivity
    have htrig :
        |(y + 1) * Real.cos (Real.log x) + Real.sin (Real.log x)| ≤
          |y + 1| + 1 := by
      calc
        |(y + 1) * Real.cos (Real.log x) + Real.sin (Real.log x)| ≤
            |(y + 1) * Real.cos (Real.log x)| +
              |Real.sin (Real.log x)| := abs_add_le _ _
        _ = |y + 1| * |Real.cos (Real.log x)| +
              |Real.sin (Real.log x)| := by rw [abs_mul]
        _ ≤ |y + 1| * 1 + 1 := by
          gcongr
          · exact Real.abs_cos_le_one _
          · exact Real.abs_sin_le_one _
        _ = |y + 1| + 1 := by ring
    dsimp [cosPrimitive, C]
    have hpowNonneg' : 0 ≤ x ^ (y + 1) := by exact hpowNonneg
    rw [abs_div, abs_mul, abs_of_nonneg hpowNonneg',
      abs_of_pos hdenpos]
    calc
      x ^ (y + 1) *
            |(y + 1) * Real.cos (Real.log x) + Real.sin (Real.log x)| /
          (1 + (y + 1) ^ 2) ≤
          Real.rpow x (y + 1) * (|y + 1| + 1) /
            (1 + (y + 1) ^ 2) := by
        rw [show x ^ (y + 1) = Real.rpow x (y + 1) by rfl]
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left htrig hpowNonneg) hdenpos.le
      _ = x ^ (y + 1) *
          ((|y + 1| + 1) / (1 + (y + 1) ^ 2)) := by
        rw [show Real.rpow x (y + 1) = x ^ (y + 1) by rfl]
        ring
  apply (tendsto_zero_iff_abs_tendsto_zero (cosPrimitive y)).2
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun x => abs_nonneg _
  · simpa only [Function.comp_apply] using hbound
  · exact hmajor

private theorem innerIntegral_value (y : ℝ) (hy : 0 < y) :
    innerIntegral y = (1 + y) / (1 + (1 + y) ^ 2) := by
  have hint := cosIntegrand_intervalIntegrable y (le_of_lt hy)
  have hzero : Tendsto (cosPrimitive y) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    cosPrimitive_tendsto_zero y (by linarith)
  have hone :
      Tendsto (cosPrimitive y) (𝓝[<] (1 : ℝ))
        (𝓝 ((1 + y) / (1 + (1 + y) ^ 2))) := by
    have hc := (cosPrimitive_deriv y 1 zero_lt_one).continuousAt.tendsto
    convert hc.mono_left inf_le_left using 1
    simp [cosPrimitive]
    ring
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto
    (a := (0 : ℝ)) (b := 1) zero_lt_one
    (fun x hx => cosPrimitive_deriv y x hx.1) hint hzero hone
  simpa [innerIntegral] using hi

private theorem original_eq_weightedPowerIntegral (a b : ℝ) :
    originalIntegral a b =
      ∫ x in (0 : ℝ)..1,
        Real.cos (Real.log (1 / x)) * powerIntegral a b x := by
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
    (c d : ℝ) (hc : 0 < c) (hcd : c ≤ d) :
    (∫ x in (0 : ℝ)..1,
      Real.cos (Real.log (1 / x)) * powerIntegral c d x) =
        ∫ y in c..d, innerIntegral y := by
  let f : ℝ × ℝ → ℝ := fun p =>
    Real.cos (Real.log (1 / p.1)) * Real.rpow p.1 p.2
  have hbaseCont : ContinuousOn (fun p : ℝ × ℝ => Real.rpow p.1 p.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc c d) := by
    intro p hp
    have hp2 : 0 < p.2 := lt_of_lt_of_le hc hp.2.1
    exact (continuous_fst.continuousAt.rpow continuous_snd.continuousAt
      (by
        by_cases hp1 : p.1 = 0
        · exact Or.inr hp2
        · exact Or.inl hp1)).continuousWithinAt
  have hbase : MeasureTheory.IntegrableOn
      (fun p : ℝ × ℝ => Real.rpow p.1 p.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc c d)
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod
        (MeasureTheory.volume : MeasureTheory.Measure ℝ)) :=
    hbaseCont.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have hcosMeas : Measurable (fun p : ℝ × ℝ =>
      Real.cos (Real.log (1 / p.1))) :=
    Real.measurable_cos.comp
      (Real.measurable_log.comp (measurable_const.div measurable_fst))
  have hcosBound : ∀ p : ℝ × ℝ,
      ‖Real.cos (Real.log (1 / p.1))‖ ≤ (1 : ℝ) := by
    intro p
    rw [Real.norm_eq_abs]
    exact Real.abs_cos_le_one _
  have hintClosed : MeasureTheory.IntegrableOn f
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc c d)
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod
        (MeasureTheory.volume : MeasureTheory.Measure ℝ)) := by
    exact hbase.bdd_mul hcosMeas.aestronglyMeasurable
      (Filter.Eventually.of_forall hcosBound)
  have hsub : Set.Ioc (0 : ℝ) 1 ×ˢ Set.Ioc c d ⊆
      Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc c d := by
    apply Set.prod_mono
    · intro x hx
      exact ⟨le_of_lt hx.1, hx.2⟩
    · intro y hy
      exact ⟨le_of_lt hy.1, hy.2⟩
  have hintOpen : MeasureTheory.IntegrableOn f
      (Set.Ioc (0 : ℝ) 1 ×ˢ Set.Ioc c d)
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod
        (MeasureTheory.volume : MeasureTheory.Measure ℝ)) :=
    hintClosed.mono_set hsub
  have hmeas :
      MeasurableSet (Set.Ioc (0 : ℝ) 1 ×ˢ Set.Ioc c d) :=
    measurableSet_Ioc.prod measurableSet_Ioc
  have hind : MeasureTheory.Integrable
      ((Set.Ioc (0 : ℝ) 1 ×ˢ Set.Ioc c d).indicator f)
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod
        (MeasureTheory.volume : MeasureTheory.Measure ℝ)) := by
    rw [MeasureTheory.integrable_indicator_iff hmeas]
    exact hintOpen
  let g : ℝ → ℝ → ℝ := fun x y =>
    (Set.Ioc (0 : ℝ) 1).indicator
      (fun x => (Set.Ioc c d).indicator
        (fun y => Real.cos (Real.log (1 / x)) * Real.rpow x y) y) x
  have huncurry : Function.uncurry g =
      (Set.Ioc (0 : ℝ) 1 ×ˢ Set.Ioc c d).indicator f := by
    funext p
    by_cases hx : p.1 ∈ Set.Ioc (0 : ℝ) 1
    · by_cases hy : p.2 ∈ Set.Ioc c d
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
          ∫ y in Set.Ioc c d,
            Real.cos (Real.log (1 / x)) * Real.rpow x y := by
    calc
      (∫ x : ℝ, ∫ y : ℝ, g x y
        ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ)
        ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ)) =
          ∫ x : ℝ, (Set.Ioc (0 : ℝ) 1).indicator
            (fun x => ∫ y : ℝ, (Set.Ioc c d).indicator
              (fun y => Real.cos (Real.log (1 / x)) * Real.rpow x y) y
              ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ)) x
            ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards [] with x
        by_cases hx : x ∈ Set.Ioc (0 : ℝ) 1
        · simp [g, hx]
        · simp [g, hx]
      _ = ∫ x in Set.Ioc (0 : ℝ) 1,
            ∫ y : ℝ, (Set.Ioc c d).indicator
              (fun y => Real.cos (Real.log (1 / x)) * Real.rpow x y) y
              ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
        exact MeasureTheory.integral_indicator measurableSet_Ioc
      _ = ∫ x in Set.Ioc (0 : ℝ) 1,
            ∫ y in Set.Ioc c d,
              Real.cos (Real.log (1 / x)) * Real.rpow x y := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards [] with x
        exact MeasureTheory.integral_indicator measurableSet_Ioc
  have hright :
      (∫ y : ℝ, ∫ x : ℝ, g x y
        ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ)
        ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ)) =
        ∫ y in Set.Ioc c d,
          ∫ x in Set.Ioc (0 : ℝ) 1,
            Real.cos (Real.log (1 / x)) * Real.rpow x y := by
    calc
      (∫ y : ℝ, ∫ x : ℝ, g x y
        ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ)
        ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ)) =
          ∫ y : ℝ, (Set.Ioc c d).indicator
            (fun y => ∫ x : ℝ, (Set.Ioc (0 : ℝ) 1).indicator
              (fun x => Real.cos (Real.log (1 / x)) * Real.rpow x y) x
              ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ)) y
            ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards [] with y
        by_cases hy : y ∈ Set.Ioc c d
        · simp [g, hy]
        · simp [g, hy]
      _ = ∫ y in Set.Ioc c d,
            ∫ x : ℝ, (Set.Ioc (0 : ℝ) 1).indicator
              (fun x => Real.cos (Real.log (1 / x)) * Real.rpow x y) x
              ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
        exact MeasureTheory.integral_indicator measurableSet_Ioc
      _ = ∫ y in Set.Ioc c d,
            ∫ x in Set.Ioc (0 : ℝ) 1,
              Real.cos (Real.log (1 / x)) * Real.rpow x y := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards [] with y
        exact MeasureTheory.integral_indicator measurableSet_Ioc
  rw [intervalIntegral.integral_of_le (le_of_lt zero_lt_one),
    intervalIntegral.integral_of_le hcd]
  calc
    (∫ x in Set.Ioc (0 : ℝ) 1,
      Real.cos (Real.log (1 / x)) * powerIntegral c d x) =
        ∫ x in Set.Ioc (0 : ℝ) 1,
          ∫ y in Set.Ioc c d,
            Real.cos (Real.log (1 / x)) * Real.rpow x y := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [] with x
      unfold powerIntegral
      rw [intervalIntegral.integral_of_le hcd,
        MeasureTheory.integral_const_mul]
    _ = ∫ y in Set.Ioc c d,
          ∫ x in Set.Ioc (0 : ℝ) 1,
            Real.cos (Real.log (1 / x)) * Real.rpow x y :=
      hleft.symm.trans (hswap.trans hright)
    _ = ∫ y in Set.Ioc c d, innerIntegral y := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [] with y
      unfold innerIntegral
      rw [intervalIntegral.integral_of_le (le_of_lt zero_lt_one)]

private theorem weighted_fubini (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (∫ x in (0 : ℝ)..1,
      Real.cos (Real.log (1 / x)) * powerIntegral a b x) =
        ∫ y in a..b, innerIntegral y := by
  rcases le_total a b with hab | hba
  · exact weighted_fubini_ordered a b ha hab
  · have hswap := weighted_fubini_ordered b a hb hba
    calc
      (∫ x in (0 : ℝ)..1,
        Real.cos (Real.log (1 / x)) * powerIntegral a b x) =
          ∫ x in (0 : ℝ)..1,
            -(Real.cos (Real.log (1 / x)) * powerIntegral b a x) := by
        apply intervalIntegral.integral_congr
        intro x _
        change Real.cos (Real.log (1 / x)) * powerIntegral a b x =
          -(Real.cos (Real.log (1 / x)) * powerIntegral b a x)
        have hp : powerIntegral a b x = -powerIntegral b a x := by
          unfold powerIntegral
          rw [intervalIntegral.integral_symm]
        rw [hp]
        ring
      _ = -(∫ x in (0 : ℝ)..1,
          Real.cos (Real.log (1 / x)) * powerIntegral b a x) := by
        rw [intervalIntegral.integral_neg]
      _ = -(∫ y in b..a, innerIntegral y) := congrArg Neg.neg hswap
      _ = ∫ y in a..b, innerIntegral y := by
        rw [intervalIntegral.integral_symm, neg_neg]

theorem gap1 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    originalIntegral a b = ∫ y in a..b, innerIntegral y := by
  calc
    originalIntegral a b =
        ∫ x in (0 : ℝ)..1,
          Real.cos (Real.log (1 / x)) * powerIntegral a b x :=
      original_eq_weightedPowerIntegral a b
    _ = ∫ y in a..b, innerIntegral y := weighted_fubini a b ha hb

theorem gap2 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (∫ y in a..b, innerIntegral y) = rationalIntegral a b := by
  unfold rationalIntegral
  apply intervalIntegral.integral_congr
  intro y hy
  have hypos : 0 < y := by
    rcases Set.mem_uIcc.mp hy with h | h
    · exact lt_of_lt_of_le ha h.1
    · exact lt_of_lt_of_le hb h.1
  exact innerIntegral_value y hypos

theorem gap3 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    originalIntegral a b = rationalIntegral a b :=
  (gap1 a b ha hb).trans (gap2 a b ha hb)

private theorem logarithmicPrimitive_deriv (y : ℝ) :
    HasDerivAt logarithmicPrimitive
      ((1 + y) / (1 + (1 + y) ^ 2)) y := by
  have hlin : HasDerivAt (fun t : ℝ => 1 + t) 1 y :=
    by
      convert (hasDerivAt_const y 1).add (hasDerivAt_id y) using 1 <;>
        simp
  have harg : HasDerivAt (fun t : ℝ => 1 + (1 + t) ^ 2)
      (2 * (1 + y)) y := by
    convert (hasDerivAt_const y 1).add (hlin.pow 2) using 1 <;>
      norm_num <;> ring
  have hne : 1 + (1 + y) ^ 2 ≠ 0 := by positivity
  have hlog :=
    (Real.hasDerivAt_log hne).comp y harg
  have h := hlog.const_mul (1 / 2 : ℝ)
  convert h using 1 <;>
    simp [logarithmicPrimitive] <;>
    field_simp [hne] <;> ring

theorem gap4 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    originalIntegral a b =
      logarithmicPrimitive b - logarithmicPrimitive a := by
  rw [gap3 a b ha hb]
  unfold rationalIntegral
  have hcont : Continuous
      (fun y : ℝ => (1 + y) / (1 + (1 + y) ^ 2)) := by
    exact (continuous_const.add continuous_id).div
      (continuous_const.add ((continuous_const.add continuous_id).pow 2))
      (fun y => by positivity)
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun y _ => logarithmicPrimitive_deriv y)
    (hcont.intervalIntegrable a b)

theorem gap5 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    logarithmicPrimitive b - logarithmicPrimitive a =
      (1 / 2 : ℝ) *
        Real.log ((b ^ 2 + 2 * b + 2) / (a ^ 2 + 2 * a + 2)) := by
  have hapos : 0 < a ^ 2 + 2 * a + 2 := by nlinarith [sq_nonneg (a + 1)]
  have hbpos : 0 < b ^ 2 + 2 * b + 2 := by nlinarith [sq_nonneg (b + 1)]
  have haeq : 1 + (1 + a) ^ 2 = a ^ 2 + 2 * a + 2 := by ring
  have hbeq : 1 + (1 + b) ^ 2 = b ^ 2 + 2 * b + 2 := by ring
  unfold logarithmicPrimitive
  rw [haeq, hbeq,
    Real.log_div (ne_of_gt hbpos) (ne_of_gt hapos)]
  ring

theorem gap6 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    originalIntegral a b =
      (1 / 2 : ℝ) *
        Real.log ((b ^ 2 + 2 * b + 2) / (a ^ 2 + 2 * a + 2)) :=
  (gap4 a b ha hb).trans (gap5 a b ha hb)

end

end ProofGap.Exercise3738_2
