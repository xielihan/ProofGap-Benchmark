import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4039

noncomputable section

open MeasureTheory
open scoped Interval

def upperHeight (x y : ℝ) : ℝ :=
  Real.sqrt (2 * x * y)

def upperDx (x y : ℝ) : ℝ :=
  y / upperHeight x y

def upperDy (x y : ℝ) : ℝ :=
  x / upperHeight x y

def rawAreaFactor (x y : ℝ) : ℝ :=
  Real.sqrt (1 + upperDx x y ^ 2 + upperDy x y ^ 2)

def areaFactor (x y : ℝ) : ℝ :=
  1 / Real.sqrt 2 * ((x + y) / Real.sqrt (x * y))

def baseRegion : Set (ℝ × ℝ) :=
  {p | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ 1}

def surfaceArea : ℝ :=
  2 * ∫ p in baseRegion, areaFactor p.1 p.2

private def invSqrt (x : ℝ) : ℝ :=
  x ^ (-(1 : ℝ) / 2)

private theorem invSqrt_eq_one_div_sqrt {x : ℝ} (hx : 0 ≤ x) :
    invSqrt x = 1 / Real.sqrt x := by
  rcases hx.eq_or_lt with rfl | hx
  · simp [invSqrt]
  · rw [invSqrt, show -(1 : ℝ) / 2 = -(1 / 2 : ℝ) by ring,
      Real.rpow_neg hx.le, Real.sqrt_eq_rpow]
    simp only [one_div]

private theorem integrableOn_one_div_sqrt_Icc :
    IntegrableOn (fun x : ℝ => 1 / Real.sqrt x) (Set.Icc 0 1) := by
  have hrpow :
      IntervalIntegrable (fun x : ℝ => x ^ (-(1 : ℝ) / 2))
        volume 0 1 :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have hrpowOn :
      IntegrableOn (fun x : ℝ => x ^ (-(1 : ℝ) / 2))
        (Set.Icc 0 1) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).1 hrpow
  refine hrpowOn.congr_fun ?_ measurableSet_Icc
  intro x hx
  exact invSqrt_eq_one_div_sqrt hx.1

private theorem triangle_integrand_eq
    (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (x + y) / Real.sqrt (x * y) =
      Real.sqrt x * (1 / Real.sqrt y) +
        (1 / Real.sqrt x) * Real.sqrt y := by
  rcases hx.eq_or_lt with rfl | hx
  · simp
  rcases hy.eq_or_lt with rfl | hy
  · simp
  have hsx : Real.sqrt x ≠ 0 := (Real.sqrt_pos.2 hx).ne'
  have hsy : Real.sqrt y ≠ 0 := (Real.sqrt_pos.2 hy).ne'
  have hsx2 : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx.le
  have hsy2 : Real.sqrt y ^ 2 = y := Real.sq_sqrt hy.le
  rw [Real.sqrt_mul hx.le]
  field_simp [hsx, hsy]
  nlinarith

private theorem baseRegion_isClosed : IsClosed baseRegion := by
  rw [baseRegion]
  simp only [Set.setOf_and]
  exact
    (isClosed_le continuous_const continuous_fst).inter
      ((isClosed_le continuous_const continuous_snd).inter
        (isClosed_le (continuous_fst.add continuous_snd) continuous_const))

private theorem baseRegion_subset_square :
    baseRegion ⊆ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 := by
  rintro p ⟨hx, hy, hsum⟩
  exact ⟨⟨hx, by linarith⟩, ⟨hy, by linarith⟩⟩

private theorem triangle_integrand_integrable :
    IntegrableOn
      (fun p : ℝ × ℝ =>
        (p.1 + p.2) / Real.sqrt (p.1 * p.2))
      baseRegion := by
  let s : Set ℝ := Set.Icc 0 1
  let q : ℝ × ℝ → ℝ :=
    fun p =>
      Real.sqrt p.1 * (1 / Real.sqrt p.2) +
        (1 / Real.sqrt p.1) * Real.sqrt p.2
  have hsqrtOn : IntegrableOn Real.sqrt s := by
    dsimp [s]
    exact Real.continuous_sqrt.integrableOn_Icc
  have hinvOn :
      IntegrableOn (fun x : ℝ => 1 / Real.sqrt x) s := by
    simpa [s] using integrableOn_one_div_sqrt_Icc
  have hqRestricted :
      Integrable q
        ((volume.restrict s).prod (volume.restrict s)) := by
    dsimp [q]
    exact
      (hsqrtOn.mul_prod hinvOn).add
        (hinvOn.mul_prod hsqrtOn)
  have hqSquare :
      IntegrableOn q (s ×ˢ s) := by
    change
      Integrable q
        ((volume.prod volume).restrict (s ×ˢ s))
    rw [← Measure.prod_restrict]
    exact hqRestricted
  have hqTriangle : IntegrableOn q baseRegion := by
    exact hqSquare.mono_set (by simpa [s] using baseRegion_subset_square)
  refine hqTriangle.congr_fun ?_ baseRegion_isClosed.measurableSet
  intro p hp
  exact (triangle_integrand_eq p.1 p.2 hp.1 hp.2.1).symm

private theorem ae_real_ne (u : ℝ) :
    ∀ᵐ x : ℝ ∂(volume : Measure ℝ), x ≠ u := by
  rw [ae_iff]
  simpa using measure_singleton u

private theorem integral_indicator_Icc_eq_interval
    (u v : ℝ) (f : ℝ → ℝ) (huv : u ≤ v) :
    (∫ x : ℝ, (Set.Icc u v).indicator f x) =
      ∫ x in u..v, f x := by
  rw [intervalIntegral.integral_of_le huv]
  rw [← integral_indicator measurableSet_Ioc]
  apply integral_congr_ae
  filter_upwards [ae_real_ne u] with x hx
  by_cases hxc : x ∈ Set.Icc u v
  · have hxo : x ∈ Set.Ioc u v :=
      ⟨lt_of_le_of_ne hxc.1 (Ne.symm hx), hxc.2⟩
    simp [hxc, hxo]
  · have hxo : x ∉ Set.Ioc u v := fun h => hxc ⟨h.1.le, h.2⟩
    simp [hxc, hxo]

theorem gap1 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    rawAreaFactor x y =
      Real.sqrt
        (1 + y ^ 2 / upperHeight x y ^ 2 +
          x ^ 2 / upperHeight x y ^ 2) := by
  simp only [rawAreaFactor, upperDx, upperDy, div_pow]

theorem gap2 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    Real.sqrt
        (1 + y ^ 2 / upperHeight x y ^ 2 +
          x ^ 2 / upperHeight x y ^ 2) =
      Real.sqrt
        ((x ^ 2 + y ^ 2 + upperHeight x y ^ 2) /
          upperHeight x y ^ 2) := by
  have hxy : 0 < 2 * x * y := by positivity
  have hh :
      upperHeight x y ^ 2 = 2 * x * y := by
    simp only [upperHeight, Real.sq_sqrt hxy.le]
  congr 1
  rw [hh]
  field_simp [hxy.ne']
  ring

theorem gap3 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    Real.sqrt
        ((x ^ 2 + y ^ 2 + upperHeight x y ^ 2) /
          upperHeight x y ^ 2) =
      1 / Real.sqrt 2 *
        Real.sqrt ((x ^ 2 + y ^ 2 + 2 * x * y) / (x * y)) := by
  have hxy : 0 < x * y := mul_pos hx hy
  have hh :
      upperHeight x y ^ 2 = 2 * x * y := by
    simp only [upperHeight, Real.sq_sqrt (by positivity : 0 ≤ 2 * x * y)]
  let A : ℝ := x ^ 2 + y ^ 2 + 2 * x * y
  have hA : 0 ≤ A := by
    dsimp [A]
    nlinarith [sq_nonneg (x + y)]
  rw [hh]
  change Real.sqrt (A / (2 * x * y)) =
    1 / Real.sqrt 2 * Real.sqrt (A / (x * y))
  rw [Real.sqrt_div hA, Real.sqrt_div hA]
  rw [show 2 * x * y = 2 * (x * y) by ring,
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  ring

theorem gap4 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    1 / Real.sqrt 2 *
        Real.sqrt ((x ^ 2 + y ^ 2 + 2 * x * y) / (x * y)) =
      areaFactor x y := by
  have hsum : 0 < x + y := add_pos hx hy
  rw [show x ^ 2 + y ^ 2 + 2 * x * y = (x + y) ^ 2 by ring]
  rw [Real.sqrt_div (sq_nonneg (x + y)), Real.sqrt_sq_eq_abs,
    abs_of_pos hsum]
  rfl

theorem gap5 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    rawAreaFactor x y = areaFactor x y := by
  rw [gap1 x y hx hy, gap2 x y hx hy, gap3 x y hx hy,
    gap4 x y hx hy]

theorem gap6 :
    surfaceArea =
      2 / Real.sqrt 2 *
        ∫ x in (0 : ℝ)..1,
          ∫ y in (0 : ℝ)..1 - x,
            (x + y) / Real.sqrt (x * y) := by
  let h : ℝ × ℝ → ℝ :=
    fun p => (p.1 + p.2) / Real.sqrt (p.1 * p.2)
  have hmeas : MeasurableSet baseRegion :=
    baseRegion_isClosed.measurableSet
  have hintOn : IntegrableOn h baseRegion := by
    simpa [h] using triangle_integrand_integrable
  have hind : Integrable (baseRegion.indicator h) :=
    (integrable_indicator_iff hmeas).2 hintOn
  have hindicator (x y : ℝ) :
      baseRegion.indicator h (x, y) =
        (Set.Icc (0 : ℝ) 1).indicator
          (fun x =>
            (Set.Icc (0 : ℝ) (1 - x)).indicator
              (fun y => (x + y) / Real.sqrt (x * y)) y) x := by
    by_cases hx : x ∈ Set.Icc (0 : ℝ) 1
    · by_cases hy : y ∈ Set.Icc (0 : ℝ) (1 - x)
      · have hp : (x, y) ∈ baseRegion := by
          exact ⟨hx.1, hy.1, by linarith [hy.2]⟩
        simp [hp, hx, hy, h]
      · have hp : (x, y) ∉ baseRegion := by
          intro hp
          apply hy
          exact ⟨hp.2.1, by linarith [hp.2.2]⟩
        simp [hp, hx, hy]
    · have hp : (x, y) ∉ baseRegion := by
        intro hp
        apply hx
        exact ⟨hp.1, by linarith [hp.2.1, hp.2.2]⟩
      simp [hp, hx]
  have hslice :
      (∫ p in baseRegion, h p) =
        ∫ x in (0 : ℝ)..1,
          ∫ y in (0 : ℝ)..1 - x,
            (x + y) / Real.sqrt (x * y) := by
    rw [← integral_indicator hmeas]
    change
      (∫ p : ℝ × ℝ, baseRegion.indicator h p
        ∂((volume : Measure ℝ).prod volume)) = _
    rw [integral_prod _ hind]
    have hcollapse (x : ℝ) :
        (∫ y : ℝ,
          (Set.Icc (0 : ℝ) 1).indicator
            (fun x =>
              (Set.Icc (0 : ℝ) (1 - x)).indicator
                (fun y => (x + y) / Real.sqrt (x * y)) y) x) =
          (Set.Icc (0 : ℝ) 1).indicator
            (fun x =>
              ∫ y : ℝ,
                (Set.Icc (0 : ℝ) (1 - x)).indicator
                  (fun y => (x + y) / Real.sqrt (x * y)) y) x := by
      by_cases hx : x ∈ Set.Icc (0 : ℝ) 1 <;> simp [hx]
    simp_rw [hindicator, hcollapse]
    rw [integral_indicator_Icc_eq_interval (0 : ℝ) 1 _ zero_le_one]
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le zero_le_one] at hx
    exact integral_indicator_Icc_eq_interval
      (0 : ℝ) (1 - x) _ (by linarith [hx.2])
  rw [surfaceArea]
  change
    2 * (∫ p in baseRegion, (1 / Real.sqrt 2) * h p) =
      2 / Real.sqrt 2 *
        ∫ x in (0 : ℝ)..1,
          ∫ y in (0 : ℝ)..1 - x,
            (x + y) / Real.sqrt (x * y)
  rw [MeasureTheory.integral_const_mul, hslice]
  ring

private theorem inner_triangle_integral
    (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    (∫ y in (0 : ℝ)..1 - x,
        (x + y) / Real.sqrt (x * y)) =
      2 * Real.sqrt (x * (1 - x)) +
        2 / (3 * Real.sqrt x) * (1 - x) * Real.sqrt (1 - x) := by
  rcases hx0.eq_or_lt with rfl | hx
  · simp
  let b : ℝ := 1 - x
  have hb : 0 ≤ b := by dsimp [b]; linarith
  have hneg :
      IntervalIntegrable (fun y : ℝ => y ^ (-(1 : ℝ) / 2))
        volume 0 b :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have hpos :
      IntervalIntegrable (fun y : ℝ => y ^ ((1 : ℝ) / 2))
        volume 0 b :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have hrewrite :
      (∫ y in (0 : ℝ)..b,
          (x + y) / Real.sqrt (x * y)) =
        ∫ y in (0 : ℝ)..b,
          Real.sqrt x * y ^ (-(1 : ℝ) / 2) +
            (1 / Real.sqrt x) * y ^ ((1 : ℝ) / 2) := by
    apply intervalIntegral.integral_congr
    intro y hy
    rw [Set.uIcc_of_le hb] at hy
    change
      (x + y) / Real.sqrt (x * y) =
        Real.sqrt x * y ^ (-(1 : ℝ) / 2) +
          (1 / Real.sqrt x) * y ^ ((1 : ℝ) / 2)
    rw [triangle_integrand_eq x y hx.le hy.1]
    rw [← invSqrt_eq_one_div_sqrt hy.1]
    simp only [invSqrt, Real.sqrt_eq_rpow]
  have hhalf :
      b ^ ((1 : ℝ) / 2) = Real.sqrt b := by
    exact (Real.sqrt_eq_rpow b).symm
  have hthreehalf :
      b ^ ((3 : ℝ) / 2) = b * Real.sqrt b := by
    calc
      b ^ ((3 : ℝ) / 2) =
          b ^ ((1 : ℝ) + (1 : ℝ) / 2) := by congr 1 <;> ring
      _ = b ^ (1 : ℝ) * b ^ ((1 : ℝ) / 2) :=
        Real.rpow_add_of_nonneg hb (by norm_num) (by norm_num)
      _ = b * Real.sqrt b := by rw [Real.rpow_one, hhalf]
  rw [show 1 - x = b by rfl, hrewrite]
  rw [intervalIntegral.integral_add
      (hneg.const_mul (Real.sqrt x))
      (hpos.const_mul (1 / Real.sqrt x)),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    integral_rpow (Or.inl (by norm_num)),
    integral_rpow (Or.inl (by norm_num))]
  norm_num
  rw [hhalf, hthreehalf]
  rw [Real.sqrt_mul hx.le]
  dsimp [b]
  ring

theorem gap7 :
    surfaceArea =
      2 / Real.sqrt 2 *
        ∫ x in (0 : ℝ)..1,
          2 * Real.sqrt (x * (1 - x)) +
            2 / (3 * Real.sqrt x) * (1 - x) * Real.sqrt (1 - x) := by
  rw [gap6]
  apply congrArg (fun z : ℝ => 2 / Real.sqrt 2 * z)
  apply intervalIntegral.integral_congr
  intro x hx
  rw [Set.uIcc_of_le zero_le_one] at hx
  exact inner_triangle_integral x hx.1 hx.2

theorem gap8 :
    surfaceArea =
      Real.sqrt 2 *
        ∫ x in (0 : ℝ)..1,
          2 * Real.sqrt (1 - x) * (1 + 2 * x) /
            (3 * Real.sqrt x) := by
  rw [gap7]
  have hsqrt2 : Real.sqrt 2 ≠ 0 :=
    (Real.sqrt_pos.2 (by norm_num)).ne'
  have hsqrt2sq : Real.sqrt 2 ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num)
  have hcoeff : 2 / Real.sqrt 2 = Real.sqrt 2 := by
    field_simp [hsqrt2]
    nlinarith
  rw [hcoeff]
  apply congrArg (fun z : ℝ => Real.sqrt 2 * z)
  apply intervalIntegral.integral_congr
  intro x hxI
  rw [Set.uIcc_of_le zero_le_one] at hxI
  rcases hxI.1.eq_or_lt with rfl | hx
  · simp
  have hsx : Real.sqrt x ≠ 0 := (Real.sqrt_pos.2 hx).ne'
  have hsx2 : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx.le
  change
    2 * Real.sqrt (x * (1 - x)) +
        2 / (3 * Real.sqrt x) * (1 - x) * Real.sqrt (1 - x) =
      2 * Real.sqrt (1 - x) * (1 + 2 * x) /
        (3 * Real.sqrt x)
  rw [Real.sqrt_mul hx.le]
  field_simp [hsx]
  rw [hsx2]
  ring

private theorem square_substitution :
    (∫ x in (0 : ℝ)..1,
        2 * Real.sqrt (1 - x) * (1 + 2 * x) /
          (3 * Real.sqrt x)) =
      4 / 3 *
        ∫ t in (0 : ℝ)..1,
          Real.sqrt (1 - t ^ 2) * (1 + 2 * t ^ 2) := by
  let g : ℝ → ℝ :=
    fun x =>
      2 * Real.sqrt (1 - x) * (1 + 2 * x) /
        (3 * Real.sqrt x)
  let k : ℝ → ℝ :=
    fun t => Real.sqrt (1 - t ^ 2) * (1 + 2 * t ^ 2)
  let m : ℝ → ℝ :=
    fun x => 2 / 3 * Real.sqrt (1 - x) * (1 + 2 * x)
  have hmcont : Continuous m := by
    dsimp [m]
    fun_prop
  have hgIcc : IntegrableOn g (Set.Icc (0 : ℝ) 1) := by
    have hprod :
        IntegrableOn
          (fun x : ℝ => (1 / Real.sqrt x) * m x)
          (Set.Icc (0 : ℝ) 1) :=
      integrableOn_one_div_sqrt_Icc.mul_continuousOn
        hmcont.continuousOn isCompact_Icc
    refine hprod.congr_fun ?_ measurableSet_Icc
    intro x hx
    dsimp [g, m]
    ring
  have hfcont :
      ContinuousOn (fun t : ℝ => t ^ 2) [[(0 : ℝ), 1]] := by
    fun_prop
  have hfder :
      ∀ t ∈ Set.Ioo (min (0 : ℝ) 1) (max (0 : ℝ) 1),
        HasDerivWithinAt (fun u : ℝ => u ^ 2) (2 * t) (Set.Ioi t) t := by
    intro t ht
    convert ((hasDerivAt_id t).pow 2).hasDerivWithinAt using 1 <;>
      simp <;> ring
  have hgcont :
      ContinuousOn g
        ((fun t : ℝ => t ^ 2) ''
          Set.Ioo (min (0 : ℝ) 1) (max (0 : ℝ) 1)) := by
    intro z hz
    rcases hz with ⟨t, ht, rfl⟩
    norm_num at ht
    have ht2 : 0 < t ^ 2 := sq_pos_of_pos ht.1
    have hsqrt_ne : Real.sqrt (t ^ 2) ≠ 0 :=
      (Real.sqrt_pos.2 ht2).ne'
    have hcontinuous : ContinuousAt g (t ^ 2) := by
      dsimp [g]
      apply ContinuousAt.div
      · fun_prop
      · fun_prop
      · exact mul_ne_zero (by norm_num) hsqrt_ne
    exact hcontinuous.continuousWithinAt
  have hgimage :
      IntegrableOn g
        ((fun t : ℝ => t ^ 2) '' [[(0 : ℝ), 1]]) := by
    refine hgIcc.mono_set ?_
    rintro z ⟨t, ht, rfl⟩
    rw [Set.uIcc_of_le zero_le_one] at ht
    exact
      ⟨sq_nonneg t,
        by nlinarith [mul_nonneg ht.1 (sub_nonneg.2 ht.2)]⟩
  have hkcont : Continuous k := by
    dsimp [k]
    fun_prop
  have hcompIcc :
      IntegrableOn
        (fun t : ℝ => (g ∘ fun u : ℝ => u ^ 2) t * (2 * t))
        (Set.Icc (0 : ℝ) 1) := by
    have hkOn :
        IntegrableOn (fun t : ℝ => (4 / 3) * k t)
          (Set.Icc (0 : ℝ) 1) :=
      (continuous_const.mul hkcont).integrableOn_Icc
    refine hkOn.congr ?_
    filter_upwards
      [ae_restrict_mem measurableSet_Icc,
        (ae_real_ne 0).filter_mono
          (ae_mono Measure.restrict_le_self)] with t htI ht
    have htpos : 0 < t :=
      lt_of_le_of_ne htI.1 (Ne.symm ht)
    dsimp [g, k, Function.comp_apply]
    rw [Real.sqrt_sq htpos.le]
    field_simp [htpos.ne']
    ring
  have hcomp :
      IntegrableOn
        (fun t : ℝ => (g ∘ fun u : ℝ => u ^ 2) t * (2 * t))
        [[(0 : ℝ), 1]] := by
    simpa [Set.uIcc_of_le zero_le_one] using hcompIcc
  have hsubst :
      (∫ t in (0 : ℝ)..1,
          (g ∘ fun u : ℝ => u ^ 2) t * (2 * t)) =
        ∫ x in (0 : ℝ)..1, g x := by
    simpa using
      (intervalIntegral.integral_comp_mul_deriv'''
        (a := (0 : ℝ)) (b := 1)
        (f := fun t : ℝ => t ^ 2) (f' := fun t : ℝ => 2 * t)
        (g := g) hfcont hfder hgcont hgimage hcomp)
  have hpoint :
      (∫ t in (0 : ℝ)..1,
          (g ∘ fun u : ℝ => u ^ 2) t * (2 * t)) =
        ∫ t in (0 : ℝ)..1, (4 / 3) * k t := by
    refine intervalIntegral.integral_congr_ae' ?_ ?_
    · filter_upwards with t
      intro ht
      have htpos : 0 < t := ht.1
      dsimp [g, k, Function.comp_apply]
      rw [Real.sqrt_sq htpos.le]
      field_simp [htpos.ne']
      ring
    · filter_upwards with t
      intro ht
      exfalso
      linarith [ht.1, ht.2]
  change (∫ x in (0 : ℝ)..1, g x) =
    4 / 3 * ∫ t in (0 : ℝ)..1, k t
  rw [← hsubst, hpoint, intervalIntegral.integral_const_mul]

theorem gap9 :
    Real.sqrt 2 *
        (∫ x in (0 : ℝ)..1,
          2 * Real.sqrt (1 - x) * (1 + 2 * x) /
            (3 * Real.sqrt x)) =
      4 * Real.sqrt 2 / 3 *
        ∫ t in (0 : ℝ)..1,
          Real.sqrt (1 - t ^ 2) * (1 + 2 * t ^ 2) := by
  rw [square_substitution]
  ring

theorem gap10 :
    surfaceArea =
      4 * Real.sqrt 2 / 3 *
        ∫ t in (0 : ℝ)..1,
          Real.sqrt (1 - t ^ 2) * (1 + 2 * t ^ 2) := by
  rw [gap8, gap9]

private theorem integral_even_neg_one_one
    (f : ℝ → ℝ) (hf : Continuous f)
    (heven : ∀ x : ℝ, f (-x) = f x) :
    (∫ x in (-1 : ℝ)..1, f x) =
      2 * ∫ x in (0 : ℝ)..1, f x := by
  have hleft : IntervalIntegrable f volume (-1 : ℝ) 0 :=
    hf.intervalIntegrable _ _
  have hright : IntervalIntegrable f volume 0 1 :=
    hf.intervalIntegrable _ _
  have hsplit :=
    intervalIntegral.integral_add_adjacent_intervals hleft hright
  have hreflect :
      (∫ x in (-1 : ℝ)..(0 : ℝ), f x) =
        ∫ x in (0 : ℝ)..1, f x := by
    calc
      (∫ x in (-1 : ℝ)..(0 : ℝ), f x) =
          ∫ x in (0 : ℝ)..1, f (-x) := by
        simpa using
          (intervalIntegral.integral_comp_neg
            (f := f) (a := (0 : ℝ)) (b := 1)).symm
      _ = ∫ x in (0 : ℝ)..1, f x := by
        apply intervalIntegral.integral_congr
        intro x hx
        exact heven x
  rw [← hsplit, hreflect]
  ring

private theorem quarter_circle_integral :
    (∫ t in (0 : ℝ)..1, Real.sqrt (1 - t ^ 2)) =
      Real.pi / 4 := by
  let f : ℝ → ℝ := fun t => Real.sqrt (1 - t ^ 2)
  have hf : Continuous f := by
    dsimp [f]
    fun_prop
  have heven : ∀ t : ℝ, f (-t) = f t := by
    intro t
    dsimp [f]
    congr 1
    ring
  have hsym := integral_even_neg_one_one f hf heven
  have hfull :
      (∫ t in (-1 : ℝ)..1, f t) = Real.pi / 2 := by
    simpa [f] using integral_sqrt_one_sub_sq
  rw [hfull] at hsym
  change (∫ t in (0 : ℝ)..1, f t) = Real.pi / 4
  linarith

private theorem weighted_quarter_circle_integral :
    (∫ t in (0 : ℝ)..1,
        t ^ 2 * Real.sqrt (1 - t ^ 2)) =
      Real.pi / 16 := by
  let g : ℝ → ℝ :=
    fun t => t ^ 2 * Real.sqrt (1 - t ^ 2)
  have hg : Continuous g := by
    dsimp [g]
    fun_prop
  have hsub :
      (∫ θ in (0 : ℝ)..Real.pi / 2,
          (g ∘ Real.sin) θ * Real.cos θ) =
        ∫ t in (0 : ℝ)..1, g t := by
    simpa using
      (intervalIntegral.integral_comp_mul_deriv
        (a := (0 : ℝ)) (b := Real.pi / 2)
        (f := Real.sin) (f' := Real.cos) (g := g)
        (fun θ hθ => Real.hasDerivAt_sin θ)
        Real.continuous_cos.continuousOn hg)
  have htrig :
      (∫ θ in (0 : ℝ)..Real.pi / 2,
          (g ∘ Real.sin) θ * Real.cos θ) =
        ∫ θ in (0 : ℝ)..Real.pi / 2,
          Real.sin θ ^ 2 * Real.cos θ ^ 2 := by
    apply intervalIntegral.integral_congr
    intro θ hθ
    rw [Set.uIcc_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 2)] at hθ
    change
      Real.sin θ ^ 2 *
          Real.sqrt (1 - Real.sin θ ^ 2) * Real.cos θ =
        Real.sin θ ^ 2 * Real.cos θ ^ 2
    have hlower : -(Real.pi / 2) ≤ θ := by
      have hpihalf : 0 ≤ Real.pi / 2 :=
        div_nonneg Real.pi_nonneg (by norm_num)
      exact (neg_nonpos.2 hpihalf).trans hθ.1
    rw [← Real.cos_eq_sqrt_one_sub_sin_sq
      hlower hθ.2]
    ring
  change (∫ t in (0 : ℝ)..1, g t) = Real.pi / 16
  rw [← hsub, htrig, integral_sin_sq_mul_cos_sq]
  rw [show 4 * (Real.pi / 2) = 2 * Real.pi by ring,
    Real.sin_two_pi]
  simp
  ring

private theorem quarter_circle_polynomial_integral :
    (∫ t in (0 : ℝ)..1,
        Real.sqrt (1 - t ^ 2) * (1 + 2 * t ^ 2)) =
      Real.pi / 4 + Real.pi / 8 := by
  let f : ℝ → ℝ := fun t => Real.sqrt (1 - t ^ 2)
  let q : ℝ → ℝ := fun t => t ^ 2 * Real.sqrt (1 - t ^ 2)
  have hf : IntervalIntegrable f volume 0 1 := by
    dsimp [f]
    exact (by fun_prop : Continuous
      (fun t : ℝ => Real.sqrt (1 - t ^ 2))).intervalIntegrable _ _
  have hq : IntervalIntegrable q volume 0 1 := by
    dsimp [q]
    exact (by fun_prop : Continuous
      (fun t : ℝ => t ^ 2 * Real.sqrt (1 - t ^ 2))).intervalIntegrable _ _
  calc
    (∫ t in (0 : ℝ)..1,
        Real.sqrt (1 - t ^ 2) * (1 + 2 * t ^ 2)) =
        ∫ t in (0 : ℝ)..1, f t + 2 * q t := by
      apply intervalIntegral.integral_congr
      intro t ht
      dsimp [f, q]
      ring
    _ = (∫ t in (0 : ℝ)..1, f t) +
          ∫ t in (0 : ℝ)..1, 2 * q t := by
      rw [intervalIntegral.integral_add hf (hq.const_mul 2)]
    _ = Real.pi / 4 + Real.pi / 8 := by
      rw [intervalIntegral.integral_const_mul]
      change
        (∫ t in (0 : ℝ)..1, Real.sqrt (1 - t ^ 2)) +
            2 *
              ∫ t in (0 : ℝ)..1,
                t ^ 2 * Real.sqrt (1 - t ^ 2) =
          _
      rw [quarter_circle_integral,
        weighted_quarter_circle_integral]
      ring

theorem gap11 :
    surfaceArea =
      4 * Real.sqrt 2 / 3 * (Real.pi / 4 + Real.pi / 8) := by
  rw [gap10, quarter_circle_polynomial_integral]

theorem gap12 :
    4 * Real.sqrt 2 / 3 * (Real.pi / 4 + Real.pi / 8) =
      Real.pi / Real.sqrt 2 := by
  have hsqrt2 : Real.sqrt 2 ≠ 0 :=
    (Real.sqrt_pos.2 (by norm_num)).ne'
  have hsqrt2sq : Real.sqrt 2 ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num)
  field_simp [hsqrt2]
  nlinarith

theorem gap13 :
    surfaceArea = Real.pi / Real.sqrt 2 := by
  rw [gap11, gap12]

end

end ProofGap.Exercise4039
