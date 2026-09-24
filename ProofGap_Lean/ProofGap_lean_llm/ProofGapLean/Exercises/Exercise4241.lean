import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4241

noncomputable section

open scoped Interval

def curveMap (a b t : ℝ) : ℝ × ℝ :=
  (a * Real.cos t, b * Real.sin t)

def rawSpeed (a b t : ℝ) : ℝ :=
  Real.sqrt (a ^ 2 * Real.sin t ^ 2 + b ^ 2 * Real.cos t ^ 2)

def weightedLength (a b : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..2 * Real.pi,
    |(curveMap a b t).2| * rawSpeed a b t

def eccentricity (a b : ℝ) : ℝ :=
  Real.sqrt (a ^ 2 - b ^ 2) / a

def hyperbolicEccentricity (a b : ℝ) : ℝ :=
  Real.sqrt (b ^ 2 - a ^ 2) / a

def minorPrimitive (a b u : ℝ) : ℝ :=
  let ε := eccentricity a b
  4 * a * b / ε *
    (1 / 2 * ε * u * Real.sqrt (1 - ε ^ 2 * u ^ 2) +
      1 / 2 * Real.arcsin (ε * u))

def majorPrimitive (a b u : ℝ) : ℝ :=
  let ε₁ := hyperbolicEccentricity a b
  4 * a * b / ε₁ *
    (1 / 2 * ε₁ * u * Real.sqrt (1 + ε₁ ^ 2 * u ^ 2) +
      1 / 2 *
        Real.log (ε₁ * u + Real.sqrt (1 + ε₁ ^ 2 * u ^ 2)))

def closedForm (a b : ℝ) : ℝ :=
  if b < a then
    let ε := eccentricity a b
    2 * b ^ 2 + 2 * a * b * (Real.arcsin ε / ε)
  else if a < b then
    let ε₁ := hyperbolicEccentricity a b
    2 * b ^ 2 +
      2 * a * b *
        (Real.log (ε₁ + Real.sqrt (1 + ε₁ ^ 2)) / ε₁)
  else
    4 * a ^ 2

private theorem cosine_change (f : ℝ → ℝ) (hf : Continuous f) (a b : ℝ) :
    (∫ t in a..b, f (Real.cos t) * (-Real.sin t)) =
      ∫ u in Real.cos a..Real.cos b, f u := by
  simpa only [smul_eq_mul, mul_comm] using
    intervalIntegral.integral_comp_mul_deriv
      (a := a) (b := b)
      (f := Real.cos) (f' := fun t : ℝ => -Real.sin t) (g := f)
      (fun x hx => Real.hasDerivAt_cos x)
      (fun x hx => Real.continuous_sin.neg.continuousWithinAt)
      hf

private theorem integral_neg_sin (a b : ℝ) :
    (∫ t in a..b, -Real.sin t) = Real.cos b - Real.cos a := by
  simpa only [one_mul, intervalIntegral.integral_const, smul_eq_mul, mul_one] using
    cosine_change (fun _ : ℝ => (1 : ℝ)) continuous_const a b

private theorem even_integral_neg_one_one (f : ℝ → ℝ) (hf : Continuous f)
    (heven : ∀ x, f (-x) = f x) :
    (∫ x in (-1 : ℝ)..1, f x) = 2 * ∫ x in (0 : ℝ)..1, f x := by
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hf.intervalIntegrable (a := (-1 : ℝ)) (b := 0))
    (hf.intervalIntegrable (a := (0 : ℝ)) (b := 1))]
  have hsub :
      (∫ x in (0 : ℝ)..1, (-1 : ℝ) * f (-x)) =
        ∫ x in (0 : ℝ)..(-1), f x := by
    simpa only [Function.comp_apply, neg_zero, smul_eq_mul, mul_comm] using
      intervalIntegral.integral_comp_mul_deriv
        (a := (0 : ℝ)) (b := 1)
        (f := fun x : ℝ => -x) (f' := fun _ : ℝ => (-1 : ℝ)) (g := f)
        (fun x hx => by
          simpa only [id_eq] using (hasDerivAt_id x).neg)
        (fun x hx => continuous_const.continuousWithinAt)
        hf
  have hleft :
      (∫ x in (0 : ℝ)..1, (-1 : ℝ) * f (-x)) =
        -(∫ x in (0 : ℝ)..1, f x) := by
    calc
      (∫ x in (0 : ℝ)..1, (-1 : ℝ) * f (-x)) =
          ∫ x in (0 : ℝ)..1, (-1 : ℝ) * f x := by
            apply intervalIntegral.integral_congr
            intro x hx
            change (-1 : ℝ) * f (-x) = (-1 : ℝ) * f x
            rw [heven x]
      _ = (-1 : ℝ) * (∫ x in (0 : ℝ)..1, f x) := by
            rw [intervalIntegral.integral_const_mul]
      _ = -(∫ x in (0 : ℝ)..1, f x) := by ring
  have hright :
      (∫ x in (0 : ℝ)..(-1), f x) =
        -(∫ x in (-1 : ℝ)..0, f x) := by
    rw [intervalIntegral.integral_symm]
  have hneg :
      (∫ x in (-1 : ℝ)..0, f x) = ∫ x in (0 : ℝ)..1, f x := by
    linarith [hsub, hleft, hright]
  rw [hneg]
  ring

private theorem minor_integral_eval (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hab : b < a) :
    4 * a * b *
        (∫ u in (0 : ℝ)..1,
          Real.sqrt (1 - eccentricity a b ^ 2 * u ^ 2)) =
      minorPrimitive a b 1 - minorPrimitive a b 0 := by
  let e : ℝ := eccentricity a b
  have hepos : 0 < e := by
    dsimp [e, eccentricity]
    exact div_pos (Real.sqrt_pos.2 (by nlinarith)) ha
  have he0 : e ≠ 0 := ne_of_gt hepos
  have hd : 0 ≤ a ^ 2 - b ^ 2 := by nlinarith
  have hsquare : (Real.sqrt (a ^ 2 - b ^ 2)) ^ 2 = a ^ 2 - b ^ 2 :=
    Real.sq_sqrt hd
  have helt : e < 1 := by
    have hsnonneg : 0 ≤ Real.sqrt (a ^ 2 - b ^ 2) := Real.sqrt_nonneg _
    have hslt : Real.sqrt (a ^ 2 - b ^ 2) < a := by
      nlinarith
    dsimp [e, eccentricity]
    exact (div_lt_one ha).2 hslt
  have hderiv : ∀ u ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (minorPrimitive a b)
        (4 * a * b * Real.sqrt (1 - e ^ 2 * u ^ 2)) u := by
    intro u hu
    have hu' : u ∈ Set.Icc (0 : ℝ) 1 := by
      simpa only [Set.uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using hu
    have hu0 : 0 ≤ u := hu'.1
    have hu1 : u ≤ 1 := hu'.2
    have heu_lt : e * u < 1 := by nlinarith
    have heu_gt : -1 < e * u := by nlinarith
    have hz : 0 < 1 - e ^ 2 * u ^ 2 := by
      nlinarith [sq_nonneg (e * u)]
    let s : ℝ := Real.sqrt (1 - e ^ 2 * u ^ 2)
    have hspos : 0 < s := by
      dsimp [s]
      exact Real.sqrt_pos.2 hz
    have hs0 : s ≠ 0 := ne_of_gt hspos
    have hs2 : s ^ 2 = 1 - e ^ 2 * u ^ 2 := by
      dsimp [s]
      exact Real.sq_sqrt (le_of_lt hz)
    have hq : HasDerivAt (fun x : ℝ => 1 - e ^ 2 * x ^ 2)
        (-2 * e ^ 2 * u) u := by
      convert (hasDerivAt_const u 1).sub
        (((hasDerivAt_id u).pow 2).const_mul (e ^ 2)) using 1 <;>
        simp only [id_eq] <;> ring
    have hsqrt : HasDerivAt
        (fun x : ℝ => Real.sqrt (1 - e ^ 2 * x ^ 2))
        ((-2 * e ^ 2 * u) / (2 * s)) u := by
      convert (Real.hasDerivAt_sqrt (ne_of_gt hz)).comp u hq using 1 <;>
        dsimp [s] <;> ring
    have hlinear : HasDerivAt
        (fun x : ℝ => (1 / 2 * e) * x) (1 / 2 * e) u := by
      convert (hasDerivAt_id u).const_mul (1 / 2 * e) using 1 <;> ring
    have hfirst : HasDerivAt
        (fun x : ℝ => (1 / 2 * e) * x * Real.sqrt (1 - e ^ 2 * x ^ 2))
        ((1 / 2 * e) * s + (1 / 2 * e) * u * ((-2 * e ^ 2 * u) / (2 * s))) u := by
      convert hlinear.mul hsqrt using 1 <;>
        dsimp [s] <;> ring
    have hinner : HasDerivAt (fun x : ℝ => e * x) e u := by
      convert (hasDerivAt_id u).const_mul e using 1 <;> ring
    have hasin : HasDerivAt
        (fun x : ℝ => (1 / 2) * Real.arcsin (e * x))
        ((1 / 2) * ((Real.sqrt (1 - (e * u) ^ 2))⁻¹ * e)) u := by
      convert (((Real.hasDerivAt_arcsin (ne_of_gt heu_gt) (ne_of_lt heu_lt)).comp u hinner).const_mul
        (1 / 2)) using 1 <;> ring
    have hsame : Real.sqrt (1 - (e * u) ^ 2) = s := by
      dsimp [s]
      congr 1
      ring
    have hcalc :
        (1 / 2 * e) * s + (1 / 2 * e) * u * ((-2 * e ^ 2 * u) / (2 * s)) +
            (1 / 2) * ((Real.sqrt (1 - (e * u) ^ 2))⁻¹ * e) = e * s := by
      rw [hsame]
      field_simp [hs0]
      nlinarith [hs2]
    have hbase : HasDerivAt
        (fun x : ℝ =>
          (1 / 2 * e) * x * Real.sqrt (1 - e ^ 2 * x ^ 2) +
            (1 / 2) * Real.arcsin (e * x))
        (e * s) u := by
      have hadd := hfirst.add hasin
      rw [hcalc] at hadd
      simpa only [Pi.add_apply] using hadd
    have hscaled := hbase.const_mul (4 * a * b / e)
    have hscaled' : HasDerivAt (minorPrimitive a b)
        ((4 * a * b / e) * (e * s)) u := by
      simpa only [minorPrimitive, e] using hscaled
    have hcoef : (4 * a * b / e) * (e * s) = 4 * a * b * s := by
      field_simp [he0] <;> ring
    rw [hcoef] at hscaled'
    simpa only [s, e] using hscaled'
  have hcont : Continuous
      (fun u : ℝ => 4 * a * b * Real.sqrt (1 - e ^ 2 * u ^ 2)) := by
    fun_prop
  have hfund :
      (∫ u in (0 : ℝ)..1,
        4 * a * b * Real.sqrt (1 - e ^ 2 * u ^ 2)) =
      minorPrimitive a b 1 - minorPrimitive a b 0 := by
    simpa only [Function.comp_apply, smul_eq_mul, mul_one, one_mul,
      intervalIntegral.integral_const] using
      intervalIntegral.integral_comp_mul_deriv
        (a := (0 : ℝ)) (b := 1)
        (f := minorPrimitive a b)
        (f' := fun u : ℝ => 4 * a * b * Real.sqrt (1 - e ^ 2 * u ^ 2))
        (g := fun _ : ℝ => (1 : ℝ))
        hderiv
        (fun x hx => hcont.continuousWithinAt)
        continuous_const
  rw [← intervalIntegral.integral_const_mul]
  simpa only [e] using hfund

private theorem major_integral_eval (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hab : a < b) :
    4 * a * b *
        (∫ u in (0 : ℝ)..1,
          Real.sqrt (1 + hyperbolicEccentricity a b ^ 2 * u ^ 2)) =
      majorPrimitive a b 1 - majorPrimitive a b 0 := by
  let e : ℝ := hyperbolicEccentricity a b
  have hepos : 0 < e := by
    dsimp [e, hyperbolicEccentricity]
    exact div_pos (Real.sqrt_pos.2 (by nlinarith)) ha
  have he0 : e ≠ 0 := ne_of_gt hepos
  have hderiv : ∀ u ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (majorPrimitive a b)
        (4 * a * b * Real.sqrt (1 + e ^ 2 * u ^ 2)) u := by
    intro u hu
    have hu' : u ∈ Set.Icc (0 : ℝ) 1 := by
      simpa only [Set.uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using hu
    have hu0 : 0 ≤ u := hu'.1
    have hz : 0 < 1 + e ^ 2 * u ^ 2 := by positivity
    let s : ℝ := Real.sqrt (1 + e ^ 2 * u ^ 2)
    have hspos : 0 < s := by
      dsimp [s]
      exact Real.sqrt_pos.2 hz
    have hs0 : s ≠ 0 := ne_of_gt hspos
    have hs2 : s ^ 2 = 1 + e ^ 2 * u ^ 2 := by
      dsimp [s]
      exact Real.sq_sqrt (le_of_lt hz)
    have harg : 0 < e * u + s := by positivity
    have harg0 : e * u + s ≠ 0 := ne_of_gt harg
    have hq : HasDerivAt (fun x : ℝ => 1 + e ^ 2 * x ^ 2)
        (2 * e ^ 2 * u) u := by
      convert (hasDerivAt_const u 1).add
        (((hasDerivAt_id u).pow 2).const_mul (e ^ 2)) using 1 <;>
        simp only [id_eq] <;> ring
    have hsqrt : HasDerivAt
        (fun x : ℝ => Real.sqrt (1 + e ^ 2 * x ^ 2))
        ((2 * e ^ 2 * u) / (2 * s)) u := by
      convert (Real.hasDerivAt_sqrt (ne_of_gt hz)).comp u hq using 1 <;>
        dsimp [s] <;> ring
    have hlinear : HasDerivAt
        (fun x : ℝ => (1 / 2 * e) * x) (1 / 2 * e) u := by
      convert (hasDerivAt_id u).const_mul (1 / 2 * e) using 1 <;> ring
    have hfirst : HasDerivAt
        (fun x : ℝ => (1 / 2 * e) * x * Real.sqrt (1 + e ^ 2 * x ^ 2))
        ((1 / 2 * e) * s + (1 / 2 * e) * u * ((2 * e ^ 2 * u) / (2 * s))) u := by
      convert hlinear.mul hsqrt using 1 <;>
        dsimp [s] <;> ring
    have hinner : HasDerivAt (fun x : ℝ => e * x) e u := by
      convert (hasDerivAt_id u).const_mul e using 1 <;> ring
    have hsum : HasDerivAt
        (fun x : ℝ => e * x + Real.sqrt (1 + e ^ 2 * x ^ 2))
        (e + (2 * e ^ 2 * u) / (2 * s)) u := by
      convert hinner.add hsqrt using 1 <;>
        dsimp [s] <;> ring
    have hlog : HasDerivAt
        (fun x : ℝ => (1 / 2) * Real.log (e * x + Real.sqrt (1 + e ^ 2 * x ^ 2)))
        ((1 / 2) * ((e + (2 * e ^ 2 * u) / (2 * s)) / (e * u + s))) u := by
      convert (((Real.hasDerivAt_log harg0).comp u hsum).const_mul (1 / 2)) using 1 <;>
        dsimp [s] <;> ring
    have hratio :
        (e + (2 * e ^ 2 * u) / (2 * s)) / (e * u + s) = e / s := by
      field_simp [hs0, harg0] <;> ring
    have hcalc :
        (1 / 2 * e) * s + (1 / 2 * e) * u * ((2 * e ^ 2 * u) / (2 * s)) +
            (1 / 2) * ((e + (2 * e ^ 2 * u) / (2 * s)) / (e * u + s)) = e * s := by
      rw [hratio]
      field_simp [hs0]
      nlinarith [hs2]
    have hbase : HasDerivAt
        (fun x : ℝ =>
          (1 / 2 * e) * x * Real.sqrt (1 + e ^ 2 * x ^ 2) +
            (1 / 2) * Real.log (e * x + Real.sqrt (1 + e ^ 2 * x ^ 2)))
        (e * s) u := by
      have hadd := hfirst.add hlog
      rw [hcalc] at hadd
      simpa only [Pi.add_apply] using hadd
    have hscaled := hbase.const_mul (4 * a * b / e)
    have hscaled' : HasDerivAt (majorPrimitive a b)
        ((4 * a * b / e) * (e * s)) u := by
      simpa only [majorPrimitive, e] using hscaled
    have hcoef : (4 * a * b / e) * (e * s) = 4 * a * b * s := by
      field_simp [he0] <;> ring
    rw [hcoef] at hscaled'
    simpa only [s, e] using hscaled'
  have hcont : Continuous
      (fun u : ℝ => 4 * a * b * Real.sqrt (1 + e ^ 2 * u ^ 2)) := by
    fun_prop
  have hfund :
      (∫ u in (0 : ℝ)..1,
        4 * a * b * Real.sqrt (1 + e ^ 2 * u ^ 2)) =
      majorPrimitive a b 1 - majorPrimitive a b 0 := by
    simpa only [Function.comp_apply, smul_eq_mul, mul_one, one_mul,
      intervalIntegral.integral_const] using
      intervalIntegral.integral_comp_mul_deriv
        (a := (0 : ℝ)) (b := 1)
        (f := majorPrimitive a b)
        (f' := fun u : ℝ => 4 * a * b * Real.sqrt (1 + e ^ 2 * u ^ 2))
        (g := fun _ : ℝ => (1 : ℝ))
        hderiv
        (fun x hx => hcont.continuousWithinAt)
        continuous_const
  rw [← intervalIntegral.integral_const_mul]
  simpa only [e] using hfund

theorem gap1 (a b : ℝ) :
    weightedLength a b =
      ∫ t in (0 : ℝ)..2 * Real.pi,
        |b * Real.sin t| * rawSpeed a b t := by
  rfl

theorem gap2 (a b t : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : b < a) :
    rawSpeed a b t =
      Real.sqrt (a ^ 2 * Real.sin t ^ 2 + b ^ 2 * Real.cos t ^ 2) := by
  rfl

theorem gap3 (a b t : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : b < a) :
    rawSpeed a b t =
      a * Real.sqrt
        (1 - eccentricity a b ^ 2 * Real.cos t ^ 2) := by
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hd : 0 ≤ a ^ 2 - b ^ 2 := by nlinarith
  have hs : (Real.sqrt (a ^ 2 - b ^ 2)) ^ 2 = a ^ 2 - b ^ 2 := Real.sq_sqrt hd
  have he : eccentricity a b ^ 2 = (a ^ 2 - b ^ 2) / a ^ 2 := by
    unfold eccentricity
    field_simp [ha0]
    nlinarith
  have htrig := Real.sin_sq_add_cos_sq t
  have harg :
      a ^ 2 * Real.sin t ^ 2 + b ^ 2 * Real.cos t ^ 2 =
        a ^ 2 * (1 - eccentricity a b ^ 2 * Real.cos t ^ 2) := by
    rw [he]
    field_simp [ha0]
    nlinarith
  rw [rawSpeed, harg, Real.sqrt_mul (sq_nonneg a)]
  rw [Real.sqrt_sq_eq_abs, abs_of_pos ha]

theorem gap4 (a b t : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : b < a) :
    rawSpeed a b t =
      a * Real.sqrt
        (1 - eccentricity a b ^ 2 * Real.cos t ^ 2) := by
  exact gap3 a b t ha hb hab

theorem gap5 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : b < a) :
    weightedLength a b =
      (∫ t in (0 : ℝ)..Real.pi,
        a * b * Real.sin t *
          Real.sqrt (1 - eccentricity a b ^ 2 * Real.cos t ^ 2)) +
      ∫ t in Real.pi..2 * Real.pi,
        a * (-b * Real.sin t) *
          Real.sqrt (1 - eccentricity a b ^ 2 * Real.cos t ^ 2) := by
  rw [gap1]
  have hcont : Continuous (fun t : ℝ => |b * Real.sin t| * rawSpeed a b t) := by
    unfold rawSpeed
    fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hcont.intervalIntegrable (a := (0 : ℝ)) (b := Real.pi))
    (hcont.intervalIntegrable (a := Real.pi) (b := 2 * Real.pi))]
  congr 1
  · apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Set.Icc (0 : ℝ) Real.pi := by
      simpa only [Set.uIcc_of_le (le_of_lt Real.pi_pos)] using ht
    have hsin : 0 ≤ Real.sin t :=
      Real.sin_nonneg_of_nonneg_of_le_pi ht'.1 ht'.2
    change |b * Real.sin t| * rawSpeed a b t =
      a * b * Real.sin t *
        Real.sqrt (1 - eccentricity a b ^ 2 * Real.cos t ^ 2)
    rw [gap3 a b t ha hb hab, abs_mul, abs_of_pos hb, abs_of_nonneg hsin]
    ring
  · apply intervalIntegral.integral_congr
    intro t ht
    have hpi2 : Real.pi ≤ 2 * Real.pi := by nlinarith [Real.pi_pos]
    have ht' : t ∈ Set.Icc Real.pi (2 * Real.pi) := by
      simpa only [Set.uIcc_of_le hpi2] using ht
    have hx0 : 0 ≤ t - Real.pi := sub_nonneg.mpr ht'.1
    have hxpi : t - Real.pi ≤ Real.pi := by
      calc
        t - Real.pi ≤ 2 * Real.pi - Real.pi :=
          sub_le_sub_right ht'.2 Real.pi
        _ = Real.pi := by ring
    have hxsin : 0 ≤ Real.sin (t - Real.pi) :=
      Real.sin_nonneg_of_nonneg_of_le_pi hx0 hxpi
    have hshift := Real.sin_add_pi (t - Real.pi)
    rw [show t - Real.pi + Real.pi = t by ring] at hshift
    have hsin : Real.sin t ≤ 0 := by
      calc
        Real.sin t = -Real.sin (t - Real.pi) := hshift
        _ ≤ 0 := neg_nonpos.mpr hxsin
    change |b * Real.sin t| * rawSpeed a b t =
      a * (-b * Real.sin t) *
        Real.sqrt (1 - eccentricity a b ^ 2 * Real.cos t ^ 2)
    rw [gap3 a b t ha hb hab, abs_mul, abs_of_pos hb, abs_of_nonpos hsin]
    ring

theorem gap6 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : b < a) :
    weightedLength a b =
      -a * b *
          (∫ t in (0 : ℝ)..Real.pi,
            Real.sqrt (1 - eccentricity a b ^ 2 * Real.cos t ^ 2) *
              (-Real.sin t)) +
        a * b *
          ∫ t in Real.pi..2 * Real.pi,
            Real.sqrt (1 - eccentricity a b ^ 2 * Real.cos t ^ 2) *
              (-Real.sin t) := by
  rw [gap5 a b ha hb hab]
  rw [← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_const_mul]
  congr 1 <;> apply intervalIntegral.integral_congr <;> intro t ht <;> ring

theorem gap7 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : b < a) :
    weightedLength a b =
      a * b *
          (∫ u in (-1 : ℝ)..1,
            Real.sqrt (1 - eccentricity a b ^ 2 * u ^ 2)) +
        a * b *
          ∫ u in (-1 : ℝ)..1,
            Real.sqrt (1 - eccentricity a b ^ 2 * u ^ 2) := by
  rw [gap6 a b ha hb hab]
  let f : ℝ → ℝ := fun u =>
    Real.sqrt (1 - eccentricity a b ^ 2 * u ^ 2)
  have hf : Continuous f := by
    dsimp [f]
    fun_prop
  rw [cosine_change f hf, cosine_change f hf]
  rw [Real.cos_zero, Real.cos_pi, Real.cos_two_pi]
  rw [intervalIntegral.integral_symm]
  change -a * b * (-(∫ u in (-1 : ℝ)..1, f u)) +
      a * b * (∫ u in (-1 : ℝ)..1, f u) =
    a * b * (∫ u in (-1 : ℝ)..1, f u) +
      a * b * (∫ u in (-1 : ℝ)..1, f u)
  ring

theorem gap8 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : b < a) :
    a * b *
          (∫ u in (-1 : ℝ)..1,
            Real.sqrt (1 - eccentricity a b ^ 2 * u ^ 2)) +
        a * b *
          (∫ u in (-1 : ℝ)..1,
            Real.sqrt (1 - eccentricity a b ^ 2 * u ^ 2)) =
      4 * a * b *
        ∫ u in (0 : ℝ)..1,
          Real.sqrt (1 - eccentricity a b ^ 2 * u ^ 2) := by
  let f : ℝ → ℝ := fun u =>
    Real.sqrt (1 - eccentricity a b ^ 2 * u ^ 2)
  have hf : Continuous f := by
    dsimp [f]
    fun_prop
  have heven : ∀ u, f (-u) = f u := by
    intro u
    simp [f]
  have hsym := even_integral_neg_one_one f hf heven
  change a * b * (∫ u in (-1 : ℝ)..1, f u) +
      a * b * (∫ u in (-1 : ℝ)..1, f u) =
    4 * a * b * ∫ u in (0 : ℝ)..1, f u
  rw [hsym]
  ring

theorem gap9 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : b < a) :
    weightedLength a b =
      4 * a * b *
        ∫ u in (0 : ℝ)..1,
          Real.sqrt (1 - eccentricity a b ^ 2 * u ^ 2) := by
  rw [gap7 a b ha hb hab]
  exact gap8 a b ha hb hab

theorem gap10 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : b < a) :
    weightedLength a b = minorPrimitive a b 1 - minorPrimitive a b 0 := by
  rw [gap9 a b ha hb hab]
  exact minor_integral_eval a b ha hb hab

theorem gap11 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : b < a) :
    minorPrimitive a b 1 - minorPrimitive a b 0 =
      2 * b ^ 2 +
        2 * a * b *
          (Real.arcsin (eccentricity a b) / eccentricity a b) := by
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hd : 0 ≤ a ^ 2 - b ^ 2 := by nlinarith
  have hs : (Real.sqrt (a ^ 2 - b ^ 2)) ^ 2 = a ^ 2 - b ^ 2 := Real.sq_sqrt hd
  have hepos : 0 < eccentricity a b := by
    unfold eccentricity
    exact div_pos (Real.sqrt_pos.2 (by nlinarith)) ha
  have he0 : eccentricity a b ≠ 0 := ne_of_gt hepos
  have he : eccentricity a b ^ 2 = (a ^ 2 - b ^ 2) / a ^ 2 := by
    unfold eccentricity
    field_simp [ha0]
    nlinarith
  have hrad : 1 - eccentricity a b ^ 2 = (b / a) ^ 2 := by
    rw [he]
    field_simp [ha0]
    ring
  have hsqrt : Real.sqrt (1 - eccentricity a b ^ 2) = b / a := by
    rw [hrad, Real.sqrt_sq_eq_abs, abs_of_pos (div_pos hb ha)]
  have hsqrt' :
      Real.sqrt (1 - eccentricity a b ^ 2 * (1 : ℝ) ^ 2) = b / a := by
    simpa only [one_pow, mul_one] using hsqrt
  unfold minorPrimitive
  simp only [one_mul, mul_one, mul_zero, Real.arcsin_zero, Real.sqrt_one,
    zero_mul, add_zero, sub_zero]
  rw [hsqrt']
  field_simp [ha0, he0]
  ring

theorem gap12 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : b < a) :
    weightedLength a b =
      2 * b ^ 2 +
        2 * a * b *
          (Real.arcsin (eccentricity a b) / eccentricity a b) := by
  rw [gap10 a b ha hb hab]
  exact gap11 a b ha hb hab

theorem gap13 (a b t : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a < b) :
    rawSpeed a b t =
      Real.sqrt (a ^ 2 * Real.sin t ^ 2 + b ^ 2 * Real.cos t ^ 2) := by
  rfl

theorem gap14 (a b t : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a < b) :
    rawSpeed a b t =
      a * Real.sqrt
        (1 + hyperbolicEccentricity a b ^ 2 * Real.cos t ^ 2) := by
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hd : 0 ≤ b ^ 2 - a ^ 2 := by nlinarith
  have hs : (Real.sqrt (b ^ 2 - a ^ 2)) ^ 2 = b ^ 2 - a ^ 2 := Real.sq_sqrt hd
  have he : hyperbolicEccentricity a b ^ 2 = (b ^ 2 - a ^ 2) / a ^ 2 := by
    unfold hyperbolicEccentricity
    field_simp [ha0]
    nlinarith
  have htrig := Real.sin_sq_add_cos_sq t
  have harg :
      a ^ 2 * Real.sin t ^ 2 + b ^ 2 * Real.cos t ^ 2 =
        a ^ 2 * (1 + hyperbolicEccentricity a b ^ 2 * Real.cos t ^ 2) := by
    rw [he]
    field_simp [ha0]
    nlinarith
  rw [rawSpeed, harg, Real.sqrt_mul (sq_nonneg a)]
  rw [Real.sqrt_sq_eq_abs, abs_of_pos ha]

theorem gap15 (a b t : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a < b) :
    rawSpeed a b t =
      a * Real.sqrt
        (1 + hyperbolicEccentricity a b ^ 2 * Real.cos t ^ 2) := by
  exact gap14 a b t ha hb hab

theorem gap16 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a < b) :
    weightedLength a b =
      (∫ t in (0 : ℝ)..Real.pi,
        a * b * Real.sin t *
          Real.sqrt
            (1 + hyperbolicEccentricity a b ^ 2 * Real.cos t ^ 2)) +
      ∫ t in Real.pi..2 * Real.pi,
        a * (-b * Real.sin t) *
          Real.sqrt
            (1 + hyperbolicEccentricity a b ^ 2 * Real.cos t ^ 2) := by
  rw [gap1]
  have hcont : Continuous (fun t : ℝ => |b * Real.sin t| * rawSpeed a b t) := by
    unfold rawSpeed
    fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hcont.intervalIntegrable (a := (0 : ℝ)) (b := Real.pi))
    (hcont.intervalIntegrable (a := Real.pi) (b := 2 * Real.pi))]
  congr 1
  · apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Set.Icc (0 : ℝ) Real.pi := by
      simpa only [Set.uIcc_of_le (le_of_lt Real.pi_pos)] using ht
    have hsin : 0 ≤ Real.sin t :=
      Real.sin_nonneg_of_nonneg_of_le_pi ht'.1 ht'.2
    change |b * Real.sin t| * rawSpeed a b t =
      a * b * Real.sin t *
        Real.sqrt (1 + hyperbolicEccentricity a b ^ 2 * Real.cos t ^ 2)
    rw [gap14 a b t ha hb hab, abs_mul, abs_of_pos hb, abs_of_nonneg hsin]
    ring
  · apply intervalIntegral.integral_congr
    intro t ht
    have hpi2 : Real.pi ≤ 2 * Real.pi := by nlinarith [Real.pi_pos]
    have ht' : t ∈ Set.Icc Real.pi (2 * Real.pi) := by
      simpa only [Set.uIcc_of_le hpi2] using ht
    have hx0 : 0 ≤ t - Real.pi := sub_nonneg.mpr ht'.1
    have hxpi : t - Real.pi ≤ Real.pi := by
      calc
        t - Real.pi ≤ 2 * Real.pi - Real.pi :=
          sub_le_sub_right ht'.2 Real.pi
        _ = Real.pi := by ring
    have hxsin : 0 ≤ Real.sin (t - Real.pi) :=
      Real.sin_nonneg_of_nonneg_of_le_pi hx0 hxpi
    have hshift := Real.sin_add_pi (t - Real.pi)
    rw [show t - Real.pi + Real.pi = t by ring] at hshift
    have hsin : Real.sin t ≤ 0 := by
      calc
        Real.sin t = -Real.sin (t - Real.pi) := hshift
        _ ≤ 0 := neg_nonpos.mpr hxsin
    change |b * Real.sin t| * rawSpeed a b t =
      a * (-b * Real.sin t) *
        Real.sqrt (1 + hyperbolicEccentricity a b ^ 2 * Real.cos t ^ 2)
    rw [gap14 a b t ha hb hab, abs_mul, abs_of_pos hb, abs_of_nonpos hsin]
    ring

theorem gap17 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a < b) :
    (∫ t in (0 : ℝ)..Real.pi,
          a * b * Real.sin t *
            Real.sqrt
              (1 + hyperbolicEccentricity a b ^ 2 * Real.cos t ^ 2)) +
        (∫ t in Real.pi..2 * Real.pi,
          a * (-b * Real.sin t) *
            Real.sqrt
              (1 + hyperbolicEccentricity a b ^ 2 * Real.cos t ^ 2)) =
      4 * a * b *
        ∫ u in (0 : ℝ)..1,
          Real.sqrt (1 + hyperbolicEccentricity a b ^ 2 * u ^ 2) := by
  let f : ℝ → ℝ := fun u =>
    Real.sqrt (1 + hyperbolicEccentricity a b ^ 2 * u ^ 2)
  have hf : Continuous f := by
    dsimp [f]
    fun_prop
  have heven : ∀ u, f (-u) = f u := by
    intro u
    simp [f]
  have hfirst :
      (∫ t in (0 : ℝ)..Real.pi,
        a * b * Real.sin t * f (Real.cos t)) =
        a * b * ∫ u in (-1 : ℝ)..1, f u := by
    rw [show (fun t => a * b * Real.sin t * f (Real.cos t)) =
        fun t => (-a * b) * (f (Real.cos t) * (-Real.sin t)) by
      funext t
      ring]
    rw [intervalIntegral.integral_const_mul, cosine_change f hf]
    rw [Real.cos_zero, Real.cos_pi, intervalIntegral.integral_symm]
    ring
  have hsecond :
      (∫ t in Real.pi..2 * Real.pi,
        a * (-b * Real.sin t) * f (Real.cos t)) =
        a * b * ∫ u in (-1 : ℝ)..1, f u := by
    rw [show (fun t => a * (-b * Real.sin t) * f (Real.cos t)) =
        fun t => (a * b) * (f (Real.cos t) * (-Real.sin t)) by
      funext t
      ring]
    rw [intervalIntegral.integral_const_mul, cosine_change f hf]
    rw [Real.cos_pi, Real.cos_two_pi]
  change
      (∫ t in (0 : ℝ)..Real.pi,
        a * b * Real.sin t * f (Real.cos t)) +
      (∫ t in Real.pi..2 * Real.pi,
        a * (-b * Real.sin t) * f (Real.cos t)) =
      4 * a * b * ∫ u in (0 : ℝ)..1, f u
  rw [hfirst, hsecond, even_integral_neg_one_one f hf heven]
  ring

theorem gap18 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a < b) :
    weightedLength a b =
      4 * a * b *
        ∫ u in (0 : ℝ)..1,
          Real.sqrt (1 + hyperbolicEccentricity a b ^ 2 * u ^ 2) := by
  rw [gap16 a b ha hb hab]
  exact gap17 a b ha hb hab

theorem gap19 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a < b) :
    weightedLength a b = majorPrimitive a b 1 - majorPrimitive a b 0 := by
  rw [gap18 a b ha hb hab]
  exact major_integral_eval a b ha hb hab

theorem gap20 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a < b) :
    majorPrimitive a b 1 - majorPrimitive a b 0 =
      2 * b ^ 2 +
        2 * a * b *
          (Real.log
              (hyperbolicEccentricity a b +
                Real.sqrt (1 + hyperbolicEccentricity a b ^ 2)) /
            hyperbolicEccentricity a b) := by
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hd : 0 ≤ b ^ 2 - a ^ 2 := by nlinarith
  have hs : (Real.sqrt (b ^ 2 - a ^ 2)) ^ 2 = b ^ 2 - a ^ 2 := Real.sq_sqrt hd
  have hepos : 0 < hyperbolicEccentricity a b := by
    unfold hyperbolicEccentricity
    exact div_pos (Real.sqrt_pos.2 (by nlinarith)) ha
  have he0 : hyperbolicEccentricity a b ≠ 0 := ne_of_gt hepos
  have he : hyperbolicEccentricity a b ^ 2 = (b ^ 2 - a ^ 2) / a ^ 2 := by
    unfold hyperbolicEccentricity
    field_simp [ha0]
    nlinarith
  have hrad : 1 + hyperbolicEccentricity a b ^ 2 = (b / a) ^ 2 := by
    rw [he]
    field_simp [ha0]
    ring
  have hsqrt : Real.sqrt (1 + hyperbolicEccentricity a b ^ 2) = b / a := by
    rw [hrad, Real.sqrt_sq_eq_abs, abs_of_pos (div_pos hb ha)]
  have hsqrt' :
      Real.sqrt (1 + hyperbolicEccentricity a b ^ 2 * (1 : ℝ) ^ 2) = b / a := by
    simpa only [one_pow, mul_one] using hsqrt
  have hlogzero :
      Real.log
        (Real.sqrt
          (1 + hyperbolicEccentricity a b ^ 2 * (0 : ℝ) ^ 2)) = 0 := by
    norm_num
  unfold majorPrimitive
  simp only [one_mul, mul_one, mul_zero, zero_mul, zero_add, add_zero, sub_zero]
  rw [hsqrt', hsqrt, hlogzero]
  field_simp [ha0, he0] <;> ring

theorem gap21 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a < b) :
    weightedLength a b =
      2 * b ^ 2 +
        2 * a * b *
          (Real.log
              (hyperbolicEccentricity a b +
                Real.sqrt (1 + hyperbolicEccentricity a b ^ 2)) /
            hyperbolicEccentricity a b) := by
  rw [gap19 a b ha hb hab]
  exact gap20 a b ha hb hab

theorem gap22 (a b t : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a = b) :
    rawSpeed a b t = a := by
  subst b
  unfold rawSpeed
  rw [← mul_add, Real.sin_sq_add_cos_sq, mul_one]
  rw [Real.sqrt_sq_eq_abs, abs_of_pos ha]

theorem gap23 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a = b) :
    weightedLength a b =
      (∫ t in (0 : ℝ)..Real.pi, a ^ 2 * Real.sin t) +
        ∫ t in Real.pi..2 * Real.pi, -a * Real.sin t * a := by
  subst b
  rw [gap1]
  have hcont : Continuous (fun t : ℝ => |a * Real.sin t| * rawSpeed a a t) := by
    unfold rawSpeed
    fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hcont.intervalIntegrable (a := (0 : ℝ)) (b := Real.pi))
    (hcont.intervalIntegrable (a := Real.pi) (b := 2 * Real.pi))]
  congr 1
  · apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Set.Icc (0 : ℝ) Real.pi := by
      simpa only [Set.uIcc_of_le (le_of_lt Real.pi_pos)] using ht
    have hsin : 0 ≤ Real.sin t :=
      Real.sin_nonneg_of_nonneg_of_le_pi ht'.1 ht'.2
    change |a * Real.sin t| * rawSpeed a a t = a ^ 2 * Real.sin t
    rw [gap22 a a t ha ha rfl, abs_mul, abs_of_pos ha, abs_of_nonneg hsin]
    ring
  · apply intervalIntegral.integral_congr
    intro t ht
    have hpi2 : Real.pi ≤ 2 * Real.pi := by nlinarith [Real.pi_pos]
    have ht' : t ∈ Set.Icc Real.pi (2 * Real.pi) := by
      simpa only [Set.uIcc_of_le hpi2] using ht
    have hx0 : 0 ≤ t - Real.pi := sub_nonneg.mpr ht'.1
    have hxpi : t - Real.pi ≤ Real.pi := by
      calc
        t - Real.pi ≤ 2 * Real.pi - Real.pi :=
          sub_le_sub_right ht'.2 Real.pi
        _ = Real.pi := by ring
    have hxsin : 0 ≤ Real.sin (t - Real.pi) :=
      Real.sin_nonneg_of_nonneg_of_le_pi hx0 hxpi
    have hshift := Real.sin_add_pi (t - Real.pi)
    rw [show t - Real.pi + Real.pi = t by ring] at hshift
    have hsin : Real.sin t ≤ 0 := by
      calc
        Real.sin t = -Real.sin (t - Real.pi) := hshift
        _ ≤ 0 := neg_nonpos.mpr hxsin
    change |a * Real.sin t| * rawSpeed a a t = -a * Real.sin t * a
    rw [gap22 a a t ha ha rfl, abs_mul, abs_of_pos ha, abs_of_nonpos hsin]
    ring

theorem gap24 (a : ℝ) (ha : 0 < a) :
    (∫ t in (0 : ℝ)..Real.pi, a ^ 2 * Real.sin t) +
        (∫ t in Real.pi..2 * Real.pi, -a * Real.sin t * a) =
      4 * a ^ 2 := by
  have hfirst :
      (fun t : ℝ => a ^ 2 * Real.sin t) =
        (fun t => (-a ^ 2) * (-Real.sin t)) := by
    funext t
    ring
  have hsecond :
      (fun t : ℝ => -a * Real.sin t * a) =
        (fun t => a ^ 2 * (-Real.sin t)) := by
    funext t
    ring
  have hfirstInt :
      (∫ t in (0 : ℝ)..Real.pi, a ^ 2 * Real.sin t) = 2 * a ^ 2 := by
    rw [hfirst, intervalIntegral.integral_const_mul, integral_neg_sin,
      Real.cos_pi, Real.cos_zero]
    ring
  have hsecondInt :
      (∫ t in Real.pi..2 * Real.pi, -a * Real.sin t * a) = 2 * a ^ 2 := by
    rw [hsecond, intervalIntegral.integral_const_mul, integral_neg_sin,
      Real.cos_two_pi, Real.cos_pi]
    ring
  rw [hfirstInt, hsecondInt]
  ring

theorem gap25 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a = b) :
    weightedLength a b = 4 * a ^ 2 := by
  rw [gap23 a b ha hb hab]
  exact gap24 a ha

theorem gap26 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    weightedLength a b = closedForm a b := by
  by_cases hba : b < a
  · rw [gap12 a b ha hb hba]
    simp [closedForm, hba]
  · by_cases hab : a < b
    · rw [gap21 a b ha hb hab]
      simp [closedForm, hba, hab]
    · have heq : a = b := le_antisymm (le_of_not_gt hba) (le_of_not_gt hab)
      rw [gap25 a b ha hb heq]
      simp [closedForm, hba, hab]

end

end ProofGap.Exercise4241
