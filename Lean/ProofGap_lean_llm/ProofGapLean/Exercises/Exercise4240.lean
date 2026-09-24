import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic.Positivity

namespace ProofGap.Exercise4240

noncomputable section

open scoped Interval

abbrev Vec3 := ℝ × ℝ × ℝ

def xCoord (a y : ℝ) : ℝ :=
  y ^ 2 / a

def zCoord (a y : ℝ) : ℝ :=
  y / a * Real.sqrt (y ^ 2 + a ^ 2)

def curveMap (a y : ℝ) : Vec3 :=
  (xCoord a y, y, zCoord a y)

def curveSegment (a : ℝ) : Set Vec3 :=
  curveMap a '' Set.Icc 0 a

def rawSpeed (a y : ℝ) : ℝ :=
  Real.sqrt
    ((2 * y / a) ^ 2 + 1 +
      ((2 * y ^ 2 + a ^ 2) /
        (a * Real.sqrt (y ^ 2 + a ^ 2))) ^ 2)

def speed (a y : ℝ) : ℝ :=
  Real.sqrt
    ((8 * y ^ 4 + 9 * a ^ 2 * y ^ 2 + 2 * a ^ 4) /
      (a ^ 2 * (y ^ 2 + a ^ 2)))

def weightedLength (a : ℝ) : ℝ :=
  ∫ y in (0 : ℝ)..a, zCoord a y * speed a y

def transformedRadicand (a y : ℝ) : ℝ :=
  y ^ 4 + 9 / 8 * a ^ 2 * y ^ 2 + 1 / 4 * a ^ 4

def endpointPrimitive (a u : ℝ) : ℝ :=
  Real.sqrt 2 / a ^ 2 *
    (u / 2 * Real.sqrt (u ^ 2 - 17 * a ^ 4 / 16 ^ 2) -
      17 * a ^ 4 / (2 * 16 ^ 2) *
        Real.log (u + Real.sqrt (u ^ 2 - 17 * a ^ 4 / 16 ^ 2)))

private def quadraticPrimitive (a u : ℝ) : ℝ :=
  let q : ℝ := 17 * a ^ 4 / 16 ^ 2
  u / 2 * Real.sqrt (u ^ 2 - q) -
    q / 2 * Real.log (u + Real.sqrt (u ^ 2 - q))

private theorem quadraticPrimitive_hasDerivAt
    (a u : ℝ) (ha : 0 < a)
    (hu : 9 * a ^ 2 / 16 ≤ u) :
    HasDerivAt (quadraticPrimitive a)
      (Real.sqrt (u ^ 2 - 17 * a ^ 4 / 16 ^ 2)) u := by
  let q : ℝ := 17 * a ^ 4 / 16 ^ 2
  let lower : ℝ := 9 * a ^ 2 / 16
  have hlower : 0 < lower := by
    dsimp [lower]
    positivity
  have hu0 : 0 < u := lt_of_lt_of_le hlower hu
  have hbase : lower ^ 2 - q = a ^ 4 / 4 := by
    dsimp [lower, q]
    ring
  have hdiff : 0 ≤ u - lower := sub_nonneg.mpr hu
  have hplus : 0 ≤ u + lower := by positivity
  have hprod : 0 ≤ (u - lower) * (u + lower) :=
    mul_nonneg hdiff hplus
  have hmono : lower ^ 2 ≤ u ^ 2 := by
    nlinarith
  have hbasepos : 0 < lower ^ 2 - q := by
    rw [hbase]
    positivity
  have hr : 0 < u ^ 2 - q := by
    nlinarith
  have hspos : 0 < Real.sqrt (u ^ 2 - q) := Real.sqrt_pos.2 hr
  have hrder : HasDerivAt (fun v : ℝ => v ^ 2 - q) (2 * u) u := by
    simpa using (((hasDerivAt_id u).pow 2).sub_const q)
  have hsder : HasDerivAt (fun v : ℝ => Real.sqrt (v ^ 2 - q))
      (u / Real.sqrt (u ^ 2 - q)) u := by
    have h := (Real.hasDerivAt_sqrt hr.ne').comp u hrder
    convert h using 1
    field_simp [ne_of_gt hspos]
    <;> ring
  have hp : 0 < u + Real.sqrt (u ^ 2 - q) := by positivity
  have hlogder :
      HasDerivAt (fun v : ℝ =>
        Real.log (v + Real.sqrt (v ^ 2 - q)))
        (1 / Real.sqrt (u ^ 2 - q)) u := by
    have hinner := (hasDerivAt_id u).add hsder
    have h := (Real.hasDerivAt_log hp.ne').comp u hinner
    convert h using 1
    field_simp [ne_of_gt hspos]
    <;> ring
  have hfirst := ((hasDerivAt_id u).div_const 2).mul hsder
  have hsecond := (hasDerivAt_const u (q / 2)).mul hlogder
  have hcomb : HasDerivAt (quadraticPrimitive a)
      ((1 / 2) * Real.sqrt (u ^ 2 - q) +
        (u / 2) * (u / Real.sqrt (u ^ 2 - q)) -
        (q / 2) * (1 / Real.sqrt (u ^ 2 - q))) u := by
    simpa [quadraticPrimitive, q] using hfirst.sub hsecond
  have hcoef :
      (1 / 2) * Real.sqrt (u ^ 2 - q) +
          (u / 2) * (u / Real.sqrt (u ^ 2 - q)) -
          (q / 2) * (1 / Real.sqrt (u ^ 2 - q)) =
        Real.sqrt (u ^ 2 - q) := by
    field_simp [ne_of_gt hspos] <;>
      nlinarith [Real.sq_sqrt hr.le]
  rw [hcoef] at hcomb
  simpa [q] using hcomb

private theorem sqrt_quadratic_integral (a : ℝ) (ha : 0 < a) :
    (∫ u in 9 * a ^ 2 / 16..25 * a ^ 2 / 16,
      Real.sqrt (u ^ 2 - 17 * a ^ 4 / 16 ^ 2)) =
      (25 * a ^ 2 / 16 / 2 *
          Real.sqrt ((25 * a ^ 2 / 16) ^ 2 - 17 * a ^ 4 / 16 ^ 2) -
        17 * a ^ 4 / (2 * 16 ^ 2) *
          Real.log (25 * a ^ 2 / 16 +
            Real.sqrt ((25 * a ^ 2 / 16) ^ 2 - 17 * a ^ 4 / 16 ^ 2))) -
      (9 * a ^ 2 / 16 / 2 *
          Real.sqrt ((9 * a ^ 2 / 16) ^ 2 - 17 * a ^ 4 / 16 ^ 2) -
        17 * a ^ 4 / (2 * 16 ^ 2) *
          Real.log (9 * a ^ 2 / 16 +
            Real.sqrt ((9 * a ^ 2 / 16) ^ 2 - 17 * a ^ 4 / 16 ^ 2))) := by
  have hab : 9 * a ^ 2 / 16 ≤ 25 * a ^ 2 / 16 := by
    nlinarith [sq_nonneg a]
  have hder : ∀ u ∈ Set.uIcc (9 * a ^ 2 / 16) (25 * a ^ 2 / 16),
      HasDerivAt (quadraticPrimitive a)
        (Real.sqrt (u ^ 2 - 17 * a ^ 4 / 16 ^ 2)) u := by
    intro u hu
    rw [Set.uIcc_of_le hab] at hu
    exact quadraticPrimitive_hasDerivAt a u ha hu.1
  have hint : IntervalIntegrable
      (fun u : ℝ => Real.sqrt (u ^ 2 - 17 * a ^ 4 / 16 ^ 2))
      MeasureTheory.volume (9 * a ^ 2 / 16) (25 * a ^ 2 / 16) := by
    exact (Real.continuous_sqrt.comp
      ((continuous_id.pow 2).sub continuous_const)).intervalIntegrable _ _
  have hfund := intervalIntegral.integral_eq_sub_of_hasDerivAt hder hint
  calc
    (∫ u in 9 * a ^ 2 / 16..25 * a ^ 2 / 16,
        Real.sqrt (u ^ 2 - 17 * a ^ 4 / 16 ^ 2)) =
        quadraticPrimitive a (25 * a ^ 2 / 16) -
          quadraticPrimitive a (9 * a ^ 2 / 16) := hfund
    _ = (25 * a ^ 2 / 16 / 2 *
          Real.sqrt ((25 * a ^ 2 / 16) ^ 2 - 17 * a ^ 4 / 16 ^ 2) -
        17 * a ^ 4 / (2 * 16 ^ 2) *
          Real.log (25 * a ^ 2 / 16 +
            Real.sqrt ((25 * a ^ 2 / 16) ^ 2 - 17 * a ^ 4 / 16 ^ 2))) -
      (9 * a ^ 2 / 16 / 2 *
          Real.sqrt ((9 * a ^ 2 / 16) ^ 2 - 17 * a ^ 4 / 16 ^ 2) -
        17 * a ^ 4 / (2 * 16 ^ 2) *
          Real.log (9 * a ^ 2 / 16 +
            Real.sqrt ((9 * a ^ 2 / 16) ^ 2 - 17 * a ^ 4 / 16 ^ 2))) := by
      unfold quadraticPrimitive
      ring

private theorem transformed_substitution (a : ℝ) (ha : 0 < a) :
    2 * (∫ y in (0 : ℝ)..a, y * Real.sqrt (transformedRadicand a y)) =
      ∫ u in 9 * a ^ 2 / 16..25 * a ^ 2 / 16,
        Real.sqrt (u ^ 2 - 17 * a ^ 4 / 16 ^ 2) := by
  let f : ℝ → ℝ := fun y => y ^ 2 + 9 * a ^ 2 / 16
  have hder : ∀ y ∈ Set.uIcc (0 : ℝ) a,
      HasDerivAt (fun v => quadraticPrimitive a (f v))
        (2 * (y * Real.sqrt (transformedRadicand a y))) y := by
    intro y hy
    have hfl : 9 * a ^ 2 / 16 ≤ f y := by
      dsimp [f]
      nlinarith [sq_nonneg y]
    have hfder : HasDerivAt f (2 * y) y := by
      simpa [f] using
        (((hasDerivAt_id y).pow 2).add_const (9 * a ^ 2 / 16))
    have hc : HasDerivAt (fun v => quadraticPrimitive a (f v))
        (Real.sqrt (f y ^ 2 - 17 * a ^ 4 / 16 ^ 2) * (2 * y)) y := by
      simpa only [Function.comp_apply] using
        (quadraticPrimitive_hasDerivAt a (f y) ha hfl).comp y hfder
    have hrad : f y ^ 2 - 17 * a ^ 4 / 16 ^ 2 =
        transformedRadicand a y := by
      dsimp [f]
      unfold transformedRadicand
      ring
    convert hc using 1
    rw [hrad]
    ring
  have htr : Continuous (fun y : ℝ => transformedRadicand a y) := by
    unfold transformedRadicand
    apply Continuous.add
    · apply Continuous.add
      · exact (continuous_id : Continuous (fun y : ℝ => y)).pow 4
      · exact
          (continuous_const :
            Continuous (fun _ : ℝ => (9 / 8 * a ^ 2 : ℝ))).mul
          ((continuous_id : Continuous (fun y : ℝ => y)).pow 2)
    · exact
        (continuous_const :
          Continuous (fun _ : ℝ => (1 / 4 * a ^ 4 : ℝ)))
  have hint : IntervalIntegrable
      (fun y : ℝ => 2 * (y * Real.sqrt (transformedRadicand a y)))
      MeasureTheory.volume 0 a := by
    exact
      ((continuous_const :
          Continuous (fun _ : ℝ => (2 : ℝ))).mul
        ((continuous_id : Continuous (fun y : ℝ => y)).mul
          (Real.continuous_sqrt.comp htr))).intervalIntegrable _ _
  have hfund := intervalIntegral.integral_eq_sub_of_hasDerivAt hder hint
  have hf0 : f 0 = 9 * a ^ 2 / 16 := by
    dsimp [f]
    ring
  have hfa : f a = 25 * a ^ 2 / 16 := by
    dsimp [f]
    ring
  calc
    2 * (∫ y in (0 : ℝ)..a,
        y * Real.sqrt (transformedRadicand a y)) =
      ∫ y in (0 : ℝ)..a,
        2 * (y * Real.sqrt (transformedRadicand a y)) := by
          rw [intervalIntegral.integral_const_mul]
    _ = quadraticPrimitive a (f a) - quadraticPrimitive a (f 0) := hfund
    _ = quadraticPrimitive a (25 * a ^ 2 / 16) -
        quadraticPrimitive a (9 * a ^ 2 / 16) := by
      rw [hfa, hf0]
    _ = ∫ u in 9 * a ^ 2 / 16..25 * a ^ 2 / 16,
        Real.sqrt (u ^ 2 - 17 * a ^ 4 / 16 ^ 2) := by
      rw [sqrt_quadratic_integral a ha]
      unfold quadraticPrimitive
      ring

theorem gap1 (a y : ℝ) (ha : 0 < a) (hy : 0 ≤ y) :
    zCoord a y = Real.sqrt (xCoord a y ^ 2 + y ^ 2) := by
  unfold zCoord xCoord
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hrewrite : (y ^ 2 / a) ^ 2 + y ^ 2 =
      (y / a) ^ 2 * (y ^ 2 + a ^ 2) := by
    field_simp [ha0]
    <;> ring
  rw [hrewrite, Real.sqrt_mul (sq_nonneg (y / a)),
    Real.sqrt_sq_eq_abs, abs_of_nonneg (div_nonneg hy ha.le)]

theorem gap2 (a y : ℝ) (ha : 0 < a) (hy : 0 ≤ y) :
    Real.sqrt (xCoord a y ^ 2 + y ^ 2) =
      Real.sqrt (y ^ 4 / a ^ 2 + y ^ 2) := by
  unfold xCoord
  congr 1
  field_simp [ne_of_gt ha]
  <;> ring

theorem gap3 (a y : ℝ) (ha : 0 < a) (hy : 0 ≤ y) :
    Real.sqrt (y ^ 4 / a ^ 2 + y ^ 2) =
      y / a * Real.sqrt (y ^ 2 + a ^ 2) := by
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hrewrite : y ^ 4 / a ^ 2 + y ^ 2 =
      (y / a) ^ 2 * (y ^ 2 + a ^ 2) := by
    field_simp [ha0]
    <;> ring
  rw [hrewrite, Real.sqrt_mul (sq_nonneg (y / a)),
    Real.sqrt_sq_eq_abs, abs_of_nonneg (div_nonneg hy ha.le)]

theorem gap4 (a y : ℝ) (ha : 0 < a) (hy : 0 ≤ y) :
    zCoord a y = y / a * Real.sqrt (y ^ 2 + a ^ 2) := by
  rfl

theorem gap5 (a : ℝ) (ha : 0 < a) :
    curveSegment a = curveMap a '' Set.Icc 0 a := by
  rfl

theorem gap6 (a y : ℝ) (ha : 0 < a) (hy : 0 < y) :
    rawSpeed a y =
      Real.sqrt
        ((2 * y / a) ^ 2 + 1 +
          ((2 * y ^ 2 + a ^ 2) /
            (a * Real.sqrt (y ^ 2 + a ^ 2))) ^ 2) := by
  rfl

theorem gap7 (a y : ℝ) (ha : 0 < a) (hy : 0 ≤ y) :
    rawSpeed a y = speed a y := by
  unfold rawSpeed speed
  congr 1
  have hsum : 0 < y ^ 2 + a ^ 2 := by
    nlinarith [sq_nonneg y, sq_pos_of_pos ha]
  have hsqrt_sq : Real.sqrt (y ^ 2 + a ^ 2) ^ 2 =
      y ^ 2 + a ^ 2 := Real.sq_sqrt hsum.le
  simp only [div_pow, mul_pow]
  rw [hsqrt_sq]
  field_simp [ne_of_gt ha, ne_of_gt hsum] <;> ring

theorem gap8 (a y : ℝ) (ha : 0 < a) (hy : 0 ≤ y) :
    rawSpeed a y =
      Real.sqrt
        ((8 * y ^ 4 + 9 * a ^ 2 * y ^ 2 + 2 * a ^ 4) /
          (a ^ 2 * (y ^ 2 + a ^ 2))) := by
  simpa [speed] using gap7 a y ha hy

theorem gap9 (a : ℝ) (ha : 0 < a) :
    weightedLength a =
      ∫ y in (0 : ℝ)..a,
        y / a * Real.sqrt (y ^ 2 + a ^ 2) *
          Real.sqrt
            ((8 * y ^ 4 + 9 * a ^ 2 * y ^ 2 + 2 * a ^ 4) /
              (a ^ 2 * (y ^ 2 + a ^ 2))) := by
  rfl

theorem gap10 (a : ℝ) (ha : 0 < a) :
    weightedLength a =
      Real.sqrt 8 / a ^ 2 *
        ∫ y in (0 : ℝ)..a,
          y * Real.sqrt (transformedRadicand a y) := by
  rw [gap9 a ha]
  calc
    (∫ y in (0 : ℝ)..a,
        y / a * Real.sqrt (y ^ 2 + a ^ 2) *
          Real.sqrt
            ((8 * y ^ 4 + 9 * a ^ 2 * y ^ 2 + 2 * a ^ 4) /
              (a ^ 2 * (y ^ 2 + a ^ 2)))) =
        ∫ y in (0 : ℝ)..a,
          (Real.sqrt 8 / a ^ 2) *
            (y * Real.sqrt (transformedRadicand a y)) := by
      apply intervalIntegral.integral_congr
      intro y hy
      change
        y / a * Real.sqrt (y ^ 2 + a ^ 2) *
            Real.sqrt
              ((8 * y ^ 4 + 9 * a ^ 2 * y ^ 2 + 2 * a ^ 4) /
                (a ^ 2 * (y ^ 2 + a ^ 2))) =
          Real.sqrt 8 / a ^ 2 *
            (y * Real.sqrt (transformedRadicand a y))
      have hsum : 0 < y ^ 2 + a ^ 2 := by
        nlinarith [sq_nonneg y, sq_pos_of_pos ha]
      have hsqrt : 0 < Real.sqrt (y ^ 2 + a ^ 2) :=
        Real.sqrt_pos.2 hsum
      have hnum :
          8 * y ^ 4 + 9 * a ^ 2 * y ^ 2 + 2 * a ^ 4 =
            8 * transformedRadicand a y := by
        unfold transformedRadicand
        ring
      have hden : Real.sqrt (a ^ 2 * (y ^ 2 + a ^ 2)) =
          a * Real.sqrt (y ^ 2 + a ^ 2) := by
        rw [Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq_eq_abs,
          abs_of_pos ha]
      rw [hnum, Real.sqrt_div,
        Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 8), hden]
      field_simp [ne_of_gt ha, ne_of_gt hsqrt] <;> ring
      rw [← hnum]
      positivity
    _ = Real.sqrt 8 / a ^ 2 *
        ∫ y in (0 : ℝ)..a,
          y * Real.sqrt (transformedRadicand a y) := by
      rw [intervalIntegral.integral_const_mul]

theorem gap11 (a : ℝ) (ha : 0 < a) :
    weightedLength a =
      Real.sqrt 2 / a ^ 2 *
        ∫ u in 9 * a ^ 2 / 16..25 * a ^ 2 / 16,
          Real.sqrt (u ^ 2 - 17 * a ^ 4 / 16 ^ 2) := by
  have hsqrt4 : Real.sqrt 4 = (2 : ℝ) := by
    rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num,
      Real.sqrt_sq_eq_abs, abs_of_nonneg (by norm_num)]
  have hsqrt8 : Real.sqrt 8 = 2 * Real.sqrt 2 := by
    rw [show (8 : ℝ) = 4 * 2 by norm_num,
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), hsqrt4]
  rw [gap10 a ha, ← transformed_substitution a ha, hsqrt8]
  ring

theorem gap12 (a : ℝ) (ha : 0 < a) :
    weightedLength a =
      endpointPrimitive a (25 * a ^ 2 / 16) -
        endpointPrimitive a (9 * a ^ 2 / 16) := by
  rw [gap11 a ha, sqrt_quadratic_integral a ha]
  unfold endpointPrimitive
  ring

theorem gap13 (a : ℝ) (ha : 0 < a) :
    weightedLength a =
      a ^ 2 / (256 * Real.sqrt 2) *
        (100 * Real.sqrt 38 - 72 -
          17 * Real.log ((25 + 4 * Real.sqrt 38) / 17)) := by
  have hradUpper :
      (25 * a ^ 2 / 16) ^ 2 - 17 * a ^ 4 / 16 ^ 2 =
        a ^ 4 * 38 / 16 := by
    ring
  have hradLower :
      (9 * a ^ 2 / 16) ^ 2 - 17 * a ^ 4 / 16 ^ 2 =
        a ^ 4 / 4 := by
    ring
  have hsqrtUpper :
      Real.sqrt ((25 * a ^ 2 / 16) ^ 2 - 17 * a ^ 4 / 16 ^ 2) =
        a ^ 2 * Real.sqrt 38 / 4 := by
    calc
      Real.sqrt ((25 * a ^ 2 / 16) ^ 2 - 17 * a ^ 4 / 16 ^ 2) =
          Real.sqrt ((a ^ 2 / 4) ^ 2 * 38) := by
            congr 1
            rw [hradUpper]
            ring
      _ = Real.sqrt ((a ^ 2 / 4) ^ 2) * Real.sqrt 38 := by
        rw [Real.sqrt_mul (sq_nonneg (a ^ 2 / 4))]
      _ = a ^ 2 * Real.sqrt 38 / 4 := by
        rw [Real.sqrt_sq_eq_abs,
          abs_of_nonneg (by positivity : 0 ≤ a ^ 2 / 4)]
        ring
  have hsqrtLower :
      Real.sqrt ((9 * a ^ 2 / 16) ^ 2 - 17 * a ^ 4 / 16 ^ 2) =
        a ^ 2 / 2 := by
    calc
      Real.sqrt ((9 * a ^ 2 / 16) ^ 2 - 17 * a ^ 4 / 16 ^ 2) =
          Real.sqrt ((a ^ 2 / 2) ^ 2) := by
            congr 1
            rw [hradLower]
            ring
      _ = a ^ 2 / 2 := by
        rw [Real.sqrt_sq_eq_abs,
          abs_of_nonneg (by positivity : 0 ≤ a ^ 2 / 2)]
  have hnumpos :
      0 < 25 * a ^ 2 / 16 + a ^ 2 * Real.sqrt 38 / 4 := by
    positivity
  have hdenpos : 0 < 9 * a ^ 2 / 16 + a ^ 2 / 2 := by
    positivity
  have hquot :
      (25 * a ^ 2 / 16 + a ^ 2 * Real.sqrt 38 / 4) /
          (9 * a ^ 2 / 16 + a ^ 2 / 2) =
        (25 + 4 * Real.sqrt 38) / 17 := by
    field_simp [ne_of_gt ha]
    <;> ring
  have hlog :
      Real.log (25 * a ^ 2 / 16 + a ^ 2 * Real.sqrt 38 / 4) =
        Real.log ((25 + 4 * Real.sqrt 38) / 17) +
          Real.log (9 * a ^ 2 / 16 + a ^ 2 / 2) := by
    have hd := Real.log_div (ne_of_gt hnumpos) (ne_of_gt hdenpos)
    rw [hquot] at hd
    linarith
  have hclean :
      endpointPrimitive a (25 * a ^ 2 / 16) -
          endpointPrimitive a (9 * a ^ 2 / 16) =
        a ^ 2 * Real.sqrt 2 / 512 *
          (100 * Real.sqrt 38 - 72 -
            17 * Real.log ((25 + 4 * Real.sqrt 38) / 17)) := by
    unfold endpointPrimitive
    rw [hsqrtUpper, hsqrtLower, hlog]
    field_simp [ne_of_gt ha]
    <;> ring
  have hsqrt2pos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsqrt2sq : (Real.sqrt 2) ^ 2 = (2 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hcoef : Real.sqrt 2 / 512 =
      1 / (256 * Real.sqrt 2) := by
    field_simp [ne_of_gt hsqrt2pos]
    nlinarith [hsqrt2sq]
  rw [gap12 a ha, hclean]
  calc
    a ^ 2 * Real.sqrt 2 / 512 *
        (100 * Real.sqrt 38 - 72 -
          17 * Real.log ((25 + 4 * Real.sqrt 38) / 17)) =
      a ^ 2 * (Real.sqrt 2 / 512) *
        (100 * Real.sqrt 38 - 72 -
          17 * Real.log ((25 + 4 * Real.sqrt 38) / 17)) := by ring
    _ = a ^ 2 * (1 / (256 * Real.sqrt 2)) *
        (100 * Real.sqrt 38 - 72 -
          17 * Real.log ((25 + 4 * Real.sqrt 38) / 17)) := by
      rw [hcoef]
    _ = a ^ 2 / (256 * Real.sqrt 2) *
        (100 * Real.sqrt 38 - 72 -
          17 * Real.log ((25 + 4 * Real.sqrt 38) / 17)) := by ring

end

end ProofGap.Exercise4240
