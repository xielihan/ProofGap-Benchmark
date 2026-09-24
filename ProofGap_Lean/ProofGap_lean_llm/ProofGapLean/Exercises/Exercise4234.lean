import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4234

noncomputable section

open scoped Interval

def cbrt (x : ℝ) : ℝ :=
  Real.rpow x (1 / 3 : ℝ)

def differenceCoord (a z : ℝ) : ℝ :=
  cbrt (9 * a / 8) * cbrt (z ^ 2)

def sumCoord (a z : ℝ) : ℝ :=
  1 / a * cbrt ((9 * a / 8) ^ 2) * cbrt (z ^ 4)

def xCoord (a z : ℝ) : ℝ :=
  1 / 2 * (sumCoord a z + differenceCoord a z)

def yCoord (a z : ℝ) : ℝ :=
  1 / 2 * (sumCoord a z - differenceCoord a z)

def curveMap (a z : ℝ) : ℝ × ℝ × ℝ :=
  (xCoord a z, yCoord a z, z)

def derivativeSquare (a z : ℝ) : ℝ :=
  cbrt (9 * a) / (2 * a) * cbrt (z ^ 2) +
    cbrt (3 * a ^ 2) / 6 * cbrt (z ^ (-2 : ℤ))

def speed (a z : ℝ) : ℝ :=
  Real.sqrt (derivativeSquare a z + 1)

def curveLength (a z₀ : ℝ) : ℝ :=
  ∫ z in (0 : ℝ)..z₀, speed a z

private def coefA (a : ℝ) : ℝ :=
  1 / a * cbrt ((9 * a / 8) ^ 2)

private def coefB (a : ℝ) : ℝ :=
  cbrt (9 * a / 8)

private def modelSpeed (a z : ℝ) : ℝ :=
  (2 * Real.sqrt 2 / 3 * coefA a) * z ^ ((1 : ℝ) / 3) +
    (Real.sqrt 2 / 3 * coefB a) * z ^ (-(1 : ℝ) / 3)

private theorem cbrt_pos (x : ℝ) (hx : 0 < x) :
    0 < cbrt x := by
  unfold cbrt
  exact Real.rpow_pos_of_pos hx _

private theorem cbrt_cubed (x : ℝ) (hx : 0 < x) :
    (cbrt x) ^ 3 = x := by
  unfold cbrt
  calc
    (x.rpow (1 / 3 : ℝ)) ^ 3 =
        x.rpow ((1 / 3 : ℝ) * 3) :=
      (Real.rpow_mul_natCast hx.le (1 / 3 : ℝ) 3).symm
    _ = x := by norm_num

private theorem cbrt_mul_of_pos
    (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    cbrt (x * y) = cbrt x * cbrt y := by
  apply (show Odd 3 by decide).pow_injective
  change (cbrt (x * y)) ^ 3 =
    (cbrt x * cbrt y) ^ 3
  rw [mul_pow, cbrt_cubed (x * y) (mul_pos hx hy),
    cbrt_cubed x hx, cbrt_cubed y hy]

private theorem cbrt_pow_eq_rpow
    (z : ℝ) (hz : 0 < z) (n : ℕ) :
    cbrt (z ^ n) = z ^ ((n : ℝ) / 3) := by
  calc
    cbrt (z ^ n) = (z ^ n).rpow (1 / 3 : ℝ) := rfl
    _ = (z.rpow (n : ℝ)).rpow (1 / 3 : ℝ) :=
      congrArg (fun x : ℝ => x.rpow (1 / 3 : ℝ))
        (Real.rpow_natCast z n).symm
    _ = z.rpow ((n : ℝ) * (1 / 3 : ℝ)) :=
      (Real.rpow_mul hz.le (n : ℝ) (1 / 3 : ℝ)).symm
    _ = z.rpow ((n : ℝ) / 3) := by
      congr 1
      ring

private theorem coefA_pos (a : ℝ) (ha : 0 < a) :
    0 < coefA a := by
  unfold coefA
  have hk : 0 < 9 * a / 8 := by positivity
  exact mul_pos (by positivity) (cbrt_pos _ (sq_pos_of_pos hk))

private theorem coefB_pos (a : ℝ) (ha : 0 < a) :
    0 < coefB a := by
  unfold coefB
  exact cbrt_pos _ (by positivity)

private theorem coefA_mul_coefB
    (a : ℝ) (ha : 0 < a) :
    coefA a * coefB a = 9 / 8 := by
  apply (show Odd 3 by decide).pow_injective
  change (coefA a * coefB a) ^ 3 = (9 / 8 : ℝ) ^ 3
  unfold coefA coefB
  have hk : 0 < 9 * a / 8 := by positivity
  rw [mul_pow, mul_pow, cbrt_cubed _ (sq_pos_of_pos hk),
    cbrt_cubed _ hk]
  field_simp [ha.ne']

private theorem coefA_eq
    (a : ℝ) (ha : 0 < a) :
    coefA a = 3 / 4 * cbrt (3 / a) := by
  apply (show Odd 3 by decide).pow_injective
  change (coefA a) ^ 3 =
    (3 / 4 * cbrt (3 / a)) ^ 3
  unfold coefA
  have hk : 0 < 9 * a / 8 := by positivity
  have hdiv : 0 < 3 / a := by positivity
  rw [mul_pow, mul_pow, cbrt_cubed _ (sq_pos_of_pos hk),
    cbrt_cubed _ hdiv]
  field_simp [ha.ne']
  ring

private theorem coefB_eq
    (a : ℝ) (ha : 0 < a) :
    coefB a = 3 / 2 * cbrt (a / 3) := by
  apply (show Odd 3 by decide).pow_injective
  change (coefB a) ^ 3 =
    (3 / 2 * cbrt (a / 3)) ^ 3
  unfold coefB
  have hk : 0 < 9 * a / 8 := by positivity
  have hdiv : 0 < a / 3 := by positivity
  rw [mul_pow, cbrt_cubed _ hk, cbrt_cubed _ hdiv]
  ring

private theorem hasDerivAt_cbrt_pow_four
    (z : ℝ) (hz : 0 < z) :
    HasDerivAt (fun w : ℝ => cbrt (w ^ 4))
      ((4 / 3 : ℝ) * z ^ ((1 : ℝ) / 3)) z := by
  have hr :
      HasDerivAt (fun w : ℝ => w ^ ((4 : ℝ) / 3))
        ((4 / 3 : ℝ) * z ^ ((1 : ℝ) / 3)) z := by
    have h :=
      Real.hasDerivAt_rpow_const (p := (4 / 3 : ℝ))
        (Or.inl hz.ne')
    simpa only [show (4 / 3 : ℝ) - 1 = 1 / 3 by ring] using h
  have hev :
      (fun w : ℝ => cbrt (w ^ 4)) =ᶠ[nhds z]
        (fun w : ℝ => w ^ ((4 : ℝ) / 3)) := by
    filter_upwards [eventually_gt_nhds hz] with w hw
    exact cbrt_pow_eq_rpow w hw 4
  exact hr.congr_of_eventuallyEq hev

private theorem hasDerivAt_cbrt_pow_two
    (z : ℝ) (hz : 0 < z) :
    HasDerivAt (fun w : ℝ => cbrt (w ^ 2))
      ((2 / 3 : ℝ) * z ^ (-(1 : ℝ) / 3)) z := by
  have hr :
      HasDerivAt (fun w : ℝ => w ^ ((2 : ℝ) / 3))
        ((2 / 3 : ℝ) * z ^ (-(1 : ℝ) / 3)) z := by
    have h :=
      Real.hasDerivAt_rpow_const (p := (2 / 3 : ℝ))
        (Or.inl hz.ne')
    simpa only [show (2 / 3 : ℝ) - 1 = -(1 : ℝ) / 3 by ring] using h
  have hev :
      (fun w : ℝ => cbrt (w ^ 2)) =ᶠ[nhds z]
        (fun w : ℝ => w ^ ((2 : ℝ) / 3)) := by
    filter_upwards [eventually_gt_nhds hz] with w hw
    exact cbrt_pow_eq_rpow w hw 2
  exact hr.congr_of_eventuallyEq hev

private theorem deriv_xCoord
    (a z : ℝ) (hz : 0 < z) :
    deriv (xCoord a) z =
      1 / 2 *
        (coefA a * ((4 / 3 : ℝ) * z ^ ((1 : ℝ) / 3)) +
          coefB a * ((2 / 3 : ℝ) * z ^ (-(1 : ℝ) / 3))) := by
  have h :=
    (((hasDerivAt_cbrt_pow_four z hz).const_mul (coefA a)).add
      ((hasDerivAt_cbrt_pow_two z hz).const_mul (coefB a))).const_mul
        (1 / 2 : ℝ)
  have hcurve :
      HasDerivAt (xCoord a)
        (1 / 2 *
          (coefA a * ((4 / 3 : ℝ) * z ^ ((1 : ℝ) / 3)) +
            coefB a * ((2 / 3 : ℝ) * z ^ (-(1 : ℝ) / 3)))) z := by
    change
      HasDerivAt
        (fun y : ℝ =>
          1 / 2 *
            (1 / a * cbrt ((9 * a / 8) ^ 2) *
                cbrt (y ^ 4) +
              cbrt (9 * a / 8) * cbrt (y ^ 2)))
        (1 / 2 *
          (coefA a * ((4 / 3 : ℝ) * z ^ ((1 : ℝ) / 3)) +
            coefB a * ((2 / 3 : ℝ) * z ^ (-(1 : ℝ) / 3)))) z
    simpa [coefA, coefB, mul_assoc] using h
  exact hcurve.deriv

private theorem deriv_yCoord
    (a z : ℝ) (hz : 0 < z) :
    deriv (yCoord a) z =
      1 / 2 *
        (coefA a * ((4 / 3 : ℝ) * z ^ ((1 : ℝ) / 3)) -
          coefB a * ((2 / 3 : ℝ) * z ^ (-(1 : ℝ) / 3))) := by
  have h :=
    (((hasDerivAt_cbrt_pow_four z hz).const_mul (coefA a)).sub
      ((hasDerivAt_cbrt_pow_two z hz).const_mul (coefB a))).const_mul
        (1 / 2 : ℝ)
  have hcurve :
      HasDerivAt (yCoord a)
        (1 / 2 *
          (coefA a * ((4 / 3 : ℝ) * z ^ ((1 : ℝ) / 3)) -
            coefB a * ((2 / 3 : ℝ) * z ^ (-(1 : ℝ) / 3)))) z := by
    change
      HasDerivAt
        (fun y : ℝ =>
          1 / 2 *
            (1 / a * cbrt ((9 * a / 8) ^ 2) *
                cbrt (y ^ 4) -
              cbrt (9 * a / 8) * cbrt (y ^ 2)))
        (1 / 2 *
          (coefA a * ((4 / 3 : ℝ) * z ^ ((1 : ℝ) / 3)) -
            coefB a * ((2 / 3 : ℝ) * z ^ (-(1 : ℝ) / 3)))) z
    simpa [coefA, coefB, mul_assoc] using h
  exact hcurve.deriv

private theorem cbrt_nine_mul_div
    (a : ℝ) (ha : 0 < a) :
    cbrt (9 * a) / a = cbrt (3 / a) ^ 2 := by
  apply (show Odd 3 by decide).pow_injective
  change (cbrt (9 * a) / a) ^ 3 =
    (cbrt (3 / a) ^ 2) ^ 3
  rw [show (cbrt (3 / a) ^ 2) ^ 3 =
      (cbrt (3 / a) ^ 3) ^ 2 by ring,
    div_pow, cbrt_cubed _ (by positivity),
    cbrt_cubed _ (by positivity)]
  field_simp [ha.ne']
  ring

private theorem cbrt_three_sq
    (a : ℝ) (ha : 0 < a) :
    cbrt (3 * a ^ 2) =
      3 * cbrt (a / 3) ^ 2 := by
  apply (show Odd 3 by decide).pow_injective
  change cbrt (3 * a ^ 2) ^ 3 =
    (3 * cbrt (a / 3) ^ 2) ^ 3
  rw [show (3 * cbrt (a / 3) ^ 2) ^ 3 =
      3 ^ 3 * (cbrt (a / 3) ^ 3) ^ 2 by ring,
    cbrt_cubed _ (by positivity),
    cbrt_cubed _ (by positivity)]
  ring

private theorem coefA_square_identity
    (a : ℝ) (ha : 0 < a) :
    8 / 9 * coefA a ^ 2 =
      cbrt (9 * a) / (2 * a) := by
  rw [coefA_eq a ha]
  have h := cbrt_nine_mul_div a ha
  field_simp [ha.ne'] at h ⊢
  nlinarith

private theorem coefB_square_identity
    (a : ℝ) (ha : 0 < a) :
    2 / 9 * coefB a ^ 2 =
      cbrt (3 * a ^ 2) / 6 := by
  rw [coefB_eq a ha, cbrt_three_sq a ha]
  ring

private theorem cbrt_zpow_neg_two
    (z : ℝ) (hz : 0 < z) :
    cbrt (z ^ (-2 : ℤ)) =
      z ^ (-(2 : ℝ) / 3) := by
  unfold cbrt
  calc
    (z ^ (-2 : ℤ)).rpow (1 / 3 : ℝ) =
        (z ^ (-2 : ℝ)) ^ (1 / 3 : ℝ) := by
      congr 1
      convert (Real.rpow_intCast z (-2)).symm using 1 <;> norm_num
    _ = z.rpow ((-2 : ℝ) * (1 / 3 : ℝ)) :=
      (Real.rpow_mul hz.le (-2 : ℝ) (1 / 3 : ℝ)).symm
    _ = z.rpow (-(2 : ℝ) / 3) := by
      congr 1
      ring

private theorem derivative_square_identity
    (a z : ℝ) (ha : 0 < a) (hz : 0 < z) :
    deriv (xCoord a) z ^ 2 + deriv (yCoord a) z ^ 2 =
      derivativeSquare a z := by
  have hp2 :
      (z ^ ((1 : ℝ) / 3)) ^ 2 = cbrt (z ^ 2) := by
    calc
      (z ^ ((1 : ℝ) / 3)) ^ 2 =
          z ^ (((1 : ℝ) / 3) * (2 : ℝ)) :=
        (Real.rpow_mul_natCast hz.le ((1 : ℝ) / 3) 2).symm
      _ = z ^ ((2 : ℝ) / 3) := by
        congr 1
        ring
      _ = cbrt (z ^ 2) :=
        (cbrt_pow_eq_rpow z hz 2).symm
  have hq2 :
      (z ^ (-(1 : ℝ) / 3)) ^ 2 =
        cbrt (z ^ (-2 : ℤ)) := by
    calc
      (z ^ (-(1 : ℝ) / 3)) ^ 2 =
          z ^ ((-(1 : ℝ) / 3) * (2 : ℝ)) :=
        (Real.rpow_mul_natCast hz.le (-(1 : ℝ) / 3) 2).symm
      _ = z ^ (-(2 : ℝ) / 3) := by
        congr 1
        ring
      _ = cbrt (z ^ (-2 : ℤ)) :=
        (cbrt_zpow_neg_two z hz).symm
  rw [deriv_xCoord a z hz, deriv_yCoord a z hz]
  calc
    (1 / 2 *
          (coefA a * ((4 / 3 : ℝ) * z ^ ((1 : ℝ) / 3)) +
            coefB a * ((2 / 3 : ℝ) * z ^ (-(1 : ℝ) / 3)))) ^ 2 +
        (1 / 2 *
          (coefA a * ((4 / 3 : ℝ) * z ^ ((1 : ℝ) / 3)) -
            coefB a * ((2 / 3 : ℝ) * z ^ (-(1 : ℝ) / 3)))) ^ 2 =
        8 / 9 * coefA a ^ 2 * (z ^ ((1 : ℝ) / 3)) ^ 2 +
          2 / 9 * coefB a ^ 2 * (z ^ (-(1 : ℝ) / 3)) ^ 2 := by
      ring
    _ = derivativeSquare a z := by
      rw [coefA_square_identity a ha, coefB_square_identity a ha,
        hp2, hq2]
      unfold derivativeSquare
      ring

private theorem speed_eq_modelSpeed
    (a z : ℝ) (ha : 0 < a) (hz : 0 < z) :
    speed a z = modelSpeed a z := by
  let A := coefA a
  let B := coefB a
  let p := z ^ ((1 : ℝ) / 3)
  let q := z ^ (-(1 : ℝ) / 3)
  have hA : 0 < A := by simpa [A] using coefA_pos a ha
  have hB : 0 < B := by simpa [B] using coefB_pos a ha
  have hp : 0 < p := Real.rpow_pos_of_pos hz _
  have hq : 0 < q := Real.rpow_pos_of_pos hz _
  have hAB : A * B = 9 / 8 := by
    simpa [A, B] using coefA_mul_coefB a ha
  have hpq : p * q = 1 := by
    dsimp [p, q]
    rw [← Real.rpow_add hz]
    norm_num
  have hs2 : Real.sqrt 2 ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num)
  have hdx :
      deriv (xCoord a) z =
        1 / 2 * (A * ((4 / 3 : ℝ) * p) +
          B * ((2 / 3 : ℝ) * q)) := by
    simpa [A, B, p, q] using deriv_xCoord a z hz
  have hdy :
      deriv (yCoord a) z =
        1 / 2 * (A * ((4 / 3 : ℝ) * p) -
          B * ((2 / 3 : ℝ) * q)) := by
    simpa [A, B, p, q] using deriv_yCoord a z hz
  have hinside :
      (1 / 2 * (A * ((4 / 3 : ℝ) * p) +
            B * ((2 / 3 : ℝ) * q))) ^ 2 +
          (1 / 2 * (A * ((4 / 3 : ℝ) * p) -
            B * ((2 / 3 : ℝ) * q))) ^ 2 + 1 =
        ((2 * Real.sqrt 2 / 3 * A) * p +
          (Real.sqrt 2 / 3 * B) * q) ^ 2 := by
    calc
      (1 / 2 * (A * ((4 / 3 : ℝ) * p) +
              B * ((2 / 3 : ℝ) * q))) ^ 2 +
            (1 / 2 * (A * ((4 / 3 : ℝ) * p) -
              B * ((2 / 3 : ℝ) * q))) ^ 2 + 1 =
          8 / 9 * A ^ 2 * p ^ 2 +
            2 / 9 * B ^ 2 * q ^ 2 + 1 := by ring
      _ = 8 / 9 * A ^ 2 * p ^ 2 +
            2 / 9 * B ^ 2 * q ^ 2 +
              8 / 9 * (A * B) * (p * q) := by
            rw [hAB, hpq]
            norm_num
      _ = ((2 * Real.sqrt 2 / 3 * A) * p +
            (Real.sqrt 2 / 3 * B) * q) ^ 2 := by
            ring_nf
            rw [hs2]
            ring
  rw [speed, ← derivative_square_identity a z ha hz, hdx, hdy, hinside, Real.sqrt_sq_eq_abs,
    abs_of_pos]
  · rfl
  · exact add_pos
      (mul_pos (mul_pos (by positivity) hA) hp)
      (mul_pos (mul_pos (by positivity) hB) hq)

private theorem integral_modelSpeed
    (a z₀ : ℝ) :
    (∫ z in (0 : ℝ)..z₀, modelSpeed a z) =
      Real.sqrt 2 / 2 *
        (coefA a * z₀ ^ ((4 : ℝ) / 3) +
          coefB a * z₀ ^ ((2 : ℝ) / 3)) := by
  have hthird :
      IntervalIntegrable (fun z : ℝ => z ^ ((1 : ℝ) / 3))
        MeasureTheory.volume 0 z₀ :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have hnegthird :
      IntervalIntegrable (fun z : ℝ => z ^ (-(1 : ℝ) / 3))
        MeasureTheory.volume 0 z₀ :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  unfold modelSpeed
  rw [intervalIntegral.integral_add
      (hthird.const_mul _) (hnegthird.const_mul _),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    integral_rpow (Or.inl (by norm_num :
      (-1 : ℝ) < (1 : ℝ) / 3)),
    integral_rpow (Or.inl (by norm_num :
      (-1 : ℝ) < -(1 : ℝ) / 3))]
  rw [Real.zero_rpow (by norm_num : (1 : ℝ) / 3 + 1 ≠ 0),
    Real.zero_rpow (by norm_num : -(1 : ℝ) / 3 + 1 ≠ 0)]
  ring_nf

private def finalValue (a z₀ : ℝ) : ℝ :=
  3 / (4 * Real.sqrt 2) *
    (cbrt (3 * z₀ ^ 4 / a) +
      2 * cbrt (a * z₀ ^ 2 / 3))

private theorem integral_value_eq_finalValue
    (a z₀ : ℝ) (ha : 0 < a) (hz₀ : 0 < z₀) :
    Real.sqrt 2 / 2 *
        (coefA a * z₀ ^ ((4 : ℝ) / 3) +
          coefB a * z₀ ^ ((2 : ℝ) / 3)) =
      finalValue a z₀ := by
  have h3a : 0 < 3 / a := by positivity
  have ha3 : 0 < a / 3 := by positivity
  have hz4 : 0 < z₀ ^ 4 := pow_pos hz₀ 4
  have hz2 : 0 < z₀ ^ 2 := pow_pos hz₀ 2
  have hfirst :
      cbrt (3 * z₀ ^ 4 / a) =
        cbrt (3 / a) * z₀ ^ ((4 : ℝ) / 3) := by
    calc
      cbrt (3 * z₀ ^ 4 / a) =
          cbrt ((3 / a) * z₀ ^ 4) := by
            congr 1
            field_simp [ha.ne']
      _ = cbrt (3 / a) * cbrt (z₀ ^ 4) :=
        cbrt_mul_of_pos _ _ h3a hz4
      _ = _ := by
        rw [cbrt_pow_eq_rpow z₀ hz₀ 4]
        norm_num
  have hsecond :
      cbrt (a * z₀ ^ 2 / 3) =
        cbrt (a / 3) * z₀ ^ ((2 : ℝ) / 3) := by
    calc
      cbrt (a * z₀ ^ 2 / 3) =
          cbrt ((a / 3) * z₀ ^ 2) := by
            congr 1
            ring
      _ = cbrt (a / 3) * cbrt (z₀ ^ 2) :=
        cbrt_mul_of_pos _ _ ha3 hz2
      _ = _ := by
        rw [cbrt_pow_eq_rpow z₀ hz₀ 2]
        norm_num
  have hspos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hs2 : Real.sqrt 2 ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num)
  rw [finalValue, hfirst, hsecond, coefA_eq a ha, coefB_eq a ha]
  field_simp [hspos.ne']
  rw [hs2]
  ring

private theorem curveLength_eq_finalValue
    (a z₀ : ℝ) (ha : 0 < a) (hz₀ : 0 ≤ z₀) :
    curveLength a z₀ = finalValue a z₀ := by
  rcases hz₀.eq_or_lt with rfl | hz₀
  · simp [curveLength, finalValue, cbrt]
  have hae :
      ∀ᵐ z : ℝ ∂MeasureTheory.volume,
        z ∈ Set.uIoc (0 : ℝ) z₀ →
          speed a z = modelSpeed a z := by
    have hne :
        ∀ᵐ z : ℝ ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ), z ≠ 0 := by
      rw [MeasureTheory.ae_iff]
      simp
    filter_upwards [hne] with z hz
    intro hmem
    have hzpos : 0 < z := by
      rw [Set.uIoc_of_le hz₀.le] at hmem
      exact hmem.1
    exact speed_eq_modelSpeed a z ha hzpos
  unfold curveLength
  rw [intervalIntegral.integral_congr_ae hae,
    integral_modelSpeed a z₀]
  exact integral_value_eq_finalValue a z₀ ha hz₀

private def transformedOne (a z₀ : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..cbrt (z₀ ^ 2),
    Real.sqrt
        (cbrt (9 * a) / (2 * a) * t +
          cbrt (3 * a ^ 2) / 6 * (1 / t) + 1) *
      (3 * Real.sqrt t / 2)

private def transformedTwo (a z₀ : ℝ) : ℝ :=
  3 / 2 *
    ∫ t in (0 : ℝ)..cbrt (z₀ ^ 2),
      Real.sqrt
        (cbrt (9 * a) / (2 * a) * t ^ 2 +
          t + cbrt (3 * a ^ 2) / 6)

private def transformedThree (a z₀ : ℝ) : ℝ :=
  3 / 2 *
    ∫ t in (0 : ℝ)..cbrt (z₀ ^ 2),
      (1 / Real.sqrt 2 * cbrt (3 / a) * t +
        1 / Real.sqrt 2 * cbrt (a / 3))

private theorem cbrt_nonneg_of_nonneg
    (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ cbrt x := by
  unfold cbrt
  exact Real.rpow_nonneg hx _

private theorem cbrt_ratio_product
    (a : ℝ) (ha : 0 < a) :
    cbrt (3 / a) * cbrt (a / 3) = 1 := by
  rw [← cbrt_mul_of_pos (3 / a) (a / 3) (by positivity) (by positivity)]
  have hprod : (3 / a) * (a / 3) = (1 : ℝ) := by
    field_simp [ha.ne']
  rw [hprod]
  simp [cbrt]

private theorem first_coefficient
    (a : ℝ) (ha : 0 < a) :
    cbrt (9 * a) / (2 * a) =
      (1 / 2 : ℝ) * cbrt (3 / a) ^ 2 := by
  have h := cbrt_nine_mul_div a ha
  field_simp [ha.ne'] at h ⊢
  nlinarith

private theorem second_coefficient
    (a : ℝ) (ha : 0 < a) :
    cbrt (3 * a ^ 2) / 6 =
      (1 / 2 : ℝ) * cbrt (a / 3) ^ 2 := by
  rw [cbrt_three_sq a ha]
  ring

private theorem quadratic_sqrt_eq_linear
    (a t : ℝ) (ha : 0 < a) (ht : 0 ≤ t) :
    Real.sqrt
        (cbrt (9 * a) / (2 * a) * t ^ 2 +
          t + cbrt (3 * a ^ 2) / 6) =
      1 / Real.sqrt 2 * cbrt (3 / a) * t +
        1 / Real.sqrt 2 * cbrt (a / 3) := by
  have hspos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hs2 : Real.sqrt 2 ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num)
  have hinside :
      cbrt (9 * a) / (2 * a) * t ^ 2 +
          t + cbrt (3 * a ^ 2) / 6 =
        (1 / Real.sqrt 2 * cbrt (3 / a) * t +
          1 / Real.sqrt 2 * cbrt (a / 3)) ^ 2 := by
    rw [first_coefficient a ha, second_coefficient a ha]
    have hprod := cbrt_ratio_product a ha
    field_simp [hspos.ne']
    rw [hs2]
    nlinarith
  rw [hinside, Real.sqrt_sq_eq_abs, abs_of_nonneg]
  exact add_nonneg
    (mul_nonneg
      (mul_nonneg (by positivity) (cbrt_nonneg_of_nonneg _ (by positivity)))
      ht)
    (mul_nonneg (by positivity) (cbrt_nonneg_of_nonneg _ (by positivity)))

private theorem first_transform_pointwise
    (a t : ℝ) (ha : 0 < a) (ht : 0 < t) :
    Real.sqrt
          (cbrt (9 * a) / (2 * a) * t +
            cbrt (3 * a ^ 2) / 6 * (1 / t) + 1) *
        (3 * Real.sqrt t / 2) =
      (3 / 2 : ℝ) *
        Real.sqrt
          (cbrt (9 * a) / (2 * a) * t ^ 2 +
            t + cbrt (3 * a ^ 2) / 6) := by
  have hfirst : 0 ≤ cbrt (9 * a) / (2 * a) := by
    rw [first_coefficient a ha]
    positivity
  have hsecond : 0 ≤ cbrt (3 * a ^ 2) / 6 := by
    rw [second_coefficient a ha]
    positivity
  have hinner :
      0 ≤ cbrt (9 * a) / (2 * a) * t +
        cbrt (3 * a ^ 2) / 6 * (1 / t) + 1 := by
    positivity
  have hmul :
      (cbrt (9 * a) / (2 * a) * t +
          cbrt (3 * a ^ 2) / 6 * (1 / t) + 1) * t =
        cbrt (9 * a) / (2 * a) * t ^ 2 +
          t + cbrt (3 * a ^ 2) / 6 := by
    field_simp [ht.ne']
    ring
  rw [show 3 * Real.sqrt t / 2 = (3 / 2 : ℝ) * Real.sqrt t by ring]
  calc
    Real.sqrt
          (cbrt (9 * a) / (2 * a) * t +
            cbrt (3 * a ^ 2) / 6 * (1 / t) + 1) *
        ((3 / 2 : ℝ) * Real.sqrt t) =
        (3 / 2 : ℝ) *
          (Real.sqrt
              (cbrt (9 * a) / (2 * a) * t +
                cbrt (3 * a ^ 2) / 6 * (1 / t) + 1) *
            Real.sqrt t) := by ring
    _ = (3 / 2 : ℝ) *
        Real.sqrt
          (cbrt (9 * a) / (2 * a) * t ^ 2 +
            t + cbrt (3 * a ^ 2) / 6) := by
      rw [← Real.sqrt_mul hinner, hmul]

private theorem transformedOne_eq_transformedTwo
    (a z₀ : ℝ) (ha : 0 < a) (hz₀ : 0 ≤ z₀) :
    transformedOne a z₀ = transformedTwo a z₀ := by
  unfold transformedOne transformedTwo
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr_ae
  have hT : 0 ≤ cbrt (z₀ ^ 2) :=
    cbrt_nonneg_of_nonneg _ (sq_nonneg z₀)
  filter_upwards [MeasureTheory.Measure.ae_ne
    (MeasureTheory.volume : MeasureTheory.Measure ℝ) 0] with t ht0
  intro htmem
  rw [Set.uIoc_of_le hT] at htmem
  exact first_transform_pointwise a t ha
    (lt_of_le_of_ne htmem.1.le (Ne.symm ht0))

private theorem transformedTwo_eq_transformedThree
    (a z₀ : ℝ) (ha : 0 < a) (hz₀ : 0 ≤ z₀) :
    transformedTwo a z₀ = transformedThree a z₀ := by
  unfold transformedTwo transformedThree
  congr 1
  apply intervalIntegral.integral_congr
  intro t htmem
  have hT : 0 ≤ cbrt (z₀ ^ 2) :=
    cbrt_nonneg_of_nonneg _ (sq_nonneg z₀)
  rw [Set.uIcc_of_le hT] at htmem
  exact quadratic_sqrt_eq_linear a t ha htmem.1

private theorem transformedThree_eq_finalValue
    (a z₀ : ℝ) (ha : 0 < a) (hz₀ : 0 ≤ z₀) :
    transformedThree a z₀ = finalValue a z₀ := by
  rcases hz₀.eq_or_lt with rfl | hz₀
  · simp [transformedThree, finalValue, cbrt]
  have hT :
      cbrt (z₀ ^ 2) = z₀ ^ ((2 : ℝ) / 3) :=
    cbrt_pow_eq_rpow z₀ hz₀ 2
  have hT2 :
      (z₀ ^ ((2 : ℝ) / 3)) ^ 2 =
        z₀ ^ ((4 : ℝ) / 3) := by
    calc
      (z₀ ^ ((2 : ℝ) / 3)) ^ 2 =
          z₀ ^ (((2 : ℝ) / 3) * (2 : ℝ)) :=
        (Real.rpow_mul_natCast hz₀.le ((2 : ℝ) / 3) 2).symm
      _ = z₀ ^ ((4 : ℝ) / 3) := by
        congr 1
        ring
  unfold transformedThree
  have hadd :
      (∫ t in (0 : ℝ)..cbrt (z₀ ^ 2),
          1 / Real.sqrt 2 * cbrt (3 / a) * t +
            1 / Real.sqrt 2 * cbrt (a / 3)) =
        (∫ t in (0 : ℝ)..cbrt (z₀ ^ 2),
          1 / Real.sqrt 2 * cbrt (3 / a) * t) +
        ∫ t in (0 : ℝ)..cbrt (z₀ ^ 2),
          1 / Real.sqrt 2 * cbrt (a / 3) := by
    exact intervalIntegral.integral_add
      ((continuous_const.mul continuous_id).intervalIntegrable _ _)
      (continuous_const.intervalIntegrable _ _)
  rw [hadd,
    intervalIntegral.integral_const_mul,
    integral_id, intervalIntegral.integral_const]
  simp only [sub_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
    zero_smul, smul_eq_mul, sub_zero]
  rw [hT, hT2]
  rw [← integral_value_eq_finalValue a z₀ ha hz₀,
    coefA_eq a ha, coefB_eq a ha]
  have hspos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hs2 : Real.sqrt 2 ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num)
  field_simp [hspos.ne']
  rw [hs2]
  ring

theorem gap1 (a z : ℝ) (ha : 0 < a) :
    xCoord a z =
      1 / 2 *
        (1 / a * cbrt ((9 * a / 8) ^ 2) * cbrt (z ^ 4) +
          cbrt (9 * a / 8) * cbrt (z ^ 2)) := by
  rfl

theorem gap2 (a z : ℝ) (ha : 0 < a) :
    yCoord a z =
      1 / 2 *
        (1 / a * cbrt ((9 * a / 8) ^ 2) * cbrt (z ^ 4) -
          cbrt (9 * a / 8) * cbrt (z ^ 2)) := by
  rfl

theorem gap3 (a z : ℝ) (ha : 0 < a) (hz : 0 < z) :
    deriv (xCoord a) z ^ 2 + deriv (yCoord a) z ^ 2 =
      derivativeSquare a z := by
  exact derivative_square_identity a z ha hz

theorem gap4 (a z₀ : ℝ) (ha : 0 < a) (hz₀ : 0 ≤ z₀) :
    curveLength a z₀ =
      ∫ z in (0 : ℝ)..z₀,
        Real.sqrt
          (cbrt (9 * a) / (2 * a) * cbrt (z ^ 2) +
            cbrt (3 * a ^ 2) / 6 * cbrt (z ^ (-2 : ℤ)) + 1) := by
  rfl

theorem gap5 (a z₀ : ℝ) (ha : 0 < a) (hz₀ : 0 ≤ z₀) :
    curveLength a z₀ =
      ∫ t in (0 : ℝ)..cbrt (z₀ ^ 2),
        Real.sqrt
            (cbrt (9 * a) / (2 * a) * t +
              cbrt (3 * a ^ 2) / 6 * (1 / t) + 1) *
          (3 * Real.sqrt t / 2) := by
  change curveLength a z₀ = transformedOne a z₀
  rw [curveLength_eq_finalValue a z₀ ha hz₀,
    transformedOne_eq_transformedTwo a z₀ ha hz₀,
    transformedTwo_eq_transformedThree a z₀ ha hz₀,
    transformedThree_eq_finalValue a z₀ ha hz₀]

theorem gap6 (a z₀ : ℝ) (ha : 0 < a) (hz₀ : 0 ≤ z₀) :
    curveLength a z₀ =
      3 / 2 *
        ∫ t in (0 : ℝ)..cbrt (z₀ ^ 2),
          Real.sqrt
            (cbrt (9 * a) / (2 * a) * t ^ 2 +
              t + cbrt (3 * a ^ 2) / 6) := by
  change curveLength a z₀ = transformedTwo a z₀
  rw [curveLength_eq_finalValue a z₀ ha hz₀,
    transformedTwo_eq_transformedThree a z₀ ha hz₀,
    transformedThree_eq_finalValue a z₀ ha hz₀]

theorem gap7 (a z₀ : ℝ) (ha : 0 < a) (hz₀ : 0 ≤ z₀) :
    curveLength a z₀ =
      3 / 2 *
        ∫ t in (0 : ℝ)..cbrt (z₀ ^ 2),
          (1 / Real.sqrt 2 * cbrt (3 / a) * t +
            1 / Real.sqrt 2 * cbrt (a / 3)) := by
  change curveLength a z₀ = transformedThree a z₀
  rw [curveLength_eq_finalValue a z₀ ha hz₀,
    transformedThree_eq_finalValue a z₀ ha hz₀]

theorem gap8 (a z₀ : ℝ) (ha : 0 < a) (hz₀ : 0 ≤ z₀) :
    3 / 2 *
        (∫ t in (0 : ℝ)..cbrt (z₀ ^ 2),
          (1 / Real.sqrt 2 * cbrt (3 / a) * t +
            1 / Real.sqrt 2 * cbrt (a / 3))) =
      3 / (4 * Real.sqrt 2) *
        (cbrt (3 * z₀ ^ 4 / a) +
          2 * cbrt (a * z₀ ^ 2 / 3)) := by
  change transformedThree a z₀ = finalValue a z₀
  exact transformedThree_eq_finalValue a z₀ ha hz₀

theorem gap9 (a z₀ : ℝ) (ha : 0 < a) (hz₀ : 0 ≤ z₀) :
    curveLength a z₀ =
      3 / (4 * Real.sqrt 2) *
        (cbrt (3 * z₀ ^ 4 / a) +
          2 * cbrt (a * z₀ ^ 2 / 3)) := by
  change curveLength a z₀ = finalValue a z₀
  exact curveLength_eq_finalValue a z₀ ha hz₀

end

end ProofGap.Exercise4234
