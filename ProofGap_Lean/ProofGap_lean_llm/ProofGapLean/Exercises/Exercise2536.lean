import ProofGapLean.Prelude.Analysis
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.SpecificFunctions.Pow

open scoped Interval
open MeasureTheory

namespace ProofGap.Exercise2536

noncomputable section

attribute [local simp] Finset.sum_range_succ

def firstMesh (i : ℕ) : ℝ := Real.pi * i / 6
def firstSample (i : ℕ) : ℝ :=
  Real.sqrt (3 + Real.cos (firstMesh i))
def firstIntegral : ℝ :=
  ∫ x in (0 : ℝ)..Real.pi, Real.sqrt (3 + Real.cos x)
def firstRoundedSimpson : ℝ :=
  Real.pi / 18 *
    (2 + 1.414 + 4 * (1.966 + 1.732 + 1.461) +
      2 * (1.871 + 1.581))

def sinc (x : ℝ) : ℝ := if x = 0 then 1 else Real.sin x / x
def secondMesh (i : ℕ) : ℝ := Real.pi * i / 20
def secondSample (i : ℕ) : ℝ := sinc (secondMesh i)
def secondIntegral : ℝ := ∫ x in (0 : ℝ)..Real.pi / 2, sinc x
def secondRoundedSimpson : ℝ :=
  Real.pi / 60 *
    (1 + 0.63662 +
      4 * (0.99589 + 0.96340 + 0.90032 + 0.81033 + 0.69865) +
      2 * (0.98363 + 0.93549 + 0.85839 + 0.75683))

def logRatio (x : ℝ) : ℝ := if x = 0 then 1 else x / Real.log (1 + x)
def thirdMesh (i : ℕ) : ℝ := i / 6
def thirdSample (i : ℕ) : ℝ := logRatio (thirdMesh i)
def thirdIntegral : ℝ := ∫ x in (0 : ℝ)..1, logRatio x
def thirdRoundedSimpson : ℝ :=
  1 / 18 *
    (1 + 1.4427 + 4 * (1.0812 + 1.2332 + 1.3748) +
      2 * (1.1587 + 1.3051))

private theorem abs_sqrt_sub_lt {q c e : ℝ}
    (hce : 0 ≤ c - e) (he : 0 ≤ e) (hq : 0 ≤ q)
    (hlo : (c - e) ^ 2 < q) (hhi : q < (c + e) ^ 2) :
    |Real.sqrt q - c| < e := by
  rw [abs_lt]
  constructor
  · have hs : c - e < Real.sqrt q := (Real.lt_sqrt hce).2 hlo
    linarith
  · have hcpe : 0 ≤ c + e := by linarith
    have hs : Real.sqrt q < c + e := (Real.sqrt_lt hq hcpe).2 hhi
    linarith

private theorem sqrt_three_bounds :
    (1.73205 : ℝ) < Real.sqrt 3 ∧ Real.sqrt 3 < 1.73206 := by
  constructor
  · rw [Real.lt_sqrt (by norm_num)]
    norm_num
  · rw [Real.sqrt_lt (by norm_num) (by norm_num)]
    norm_num

private def sqrtCore6 (u : ℝ) : ℝ :=
  1 + u / 6 - u ^ 2 / 72 + u ^ 3 / 432 -
    5 * u ^ 4 / 10368 + 7 * u ^ 5 / 62208 -
    7 * u ^ 6 / 248832

private def sqrtResidual6 (u : ℝ) : ℝ :=
  u ^ 7 * (11 / 746496) + u ^ 8 * (-55 / 35831808) +
    u ^ 9 * (77 / 322486272) + u ^ 10 * (-77 / 1934917632) +
    u ^ 11 * (49 / 7739670528) + u ^ 12 * (-49 / 61917364224)

private theorem sqrt_residual_eq (u : ℝ) :
    1 + u / 3 - sqrtCore6 u ^ 2 = sqrtResidual6 u := by
  unfold sqrtCore6
  unfold sqrtResidual6
  ring_nf

private theorem sqrtCore6_error {u : ℝ} (hu : |u| ≤ 1) :
    |Real.sqrt (3 + u) - Real.sqrt 3 * sqrtCore6 u| < (1 : ℝ) / 30000 := by
  have hterm (n : ℕ) (c : ℝ) : |u ^ n * c| ≤ |c| := by
    calc
      |u ^ n * c| = |u| ^ n * |c| := by rw [abs_mul, abs_pow]
      _ ≤ 1 * |c| := by
        exact mul_le_mul_of_nonneg_right
          (pow_le_one₀ (abs_nonneg u) hu) (abs_nonneg c)
      _ = |c| := one_mul _
  have hres : |sqrtResidual6 u| < (1 : ℝ) / 60000 := by
    unfold sqrtResidual6
    calc
      |u ^ 7 * (11 / 746496) + u ^ 8 * (-55 / 35831808) +
          u ^ 9 * (77 / 322486272) + u ^ 10 * (-77 / 1934917632) +
          u ^ 11 * (49 / 7739670528) + u ^ 12 * (-49 / 61917364224)| ≤
          |u ^ 7 * (11 / 746496)| + |u ^ 8 * (-55 / 35831808)| +
          |u ^ 9 * (77 / 322486272)| + |u ^ 10 * (-77 / 1934917632)| +
          |u ^ 11 * (49 / 7739670528)| + |u ^ 12 * (-49 / 61917364224)| := by
        rw [abs_le]
        constructor
        · linarith [neg_abs_le (u ^ 7 * (11 / 746496)),
            neg_abs_le (u ^ 8 * (-55 / 35831808)),
            neg_abs_le (u ^ 9 * (77 / 322486272)),
            neg_abs_le (u ^ 10 * (-77 / 1934917632)),
            neg_abs_le (u ^ 11 * (49 / 7739670528)),
            neg_abs_le (u ^ 12 * (-49 / 61917364224))]
        · linarith [le_abs_self (u ^ 7 * (11 / 746496)),
            le_abs_self (u ^ 8 * (-55 / 35831808)),
            le_abs_self (u ^ 9 * (77 / 322486272)),
            le_abs_self (u ^ 10 * (-77 / 1934917632)),
            le_abs_self (u ^ 11 * (49 / 7739670528)),
            le_abs_self (u ^ 12 * (-49 / 61917364224))]
      _ ≤ |(11 / 746496 : ℝ)| + |(-55 / 35831808 : ℝ)| +
          |(77 / 322486272 : ℝ)| + |(-77 / 1934917632 : ℝ)| +
          |(49 / 7739670528 : ℝ)| + |(-49 / 61917364224 : ℝ)| := by
        linarith [hterm 7 (11 / 746496), hterm 8 (-55 / 35831808),
          hterm 9 (77 / 322486272), hterm 10 (-77 / 1934917632),
          hterm 11 (49 / 7739670528), hterm 12 (-49 / 61917364224)]
      _ < (1 : ℝ) / 60000 := by norm_num
  have hq : (4 / 5 : ℝ) ≤ sqrtCore6 u := by
    have h1 := hterm 1 (1 / 6)
    have h2 := hterm 2 (1 / 72)
    have h3 := hterm 3 (1 / 432)
    have h4 := hterm 4 (5 / 10368)
    have h5 := hterm 5 (7 / 62208)
    have h6 := hterm 6 (7 / 248832)
    unfold sqrtCore6
    norm_num only [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 6)] at h1
    norm_num only [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 72)] at h2
    norm_num only [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 432)] at h3
    norm_num only [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 5 / 10368)] at h4
    norm_num only [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 7 / 62208)] at h5
    norm_num only [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 7 / 248832)] at h6
    nlinarith [neg_abs_le (u ^ 1 * (1 / 6)),
      le_abs_self (u ^ 2 * (1 / 72)),
      neg_abs_le (u ^ 3 * (1 / 432)),
      le_abs_self (u ^ 4 * (5 / 10368)),
      neg_abs_le (u ^ 5 * (7 / 62208)),
      le_abs_self (u ^ 6 * (7 / 248832))]
  have hsqrt3 : (5 / 4 : ℝ) ≤ Real.sqrt 3 := by
    linarith [sqrt_three_bounds.1]
  have hpoly : 1 ≤ Real.sqrt 3 * sqrtCore6 u := by
    calc
      (1 : ℝ) = (5 / 4) * (4 / 5) := by norm_num
      _ ≤ Real.sqrt 3 * sqrtCore6 u := by
        exact mul_le_mul hsqrt3 hq (by norm_num) (Real.sqrt_nonneg 3)
  have harg : 0 ≤ 3 + u := by
    have hu' := neg_abs_le u
    linarith
  have hsqrt : 1 ≤ Real.sqrt (3 + u) := by
    rw [Real.one_le_sqrt]
    have hu' := neg_abs_le u
    linarith
  have hsum : 2 ≤ |Real.sqrt (3 + u) + Real.sqrt 3 * sqrtCore6 u| := by
    rw [abs_of_nonneg]
    · linarith
    · positivity
  have hid :
      (Real.sqrt (3 + u) - Real.sqrt 3 * sqrtCore6 u) *
          (Real.sqrt (3 + u) + Real.sqrt 3 * sqrtCore6 u) =
        3 * sqrtResidual6 u := by
    calc
      _ = Real.sqrt (3 + u) ^ 2 -
          (Real.sqrt 3 * sqrtCore6 u) ^ 2 := by ring
      _ = (3 + u) - 3 * sqrtCore6 u ^ 2 := by
        rw [Real.sq_sqrt harg, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
      _ = 3 * sqrtResidual6 u := by
        rw [← sqrt_residual_eq]
        ring
  have habs :
      |Real.sqrt (3 + u) - Real.sqrt 3 * sqrtCore6 u| *
          |Real.sqrt (3 + u) + Real.sqrt 3 * sqrtCore6 u| =
        |3 * sqrtResidual6 u| := by
    rw [← abs_mul, hid]
  have hnum : |3 * sqrtResidual6 u| < (1 : ℝ) / 20000 := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]
    nlinarith
  have hmul :
      2 * |Real.sqrt (3 + u) - Real.sqrt 3 * sqrtCore6 u| ≤
        |Real.sqrt (3 + u) - Real.sqrt 3 * sqrtCore6 u| *
          |Real.sqrt (3 + u) + Real.sqrt 3 * sqrtCore6 u| := by
    simpa only [mul_comm] using
      mul_le_mul_of_nonneg_left hsum
        (abs_nonneg (Real.sqrt (3 + u) - Real.sqrt 3 * sqrtCore6 u))
  rw [habs] at hmul
  nlinarith

private theorem integral_cos_pow_one_zero_pi :
    (∫ x in (0 : ℝ)..Real.pi, Real.cos x) = 0 := by
  rw [integral_cos]
  simp

private theorem integral_cos_pow_two_zero_pi :
    (∫ x in (0 : ℝ)..Real.pi, Real.cos x ^ 2) = Real.pi / 2 := by
  rw [integral_cos_sq]
  simp

private theorem integral_cos_pow_three_zero_pi :
    (∫ x in (0 : ℝ)..Real.pi, Real.cos x ^ 3) = 0 := by
  rw [integral_cos_pow_three]
  simp

private theorem integral_cos_pow_four_zero_pi :
    (∫ x in (0 : ℝ)..Real.pi, Real.cos x ^ 4) = 3 * Real.pi / 8 := by
  rw [show 4 = 2 + 2 by norm_num, integral_cos_pow]
  rw [integral_cos_pow_two_zero_pi]
  simp
  ring

private theorem integral_cos_pow_five_zero_pi :
    (∫ x in (0 : ℝ)..Real.pi, Real.cos x ^ 5) = 0 := by
  rw [show 5 = 3 + 2 by norm_num, integral_cos_pow]
  rw [integral_cos_pow_three_zero_pi]
  simp

private theorem integral_cos_pow_six_zero_pi :
    (∫ x in (0 : ℝ)..Real.pi, Real.cos x ^ 6) = 5 * Real.pi / 16 := by
  rw [show 6 = 4 + 2 by norm_num, integral_cos_pow]
  rw [integral_cos_pow_four_zero_pi]
  simp
  ring

private def firstIntegralCore : ℝ :=
  1 - (1 / 72 : ℝ) * (1 / 2) -
    (5 / 10368 : ℝ) * (3 / 8) -
    (7 / 248832 : ℝ) * (5 / 16)

private theorem integral_sqrtCore6_cos :
    (∫ x in (0 : ℝ)..Real.pi, sqrtCore6 (Real.cos x)) =
      Real.pi * firstIntegralCore := by
  unfold sqrtCore6
  have contInt (f : ℝ → ℝ) (hf : Continuous f) :
      IntervalIntegrable f volume 0 Real.pi := hf.intervalIntegrable 0 Real.pi
  rw [intervalIntegral.integral_sub (contInt _ (by fun_prop)) (contInt _ (by fun_prop))]
  rw [intervalIntegral.integral_add (contInt _ (by fun_prop)) (contInt _ (by fun_prop))]
  rw [intervalIntegral.integral_sub (contInt _ (by fun_prop)) (contInt _ (by fun_prop))]
  rw [intervalIntegral.integral_add (contInt _ (by fun_prop)) (contInt _ (by fun_prop))]
  rw [intervalIntegral.integral_sub (contInt _ (by fun_prop)) (contInt _ (by fun_prop))]
  rw [intervalIntegral.integral_add (contInt _ (by fun_prop)) (contInt _ (by fun_prop))]
  simp only [intervalIntegral.integral_div, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const, smul_eq_mul, mul_one]
  rw [integral_cos_pow_one_zero_pi, integral_cos_pow_two_zero_pi,
    integral_cos_pow_three_zero_pi, integral_cos_pow_four_zero_pi,
    integral_cos_pow_five_zero_pi, integral_cos_pow_six_zero_pi]
  unfold firstIntegralCore
  ring

private theorem firstIntegral_poly_error :
    |firstIntegral - Real.sqrt 3 * Real.pi * firstIntegralCore| < (1 : ℝ) / 7000 := by
  have hrad : ∀ x : ℝ, 0 ≤ 3 + Real.cos x := by
    intro x
    linarith [Real.neg_one_le_cos x]
  have hf : IntervalIntegrable (fun x : ℝ => Real.sqrt (3 + Real.cos x))
      volume 0 Real.pi := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hg : IntervalIntegrable
      (fun x : ℝ => Real.sqrt 3 * sqrtCore6 (Real.cos x))
      volume 0 Real.pi := by
    apply Continuous.intervalIntegrable
    unfold sqrtCore6
    fun_prop
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun x : ℝ => Real.sqrt (3 + Real.cos x) -
      Real.sqrt 3 * sqrtCore6 (Real.cos x))
    (a := (0 : ℝ)) (b := Real.pi) (C := (1 : ℝ) / 30000) (by
      intro x hx
      rw [Real.norm_eq_abs]
      exact (sqrtCore6_error (Real.abs_cos_le_one x)).le)
  rw [intervalIntegral.integral_sub hf hg,
    intervalIntegral.integral_const_mul, integral_sqrtCore6_cos] at hnorm
  simp only [firstIntegral, Real.norm_eq_abs, sub_zero, abs_of_nonneg Real.pi_pos.le,
    mul_assoc] at hnorm
  have hpi : (1 : ℝ) / 30000 * Real.pi < 1 / 7000 := by
    nlinarith [Real.pi_lt_four]
  simpa only [firstIntegral, mul_assoc] using hnorm.trans_lt hpi

private def sinPoly11 (x : ℝ) : ℝ :=
  x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 +
    x ^ 9 / 362880 - x ^ 11 / 39916800

private def sincPoly10 (x : ℝ) : ℝ :=
  1 - x ^ 2 / 6 + x ^ 4 / 120 - x ^ 6 / 5040 +
    x ^ 8 / 362880 - x ^ 10 / 39916800

private theorem sinPoly11_eq (x : ℝ) :
    sinPoly11 x = x * sincPoly10 x := by
  unfold sinPoly11 sincPoly10
  ring

private def sincPolyLower (l u : ℝ) : ℝ :=
  1 - u ^ 2 / 6 + l ^ 4 / 120 - u ^ 6 / 5040 +
    l ^ 8 / 362880 - u ^ 10 / 39916800

private def sincPolyUpper (l u : ℝ) : ℝ :=
  1 - l ^ 2 / 6 + u ^ 4 / 120 - l ^ 6 / 5040 +
    u ^ 8 / 362880 - l ^ 10 / 39916800

private theorem sincPoly_interval_bounds {l x u : ℝ}
    (hl0 : 0 ≤ l) (hl : l ≤ x) (hu : x ≤ u) :
    sincPolyLower l u ≤ sincPoly10 x ∧
      sincPoly10 x ≤ sincPolyUpper l u := by
  have hx0 : 0 ≤ x := hl0.trans hl
  have h2l := pow_le_pow_left₀ hl0 hl 2
  have h4l := pow_le_pow_left₀ hl0 hl 4
  have h6l := pow_le_pow_left₀ hl0 hl 6
  have h8l := pow_le_pow_left₀ hl0 hl 8
  have h10l := pow_le_pow_left₀ hl0 hl 10
  have h2u := pow_le_pow_left₀ hx0 hu 2
  have h4u := pow_le_pow_left₀ hx0 hu 4
  have h6u := pow_le_pow_left₀ hx0 hu 6
  have h8u := pow_le_pow_left₀ hx0 hu 8
  have h10u := pow_le_pow_left₀ hx0 hu 10
  constructor
  · unfold sincPolyLower sincPoly10
    nlinarith
  · unfold sincPolyUpper sincPoly10
    nlinarith

private theorem sin_taylor_eval (x : ℝ) :
    taylorWithinEval Real.sin 12 (Set.Icc (0 : ℝ) 2) 0 x = sinPoly11 x := by
  have hiter (n : ℕ) :
      iteratedDerivWithin n Real.sin (Set.Icc (0 : ℝ) 2) 0 =
        iteratedDeriv n Real.sin 0 :=
    Real.iteratedDerivWithin_sin_Icc n (by norm_num) (by norm_num)
  norm_num [taylorWithinEval_succ, hiter, sinPoly11]
  ring

private theorem sin_poly_error {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 2) :
    |Real.sin x - sinPoly11 x| ≤ x ^ 13 / Nat.factorial 12 := by
  have h := taylor_mean_remainder_bound
    (f := Real.sin) (a := (0 : ℝ)) (b := 2) (C := 1) (x := x) (n := 12)
    (by norm_num) Real.contDiff_sin.contDiffOn hx (by
      intro y hy
      rw [Real.iteratedDerivWithin_sin_Icc 13 (by norm_num) hy]
      simpa [Real.norm_eq_abs] using Real.abs_iteratedDeriv_sin_le_one 13 y)
  rw [sin_taylor_eval] at h
  simpa [Real.norm_eq_abs] using h

private theorem sinc_abs_sub_lt_of_poly_bounds {x c e : ℝ}
    (hx0 : 0 < x) (hx2 : x ≤ 2)
    (hlo : c - e + x ^ 12 / Nat.factorial 12 < sincPoly10 x)
    (hhi : sincPoly10 x + x ^ 12 / Nat.factorial 12 < c + e) :
    |sinc x - c| < e := by
  have herr := sin_poly_error ⟨hx0.le, hx2⟩
  rw [sinPoly11_eq] at herr
  rcases abs_le.mp herr with ⟨herrlo, herrhi⟩
  have hlomul := mul_lt_mul_of_pos_right hlo hx0
  have hhimul := mul_lt_mul_of_pos_right hhi hx0
  have herrpow : x ^ 12 / Nat.factorial 12 * x =
      x ^ 13 / Nat.factorial 12 := by ring
  have hslo : (c - e) * x < Real.sin x := by nlinarith
  have hshi : Real.sin x < (c + e) * x := by nlinarith
  rw [sinc, if_neg hx0.ne', abs_lt]
  constructor
  · have hdiv : c - e < Real.sin x / x := by
      rw [lt_div_iff₀ hx0]
      exact hslo
    linarith
  · have hdiv : Real.sin x / x < c + e := by
      rw [div_lt_iff₀ hx0]
      exact hshi
    linarith

private theorem sinc_abs_sub_lt_of_interval {x l u c e : ℝ}
    (hx0 : 0 < x) (hx2 : x ≤ 2) (hl0 : 0 ≤ l)
    (hl : l ≤ x) (hu : x ≤ u)
    (hlo : c - e + u ^ 12 / Nat.factorial 12 < sincPolyLower l u)
    (hhi : sincPolyUpper l u + u ^ 12 / Nat.factorial 12 < c + e) :
    |sinc x - c| < e := by
  have hb := sincPoly_interval_bounds hl0 hl hu
  have h12 := pow_le_pow_left₀ hx0.le hu 12
  apply sinc_abs_sub_lt_of_poly_bounds hx0 hx2
  · calc
      c - e + x ^ 12 / Nat.factorial 12 ≤
          c - e + u ^ 12 / Nat.factorial 12 := by
        have herr : x ^ 12 / Nat.factorial 12 ≤ u ^ 12 / Nat.factorial 12 :=
          div_le_div_of_nonneg_right h12 (by positivity)
        linarith
      _ < sincPolyLower l u := hlo
      _ ≤ sincPoly10 x := hb.1
  · calc
      sincPoly10 x + x ^ 12 / Nat.factorial 12 ≤
          sincPolyUpper l u + u ^ 12 / Nat.factorial 12 := by
        have herr : x ^ 12 / Nat.factorial 12 ≤ u ^ 12 / Nat.factorial 12 :=
          div_le_div_of_nonneg_right h12 (by positivity)
        linarith [hb.2]
      _ < c + e := hhi

private def sincPrimitive11 (x : ℝ) : ℝ :=
  x - x ^ 3 / 18 + x ^ 5 / 600 - x ^ 7 / 35280 +
    x ^ 9 / 3265920 - x ^ 11 / 439084800

private theorem sincPrimitive11_hasDerivAt (x : ℝ) :
    HasDerivAt sincPrimitive11 (sincPoly10 x) x := by
  unfold sincPrimitive11 sincPoly10
  convert
    (((((hasDerivAt_id x).sub (((hasDerivAt_id x).pow 3).div_const 18)).add
      (((hasDerivAt_id x).pow 5).div_const 600)).sub
      (((hasDerivAt_id x).pow 7).div_const 35280)).add
      (((hasDerivAt_id x).pow 9).div_const 3265920)).sub
      (((hasDerivAt_id x).pow 11).div_const 439084800) using 1 <;>
    norm_num <;> ring

private theorem integral_sincPoly10 (b : ℝ) :
    (∫ x in (0 : ℝ)..b, sincPoly10 x) = sincPrimitive11 b := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := b) (f := sincPrimitive11) (f' := sincPoly10)
    (fun x hx => sincPrimitive11_hasDerivAt x)
    (by
      apply Continuous.intervalIntegrable
      unfold sincPoly10
      fun_prop)
  simpa [sincPrimitive11] using h

private theorem continuous_sinc : Continuous sinc := by
  have heq : sinc = Real.sinc := by
    funext x
    rfl
  rw [heq]
  exact Real.continuous_sinc

private theorem sinc_poly_error {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 2) :
    |sinc x - sincPoly10 x| ≤ x ^ 12 / Nat.factorial 12 := by
  by_cases hxzero : x = 0
  · subst x
    norm_num [sinc, sincPoly10]
  have hxpos : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hxzero)
  have h := sin_poly_error hx
  rw [sinPoly11_eq] at h
  rw [sinc, if_neg hxzero]
  have heq : Real.sin x / x - sincPoly10 x =
      (Real.sin x - x * sincPoly10 x) / x := by
    field_simp [hxzero]
  calc
    |Real.sin x / x - sincPoly10 x| =
        |Real.sin x - x * sincPoly10 x| / x := by
      rw [heq, abs_div, abs_of_pos hxpos]
    _ ≤ (x ^ 13 / Nat.factorial 12) / x := by
      exact div_le_div_of_nonneg_right h hxpos.le
    _ = x ^ 12 / Nat.factorial 12 := by
      field_simp [hxzero]

private theorem secondIntegral_poly_error :
    |secondIntegral - sincPrimitive11 (Real.pi / 2)| ≤
      (Real.pi / 2) ^ 13 / Nat.factorial 12 := by
  have hb0 : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  have hb2 : Real.pi / 2 ≤ 2 := by nlinarith [Real.pi_lt_four]
  have hsinc : IntervalIntegrable sinc volume 0 (Real.pi / 2) :=
    continuous_sinc.intervalIntegrable _ _
  have hpoly : IntervalIntegrable sincPoly10 volume 0 (Real.pi / 2) := by
    apply Continuous.intervalIntegrable
    unfold sincPoly10
    fun_prop
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun x : ℝ => sinc x - sincPoly10 x)
    (a := (0 : ℝ)) (b := Real.pi / 2)
    (C := (Real.pi / 2) ^ 12 / Nat.factorial 12) (by
      intro x hx
      rw [Set.uIoc_of_le hb0] at hx
      rw [Real.norm_eq_abs]
      calc
        |sinc x - sincPoly10 x| ≤ x ^ 12 / Nat.factorial 12 :=
          sinc_poly_error ⟨hx.1.le, hx.2.trans hb2⟩
        _ ≤ (Real.pi / 2) ^ 12 / Nat.factorial 12 := by
          have hpow := pow_le_pow_left₀ hx.1.le hx.2 12
          exact div_le_div_of_nonneg_right hpow (by positivity))
  rw [intervalIntegral.integral_sub hsinc hpoly] at hnorm
  rw [integral_sincPoly10] at hnorm
  simp only [secondIntegral, Real.norm_eq_abs, sub_zero, abs_of_nonneg hb0] at hnorm
  convert hnorm using 1 <;> ring

private def sincPrimitiveLower (l u : ℝ) : ℝ :=
  l - u ^ 3 / 18 + l ^ 5 / 600 - u ^ 7 / 35280 +
    l ^ 9 / 3265920 - u ^ 11 / 439084800

private def sincPrimitiveUpper (l u : ℝ) : ℝ :=
  u - l ^ 3 / 18 + u ^ 5 / 600 - l ^ 7 / 35280 +
    u ^ 9 / 3265920 - l ^ 11 / 439084800

private theorem sincPrimitive_interval_bounds {l x u : ℝ}
    (hl0 : 0 ≤ l) (hl : l ≤ x) (hu : x ≤ u) :
    sincPrimitiveLower l u ≤ sincPrimitive11 x ∧
      sincPrimitive11 x ≤ sincPrimitiveUpper l u := by
  have hx0 : 0 ≤ x := hl0.trans hl
  have h3l := pow_le_pow_left₀ hl0 hl 3
  have h5l := pow_le_pow_left₀ hl0 hl 5
  have h7l := pow_le_pow_left₀ hl0 hl 7
  have h9l := pow_le_pow_left₀ hl0 hl 9
  have h11l := pow_le_pow_left₀ hl0 hl 11
  have h3u := pow_le_pow_left₀ hx0 hu 3
  have h5u := pow_le_pow_left₀ hx0 hu 5
  have h7u := pow_le_pow_left₀ hx0 hu 7
  have h9u := pow_le_pow_left₀ hx0 hu 9
  have h11u := pow_le_pow_left₀ hx0 hu 11
  constructor
  · unfold sincPrimitiveLower sincPrimitive11
    nlinarith
  · unfold sincPrimitiveUpper sincPrimitive11
    nlinarith

private def logSeriesT (x : ℝ) : ℝ := x / (x + 2)

private def logHalfSum (x : ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n,
    logSeriesT x ^ (2 * i + 1) / (2 * i + 1)

private def logHalfUpper (x : ℝ) (n : ℕ) : ℝ :=
  logHalfSum x n +
    logSeriesT x ^ (2 * n + 1) / (1 - logSeriesT x ^ 2)

private theorem log_one_add_bounds {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    2 * logHalfSum x n ≤ Real.log (1 + x) ∧
      Real.log (1 + x) ≤ 2 * logHalfUpper x n := by
  have hden : 0 < x + 2 := by linarith
  have ht0 : 0 ≤ logSeriesT x := by
    unfold logSeriesT
    positivity
  have ht1 : logSeriesT x < 1 := by
    unfold logSeriesT
    rw [div_lt_one hden]
    linarith
  have hratio : (1 + logSeriesT x) / (1 - logSeriesT x) = 1 + x := by
    unfold logSeriesT
    field_simp
    ring
  have hlo := Real.sum_range_le_log_div ht0 ht1 n
  have hhi := Real.log_div_le_sum_range_add ht0 ht1 n
  rw [hratio] at hlo hhi
  constructor
  · unfold logHalfSum
    nlinarith
  · unfold logHalfUpper logHalfSum
    nlinarith

private theorem logRatio_abs_sub_lt_of_bounds {x c e L U : ℝ}
    (hx : 0 < x) (he : 0 ≤ e) (hc : 0 ≤ c - e)
    (hLpos : 0 < L) (hL : L ≤ Real.log (1 + x))
    (hU : Real.log (1 + x) ≤ U)
    (hnumlo : (c - e) * U < x) (hnumhi : x < (c + e) * L) :
    |logRatio x - c| < e := by
  have hlogpos : 0 < Real.log (1 + x) := hLpos.trans_le hL
  have hcpe : 0 ≤ c + e := by linarith
  rw [logRatio, if_neg hx.ne', abs_lt]
  constructor
  · have hmul : (c - e) * Real.log (1 + x) ≤ (c - e) * U :=
      mul_le_mul_of_nonneg_left hU hc
    have hratio : c - e < x / Real.log (1 + x) := by
      rw [lt_div_iff₀ hlogpos]
      linarith
    linarith
  · have hmul : (c + e) * L ≤ (c + e) * Real.log (1 + x) :=
      mul_le_mul_of_nonneg_left hL hcpe
    have hratio : x / Real.log (1 + x) < c + e := by
      rw [div_lt_iff₀ hlogpos]
      linarith
    linarith

private def logMean (x : ℝ) : ℝ :=
  ∫ t in Set.Ioc (0 : ℝ) 1, (1 + x) ^ t

private theorem logMean_concave :
    ConcaveOn ℝ (Set.Ioi (-1)) logMean := by
  unfold logMean
  apply integral_concaveOn_of_integrand_ae (convex_Ioi (-1))
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    refine ⟨convex_Ioi (-1), ?_⟩
    intro x hx y hy a b ha hb hab
    have hx' : (-1 : ℝ) < x := hx
    have hy' : (-1 : ℝ) < y := hy
    have hpow := (Real.concaveOn_rpow ht.1.le ht.2).2
      (show 1 + x ∈ Set.Ici (0 : ℝ) by exact Set.mem_Ici.mpr (by linarith))
      (show 1 + y ∈ Set.Ici (0 : ℝ) by exact Set.mem_Ici.mpr (by linarith))
      ha hb hab
    have hbase : a * (1 + x) + b * (1 + y) = 1 + (a * x + b * y) := by
      nlinarith
    simp only [smul_eq_mul] at hpow
    rw [hbase] at hpow
    simpa only [smul_eq_mul] using hpow
  · intro x hx
    have hx' : (-1 : ℝ) < x := hx
    have hbase : 0 < 1 + x := by linarith
    exact (Real.continuous_const_rpow hbase.ne').integrableOn_Ioc

private theorem continuousOn_logMean :
    ContinuousOn logMean (Set.Ioi (-1)) :=
  logMean_concave.continuousOn isOpen_Ioi

private theorem logMean_eq_logRatio {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    logMean x = logRatio x := by
  by_cases hzero : x = 0
  · subst x
    simp [logMean, logRatio]
  · have hxpos : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hzero)
    have hbase : 0 < 1 + x := by linarith
    have hlog : Real.log (1 + x) ≠ 0 := (Real.log_pos (by linarith)).ne'
    have hderiv (t : ℝ) (_ht : t ∈ Set.uIcc (0 : ℝ) 1) :
        HasDerivAt (fun s : ℝ => (1 + x) ^ s / Real.log (1 + x))
          ((1 + x) ^ t) t := by
      convert (Real.hasStrictDerivAt_const_rpow hbase t).hasDerivAt.div_const
        (Real.log (1 + x)) using 1 <;> field_simp
    have hint : IntervalIntegrable (fun t : ℝ => (1 + x) ^ t) volume 0 1 :=
      (Real.continuous_const_rpow hbase.ne').intervalIntegrable 0 1
    rw [logRatio, if_neg hzero]
    unfold logMean
    rw [← intervalIntegral.integral_of_le (by norm_num)]
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
    simp only [Real.rpow_one, Real.rpow_zero]
    field_simp
    ring

private theorem concave_unit_integral_bounds {f : ℝ → ℝ}
    (hf : ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) f)
    (hint : IntervalIntegrable f volume 0 1) :
    (f 0 + f 1) / 2 ≤ (∫ t in (0 : ℝ)..1, f t) ∧
      (∫ t in (0 : ℝ)..1, f t) ≤ f (1 / 2) := by
  constructor
  · let chord : ℝ → ℝ := fun t => (1 - t) * f 0 + t * f 1
    have hchord : IntervalIntegrable chord volume 0 1 := by
      apply Continuous.intervalIntegrable
      unfold chord
      fun_prop
    have hmono := intervalIntegral.integral_mono_on
      (μ := volume) (by norm_num : (0 : ℝ) ≤ 1) hchord hint (by
        intro t ht
        have hc := hf.2 (show (0 : ℝ) ∈ Set.Icc 0 1 by norm_num)
          (show (1 : ℝ) ∈ Set.Icc 0 1 by norm_num)
          (sub_nonneg.mpr ht.2) ht.1 (by ring)
        simpa only [chord, smul_eq_mul, zero_mul, mul_zero, mul_one, add_zero, zero_add]
          using hc)
    have hchordValue : (∫ t in (0 : ℝ)..1, chord t) = (f 0 + f 1) / 2 := by
      have hconst : IntervalIntegrable (fun _ : ℝ => f 0) volume 0 1 :=
        continuous_const.intervalIntegrable 0 1
      have hlinear : IntervalIntegrable (fun t : ℝ => t * (f 1 - f 0)) volume 0 1 :=
        (continuous_id.mul continuous_const).intervalIntegrable 0 1
      rw [show chord = fun t : ℝ => f 0 + t * (f 1 - f 0) by
        funext t
        unfold chord
        ring]
      rw [intervalIntegral.integral_add hconst hlinear,
        intervalIntegral.integral_mul_const, intervalIntegral.integral_const,
        integral_id]
      norm_num
      ring
    rwa [hchordValue] at hmono
  · let paired : ℝ → ℝ := fun t => (f t + f (1 - t)) / 2
    have hmirror : IntervalIntegrable (fun t : ℝ => f (1 - t)) volume 0 1 := by
      simpa using (hint.comp_sub_left 1).symm
    have hpaired : IntervalIntegrable paired volume 0 1 := by
      exact (hint.add hmirror).div_const 2
    have hconst : IntervalIntegrable (fun _ : ℝ => f (1 / 2)) volume 0 1 :=
      continuous_const.intervalIntegrable 0 1
    have hmono := intervalIntegral.integral_mono_on
      (μ := volume) (by norm_num : (0 : ℝ) ≤ 1) hpaired hconst (by
        intro t ht
        have hmirror_mem : 1 - t ∈ Set.Icc (0 : ℝ) 1 := by
          constructor <;> linarith [ht.1, ht.2]
        have hc := hf.2 ht hmirror_mem
          (show (0 : ℝ) ≤ 1 / 2 by norm_num)
          (show (0 : ℝ) ≤ 1 / 2 by norm_num)
          (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
        unfold paired
        convert hc using 1 <;> simp only [smul_eq_mul] <;> ring)
    have hpairedValue : (∫ t in (0 : ℝ)..1, paired t) =
        (∫ t in (0 : ℝ)..1, f t) := by
      unfold paired
      rw [intervalIntegral.integral_div,
        intervalIntegral.integral_add hint hmirror,
        intervalIntegral.integral_comp_sub_left]
      norm_num
    rw [hpairedValue] at hmono
    simpa using hmono

private theorem logMean_interval_integral_bounds {a b : ℝ}
    (ha : 0 ≤ a) (hab : a < b) :
    (b - a) * (logMean a + logMean b) / 2 ≤
        (∫ x in a..b, logMean x) ∧
      (∫ x in a..b, logMean x) ≤
        (b - a) * logMean ((a + b) / 2) := by
  let d : ℝ := b - a
  let g : ℝ → ℝ := fun t => logMean (d * t + a)
  have hd : 0 < d := by
    dsimp [d]
    exact sub_pos.mpr hab
  have hmap {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      a ≤ d * t + a ∧ d * t + a ≤ b := by
    rcases ht with ⟨ht0, ht1⟩
    constructor
    · nlinarith
    · dsimp [d] at *
      nlinarith
  have hgconc : ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) g := by
    refine ⟨convex_Icc 0 1, ?_⟩
    intro x hx y hy r s hr hs hrs
    have hxm := hmap hx
    have hym := hmap hy
    have hxdomain : d * x + a ∈ Set.Ioi (-1 : ℝ) := by
      change (-1 : ℝ) < d * x + a
      linarith [ha, hxm.1]
    have hydomain : d * y + a ∈ Set.Ioi (-1 : ℝ) := by
      change (-1 : ℝ) < d * y + a
      linarith [ha, hym.1]
    have hc := logMean_concave.2 hxdomain hydomain hr hs hrs
    have harg : r * (d * x + a) + s * (d * y + a) =
        d * (r * x + s * y) + a := by
      nlinarith
    unfold g
    simp only [smul_eq_mul] at hc ⊢
    rw [harg] at hc
    exact hc
  have hgcont : ContinuousOn g (Set.Icc (0 : ℝ) 1) := by
    unfold g
    apply continuousOn_logMean.comp'
    · fun_prop
    · intro t ht
      have htm := hmap ht
      change (-1 : ℝ) < d * t + a
      linarith [ha, htm.1]
  have hgint : IntervalIntegrable g volume 0 1 :=
    hgcont.intervalIntegrable_of_Icc (by norm_num)
  have hunit := concave_unit_integral_bounds hgconc hgint
  have hscale : (∫ t in (0 : ℝ)..1, g t) =
      (∫ x in a..b, logMean x) / d := by
    unfold g
    rw [intervalIntegral.integral_comp_mul_add logMean hd.ne' a]
    simp only [zero_mul, zero_add, mul_one, smul_eq_mul]
    rw [show d + a = b by dsimp [d]; ring]
    ring
  rw [hscale] at hunit
  have hg0 : g 0 = logMean a := by simp [g]
  have hg1 : g 1 = logMean b := by
    simp only [g, mul_one]
    rw [show d + a = b by dsimp [d]; ring]
  have hghalf : g (1 / 2) = logMean ((a + b) / 2) := by
    unfold g
    congr 1
    dsimp [d]
    ring
  rw [hg0, hg1, hghalf] at hunit
  constructor
  · have := (le_div_iff₀ hd).mp hunit.1
    nlinarith
  · have := (div_le_iff₀ hd).mp hunit.2
    nlinarith

theorem gap1 : firstMesh 0 = 0 := by norm_num [firstMesh]
theorem gap2 : firstSample 0 = 2 := by
  unfold firstSample
  rw [gap1, Real.cos_zero]
  rw [show (3 : ℝ) + 1 = 2 ^ 2 by norm_num, Real.sqrt_sq_eq_abs]
  norm_num
theorem gap3 : firstMesh 1 = Real.pi / 6 := by norm_num [firstMesh]
theorem gap4 : firstSample 1 = Real.sqrt (3 + Real.cos (Real.pi / 6)) := by
  unfold firstSample
  rw [gap3]
theorem gap5 :
    firstSample 1 = Real.sqrt (3 + Real.sqrt 3 / 2) := by
  rw [gap4, Real.cos_pi_div_six]
theorem gap6 : |firstSample 1 - 1.966| < 0.001 := by
  rw [gap5]
  apply abs_sqrt_sub_lt
  · norm_num
  · norm_num
  · positivity
  · nlinarith [sqrt_three_bounds.1]
  · nlinarith [sqrt_three_bounds.2]
theorem gap7 : firstMesh 2 = Real.pi / 3 := by norm_num [firstMesh] <;> ring
theorem gap8 : firstSample 2 = Real.sqrt (3 + Real.cos (Real.pi / 3)) := by
  unfold firstSample
  rw [gap7]
theorem gap9 : firstSample 2 = Real.sqrt 3.5 := by
  rw [gap8, Real.cos_pi_div_three]
  norm_num
theorem gap10 : |firstSample 2 - 1.871| < 0.001 := by
  rw [gap9]
  apply abs_sqrt_sub_lt <;> norm_num
theorem gap11 : firstMesh 3 = Real.pi / 2 := by norm_num [firstMesh] <;> ring
theorem gap12 : firstSample 3 = Real.sqrt (3 + Real.cos (Real.pi / 2)) := by
  unfold firstSample
  rw [gap11]
theorem gap13 : firstSample 3 = Real.sqrt 3 := by
  rw [gap12, Real.cos_pi_div_two]
  norm_num
theorem gap14 : |firstSample 3 - 1.732| < 0.001 := by
  rw [gap13]
  apply abs_sqrt_sub_lt <;> norm_num
theorem gap15 : firstMesh 4 = 2 * Real.pi / 3 := by norm_num [firstMesh] <;> ring
theorem gap16 : firstSample 4 = Real.sqrt (3 + Real.cos (2 * Real.pi / 3)) := by
  unfold firstSample
  rw [gap15]
theorem gap17 : firstSample 4 = Real.sqrt 2.5 := by
  rw [gap16, show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring,
    Real.cos_pi_sub, Real.cos_pi_div_three]
  norm_num
theorem gap18 : |firstSample 4 - 1.581| < 0.001 := by
  rw [gap17]
  apply abs_sqrt_sub_lt <;> norm_num
theorem gap19 : firstMesh 5 = 5 * Real.pi / 6 := by norm_num [firstMesh] <;> ring
theorem gap20 : firstSample 5 = Real.sqrt (3 + Real.cos (5 * Real.pi / 6)) := by
  unfold firstSample
  rw [gap19]
theorem gap21 : firstSample 5 = Real.sqrt (3 - Real.sqrt 3 / 2) := by
  rw [gap20, show 5 * Real.pi / 6 = Real.pi - Real.pi / 6 by ring,
    Real.cos_pi_sub, Real.cos_pi_div_six]
  congr 1
theorem gap22 : |firstSample 5 - 1.461| < 0.001 := by
  rw [gap21]
  apply abs_sqrt_sub_lt
  · norm_num
  · norm_num
  · nlinarith [sqrt_three_bounds.2]
  · nlinarith [sqrt_three_bounds.2]
  · nlinarith [sqrt_three_bounds.1]
theorem gap23 : firstMesh 6 = Real.pi := by norm_num [firstMesh] <;> ring
theorem gap24 : firstSample 6 = Real.sqrt (3 + Real.cos Real.pi) := by
  unfold firstSample
  rw [gap23]
theorem gap25 : firstSample 6 = Real.sqrt 2 := by
  rw [gap24, Real.cos_pi]
  norm_num
theorem gap26 : |firstSample 6 - 1.414| < 0.001 := by
  rw [gap25]
  apply abs_sqrt_sub_lt <;> norm_num

theorem gap27 :
    firstRoundedSimpson =
      Real.pi / 18 *
        (2 + 1.414 + 4 * (1.966 + 1.732 + 1.461) +
          2 * (1.871 + 1.581)) := by rfl
theorem gap28 : |firstRoundedSimpson - 5.4025| < 0.001 := by
  rw [abs_lt]
  constructor <;> norm_num [firstRoundedSimpson] <;>
    nlinarith [Real.pi_gt_d20, Real.pi_lt_d20]
theorem gap29 : |firstIntegral - 5.4025| < 0.001 := by
  have hcore : 0 < firstIntegralCore := by
    norm_num [firstIntegralCore]
  have happroxLo :
      (1.73205 : ℝ) * 3.141592 * firstIntegralCore <
        Real.sqrt 3 * Real.pi * firstIntegralCore := by
    have hsp : (1.73205 : ℝ) * 3.141592 < Real.sqrt 3 * Real.pi := by
      calc
        (1.73205 : ℝ) * 3.141592 < Real.sqrt 3 * 3.141592 := by
          exact mul_lt_mul_of_pos_right sqrt_three_bounds.1 (by norm_num)
        _ < Real.sqrt 3 * Real.pi := by
          exact mul_lt_mul_of_pos_left Real.pi_gt_d6 (Real.sqrt_pos.2 (by norm_num))
    exact mul_lt_mul_of_pos_right hsp hcore
  have happroxHi :
      Real.sqrt 3 * Real.pi * firstIntegralCore <
        (1.73206 : ℝ) * 3.141593 * firstIntegralCore := by
    have hsp : Real.sqrt 3 * Real.pi < (1.73206 : ℝ) * 3.141593 := by
      calc
        Real.sqrt 3 * Real.pi < (1.73206 : ℝ) * Real.pi := by
          exact mul_lt_mul_of_pos_right sqrt_three_bounds.2 Real.pi_pos
        _ < (1.73206 : ℝ) * 3.141593 := by
          exact mul_lt_mul_of_pos_left Real.pi_lt_d6 (by norm_num)
    exact mul_lt_mul_of_pos_right hsp hcore
  have hnumLo : (5.4025 : ℝ) - 0.0008 <
      (1.73205 : ℝ) * 3.141592 * firstIntegralCore := by
    norm_num [firstIntegralCore]
  have hnumHi : (1.73206 : ℝ) * 3.141593 * firstIntegralCore <
      (5.4025 : ℝ) + 0.0008 := by
    norm_num [firstIntegralCore]
  have happLo : (5.4025 : ℝ) - 0.0008 <
      Real.sqrt 3 * Real.pi * firstIntegralCore := hnumLo.trans happroxLo
  have happHi : Real.sqrt 3 * Real.pi * firstIntegralCore <
      (5.4025 : ℝ) + 0.0008 := happroxHi.trans hnumHi
  have herr := firstIntegral_poly_error
  rw [abs_lt] at herr ⊢
  constructor <;> nlinarith

theorem gap30 : secondMesh 0 = 0 := by norm_num [secondMesh]
theorem gap31 : secondSample 0 = 1 := by norm_num [secondSample, secondMesh, sinc]
theorem gap32 : secondMesh 1 = Real.pi / 20 := by norm_num [secondMesh]
theorem gap33 : secondSample 1 = 20 / Real.pi * Real.sin (Real.pi / 20) := by
  rw [secondSample, gap32, sinc, if_neg (div_ne_zero Real.pi_ne_zero (by norm_num))]
  field_simp [Real.pi_ne_zero]
theorem gap34 : |secondSample 1 - 0.99589| < 0.00001 := by
  rw [secondSample, gap32]
  apply sinc_abs_sub_lt_of_interval (l := (3.141592 : ℝ) / 20)
    (u := (3.141593 : ℝ) / 20)
  · positivity
  · nlinarith [Real.pi_lt_d20]
  · norm_num
  · nlinarith [Real.pi_gt_d6]
  · nlinarith [Real.pi_lt_d6]
  · norm_num [sincPolyLower, Nat.factorial]
  · norm_num [sincPolyUpper, Nat.factorial]
theorem gap35 : secondMesh 2 = Real.pi / 10 := by norm_num [secondMesh] <;> ring
theorem gap36 : secondSample 2 = 10 / Real.pi * Real.sin (Real.pi / 10) := by
  rw [secondSample, gap35, sinc, if_neg (div_ne_zero Real.pi_ne_zero (by norm_num))]
  field_simp [Real.pi_ne_zero]
theorem gap37 : |secondSample 2 - 0.98363| < 0.00001 := by
  rw [secondSample, gap35]
  apply sinc_abs_sub_lt_of_interval (l := 2 * (3.141592 : ℝ) / 20)
    (u := 2 * (3.141593 : ℝ) / 20)
  · positivity
  · nlinarith [Real.pi_lt_four]
  · norm_num
  · nlinarith [Real.pi_gt_d6]
  · nlinarith [Real.pi_lt_d6]
  · norm_num [sincPolyLower, Nat.factorial]
  · norm_num [sincPolyUpper, Nat.factorial]
theorem gap38 : secondMesh 3 = 3 * Real.pi / 20 := by norm_num [secondMesh] <;> ring
theorem gap39 : secondSample 3 = 20 / (3 * Real.pi) * Real.sin (3 * Real.pi / 20) := by
  rw [secondSample, gap38, sinc,
    if_neg (div_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) (by norm_num))]
  field_simp [Real.pi_ne_zero]
theorem gap40 : |secondSample 3 - 0.96340| < 0.00001 := by
  rw [secondSample, gap38]
  apply sinc_abs_sub_lt_of_interval (l := 3 * (3.141592 : ℝ) / 20)
    (u := 3 * (3.141593 : ℝ) / 20)
  · positivity
  · nlinarith [Real.pi_lt_four]
  · norm_num
  · nlinarith [Real.pi_gt_d6]
  · nlinarith [Real.pi_lt_d6]
  · norm_num [sincPolyLower, Nat.factorial]
  · norm_num [sincPolyUpper, Nat.factorial]
theorem gap41 : secondMesh 4 = Real.pi / 5 := by norm_num [secondMesh] <;> ring
theorem gap42 : secondSample 4 = 5 / Real.pi * Real.sin (Real.pi / 5) := by
  rw [secondSample, gap41, sinc, if_neg (div_ne_zero Real.pi_ne_zero (by norm_num))]
  field_simp [Real.pi_ne_zero]
theorem gap43 : |secondSample 4 - 0.93549| < 0.00001 := by
  rw [secondSample, gap41]
  apply sinc_abs_sub_lt_of_interval (l := 4 * (3.141592 : ℝ) / 20)
    (u := 4 * (3.141593 : ℝ) / 20)
  · positivity
  · nlinarith [Real.pi_lt_four]
  · norm_num
  · nlinarith [Real.pi_gt_d6]
  · nlinarith [Real.pi_lt_d6]
  · norm_num [sincPolyLower, Nat.factorial]
  · norm_num [sincPolyUpper, Nat.factorial]
theorem gap44 : secondMesh 5 = Real.pi / 4 := by norm_num [secondMesh] <;> ring
theorem gap45 : secondSample 5 = 4 / Real.pi * Real.sin (Real.pi / 4) := by
  rw [secondSample, gap44, sinc, if_neg (div_ne_zero Real.pi_ne_zero (by norm_num))]
  field_simp [Real.pi_ne_zero]
theorem gap46 : |secondSample 5 - 0.90032| < 0.00001 := by
  rw [secondSample, gap44]
  apply sinc_abs_sub_lt_of_interval (l := 5 * (3.141592 : ℝ) / 20)
    (u := 5 * (3.141593 : ℝ) / 20)
  · positivity
  · nlinarith [Real.pi_lt_four]
  · norm_num
  · nlinarith [Real.pi_gt_d6]
  · nlinarith [Real.pi_lt_d6]
  · norm_num [sincPolyLower, Nat.factorial]
  · norm_num [sincPolyUpper, Nat.factorial]
theorem gap47 : secondMesh 6 = 3 * Real.pi / 10 := by norm_num [secondMesh] <;> ring
theorem gap48 : secondSample 6 = 10 / (3 * Real.pi) * Real.sin (3 * Real.pi / 10) := by
  rw [secondSample, gap47, sinc,
    if_neg (div_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) (by norm_num))]
  field_simp [Real.pi_ne_zero]
theorem gap49 : |secondSample 6 - 0.85839| < 0.00001 := by
  rw [secondSample, gap47]
  apply sinc_abs_sub_lt_of_interval (l := 6 * (3.141592 : ℝ) / 20)
    (u := 6 * (3.141593 : ℝ) / 20)
  · positivity
  · nlinarith [Real.pi_lt_four]
  · norm_num
  · nlinarith [Real.pi_gt_d6]
  · nlinarith [Real.pi_lt_d6]
  · norm_num [sincPolyLower, Nat.factorial]
  · norm_num [sincPolyUpper, Nat.factorial]
theorem gap50 : secondMesh 7 = 7 * Real.pi / 20 := by norm_num [secondMesh] <;> ring
theorem gap51 : secondSample 7 = 20 / (7 * Real.pi) * Real.sin (7 * Real.pi / 20) := by
  rw [secondSample, gap50, sinc,
    if_neg (div_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) (by norm_num))]
  field_simp [Real.pi_ne_zero]
theorem gap52 : |secondSample 7 - 0.81033| < 0.00001 := by
  rw [secondSample, gap50]
  apply sinc_abs_sub_lt_of_interval (l := 7 * (3.141592 : ℝ) / 20)
    (u := 7 * (3.141593 : ℝ) / 20)
  · positivity
  · nlinarith [Real.pi_lt_four]
  · norm_num
  · nlinarith [Real.pi_gt_d6]
  · nlinarith [Real.pi_lt_d6]
  · norm_num [sincPolyLower, Nat.factorial]
  · norm_num [sincPolyUpper, Nat.factorial]
theorem gap53 : secondMesh 8 = 2 * Real.pi / 5 := by norm_num [secondMesh] <;> ring
theorem gap54 : secondSample 8 = 5 / (2 * Real.pi) * Real.sin (2 * Real.pi / 5) := by
  rw [secondSample, gap53, sinc,
    if_neg (div_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) (by norm_num))]
  field_simp [Real.pi_ne_zero]
theorem gap55 : |secondSample 8 - 0.75683| < 0.00001 := by
  rw [secondSample, gap53]
  apply sinc_abs_sub_lt_of_interval (l := 8 * (3.141592 : ℝ) / 20)
    (u := 8 * (3.141593 : ℝ) / 20)
  · positivity
  · nlinarith [Real.pi_lt_four]
  · norm_num
  · nlinarith [Real.pi_gt_d6]
  · nlinarith [Real.pi_lt_d6]
  · norm_num [sincPolyLower, Nat.factorial]
  · norm_num [sincPolyUpper, Nat.factorial]
theorem gap56 : secondMesh 9 = 9 * Real.pi / 20 := by norm_num [secondMesh] <;> ring
theorem gap57 : secondSample 9 = 20 / (9 * Real.pi) * Real.sin (9 * Real.pi / 20) := by
  rw [secondSample, gap56, sinc,
    if_neg (div_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) (by norm_num))]
  field_simp [Real.pi_ne_zero]
theorem gap58 : |secondSample 9 - 0.69865| < 0.00001 := by
  rw [secondSample, gap56]
  apply sinc_abs_sub_lt_of_interval (l := 9 * (3.141592 : ℝ) / 20)
    (u := 9 * (3.141593 : ℝ) / 20)
  · positivity
  · nlinarith [Real.pi_lt_four]
  · norm_num
  · nlinarith [Real.pi_gt_d6]
  · nlinarith [Real.pi_lt_d6]
  · norm_num [sincPolyLower, Nat.factorial]
  · norm_num [sincPolyUpper, Nat.factorial]
theorem gap59 : secondMesh 10 = Real.pi / 2 := by norm_num [secondMesh] <;> ring
theorem gap60 : secondSample 10 = 2 / Real.pi := by
  rw [secondSample, gap59, sinc, if_neg (div_ne_zero Real.pi_ne_zero (by norm_num)),
    Real.sin_pi_div_two]
  field_simp [Real.pi_ne_zero]
theorem gap61 : |2 / Real.pi - 0.63662| < 0.00001 := by
  rw [abs_lt]
  constructor
  · have h : (0.63662 : ℝ) - 0.00001 < 2 / Real.pi := by
      rw [lt_div_iff₀ Real.pi_pos]
      nlinarith [Real.pi_lt_d20]
    linarith
  · have h : 2 / Real.pi < (0.63662 : ℝ) + 0.00001 := by
      rw [div_lt_iff₀ Real.pi_pos]
      nlinarith [Real.pi_gt_d20]
    linarith

theorem gap62 :
    secondRoundedSimpson =
      Real.pi / 60 *
        (1 + 0.63662 +
          4 * (0.99589 + 0.96340 + 0.90032 + 0.81033 + 0.69865) +
          2 * (0.98363 + 0.93549 + 0.85839 + 0.75683)) := by rfl
theorem gap63 : |secondRoundedSimpson - 1.37076| < 0.00001 := by
  rw [abs_lt]
  constructor <;> norm_num [secondRoundedSimpson] <;>
    nlinarith [Real.pi_gt_d20, Real.pi_lt_d20]
theorem gap64 : |secondIntegral - 1.37076| < 0.0001 := by
  let l : ℝ := 3.141592 / 2
  let u : ℝ := 3.141593 / 2
  have hl0 : 0 ≤ l := by norm_num [l]
  have hl : l ≤ Real.pi / 2 := by
    dsimp [l]
    nlinarith [Real.pi_gt_d6]
  have hu : Real.pi / 2 ≤ u := by
    dsimp [u]
    nlinarith [Real.pi_lt_d6]
  have hb := sincPrimitive_interval_bounds hl0 hl hu
  have herr := secondIntegral_poly_error
  rcases abs_le.mp herr with ⟨herrlo, herrhi⟩
  have h13 := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ Real.pi / 2) hu 13
  have herrBound : (Real.pi / 2) ^ 13 / Nat.factorial 12 ≤
      u ^ 13 / Nat.factorial 12 := by
    exact div_le_div_of_nonneg_right h13 (by positivity)
  have hlo : (1.37076 : ℝ) - 0.0001 + u ^ 13 / Nat.factorial 12 <
      sincPrimitiveLower l u := by
    norm_num [l, u, sincPrimitiveLower, Nat.factorial]
  have hhi : sincPrimitiveUpper l u + u ^ 13 / Nat.factorial 12 <
      (1.37076 : ℝ) + 0.0001 := by
    norm_num [l, u, sincPrimitiveUpper, Nat.factorial]
  rw [abs_lt]
  constructor <;> nlinarith

theorem gap65 : thirdMesh 0 = 0 := by norm_num [thirdMesh]
theorem gap66 : thirdSample 0 = 1 := by norm_num [thirdSample, thirdMesh, logRatio]
theorem gap67 :
    Filter.Tendsto (fun x : ℝ => x / Real.log (1 + x))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
  have h : Filter.Tendsto (fun x : ℝ => Real.log (1 + x) / x)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    simpa [div_eq_mul_inv, mul_comm] using
      (Real.hasDerivAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto_slope_zero_right
  simpa only [inv_div, inv_one] using h.inv₀ one_ne_zero
theorem gap68 : thirdMesh 1 = 1 / 6 := by norm_num [thirdMesh]
theorem gap69 : |thirdSample 1 - 1.0812| < 0.0001 := by
  rw [thirdSample, gap68]
  have hb := log_one_add_bounds (x := (1 : ℝ) / 6) (by norm_num) 5
  apply logRatio_abs_sub_lt_of_bounds
    (L := 2 * logHalfSum ((1 : ℝ) / 6) 5)
    (U := 2 * logHalfUpper ((1 : ℝ) / 6) 5)
  · norm_num
  · norm_num
  · norm_num
  · norm_num [logHalfSum, logSeriesT]
  · exact hb.1
  · exact hb.2
  · norm_num [logHalfUpper, logHalfSum, logSeriesT]
  · norm_num [logHalfUpper, logHalfSum, logSeriesT]
theorem gap70 : thirdMesh 2 = 1 / 3 := by norm_num [thirdMesh]
theorem gap71 : |thirdSample 2 - 1.1587| < 0.0001 := by
  rw [thirdSample, gap70]
  have hb := log_one_add_bounds (x := (1 : ℝ) / 3) (by norm_num) 5
  apply logRatio_abs_sub_lt_of_bounds
    (L := 2 * logHalfSum ((1 : ℝ) / 3) 5)
    (U := 2 * logHalfUpper ((1 : ℝ) / 3) 5)
  · norm_num
  · norm_num
  · norm_num
  · norm_num [logHalfSum, logSeriesT]
  · exact hb.1
  · exact hb.2
  · norm_num [logHalfUpper, logHalfSum, logSeriesT]
  · norm_num [logHalfUpper, logHalfSum, logSeriesT]
theorem gap72 : thirdMesh 3 = 1 / 2 := by norm_num [thirdMesh]
theorem gap73 : |thirdSample 3 - 1.2332| < 0.0001 := by
  rw [thirdSample, gap72]
  have hb := log_one_add_bounds (x := (1 : ℝ) / 2) (by norm_num) 5
  apply logRatio_abs_sub_lt_of_bounds
    (L := 2 * logHalfSum ((1 : ℝ) / 2) 5)
    (U := 2 * logHalfUpper ((1 : ℝ) / 2) 5)
  · norm_num
  · norm_num
  · norm_num
  · norm_num [logHalfSum, logSeriesT]
  · exact hb.1
  · exact hb.2
  · norm_num [logHalfUpper, logHalfSum, logSeriesT]
  · norm_num [logHalfUpper, logHalfSum, logSeriesT]
theorem gap74 : thirdMesh 4 = 2 / 3 := by norm_num [thirdMesh]
theorem gap75 : |thirdSample 4 - 1.3051| < 0.0001 := by
  rw [thirdSample, gap74]
  have hb := log_one_add_bounds (x := (2 : ℝ) / 3) (by norm_num) 5
  apply logRatio_abs_sub_lt_of_bounds
    (L := 2 * logHalfSum ((2 : ℝ) / 3) 5)
    (U := 2 * logHalfUpper ((2 : ℝ) / 3) 5)
  · norm_num
  · norm_num
  · norm_num
  · norm_num [logHalfSum, logSeriesT]
  · exact hb.1
  · exact hb.2
  · norm_num [logHalfUpper, logHalfSum, logSeriesT]
  · norm_num [logHalfUpper, logHalfSum, logSeriesT]
theorem gap76 : thirdMesh 5 = 5 / 6 := by norm_num [thirdMesh]
theorem gap77 : |thirdSample 5 - 1.3748| < 0.0001 := by
  rw [thirdSample, gap76]
  have hb := log_one_add_bounds (x := (5 : ℝ) / 6) (by norm_num) 5
  apply logRatio_abs_sub_lt_of_bounds
    (L := 2 * logHalfSum ((5 : ℝ) / 6) 5)
    (U := 2 * logHalfUpper ((5 : ℝ) / 6) 5)
  · norm_num
  · norm_num
  · norm_num
  · norm_num [logHalfSum, logSeriesT]
  · exact hb.1
  · exact hb.2
  · norm_num [logHalfUpper, logHalfSum, logSeriesT]
  · norm_num [logHalfUpper, logHalfSum, logSeriesT]
theorem gap78 : thirdMesh 6 = 1 := by norm_num [thirdMesh]
theorem gap79 : |thirdSample 6 - 1.4427| < 0.0001 := by
  rw [thirdSample, gap78]
  have hb := log_one_add_bounds (x := (1 : ℝ)) (by norm_num) 5
  apply logRatio_abs_sub_lt_of_bounds
    (L := 2 * logHalfSum (1 : ℝ) 5)
    (U := 2 * logHalfUpper (1 : ℝ) 5)
  · norm_num
  · norm_num
  · norm_num
  · norm_num [logHalfSum, logSeriesT]
  · exact hb.1
  · exact hb.2
  · norm_num [logHalfUpper, logHalfSum, logSeriesT]
  · norm_num [logHalfUpper, logHalfSum, logSeriesT]
theorem gap80 :
    thirdRoundedSimpson =
      1 / 18 * (1 + 1.4427 + 4 * (1.0812 + 1.2332 + 1.3748) +
        2 * (1.1587 + 1.3051)) := by rfl
theorem gap81 : |thirdRoundedSimpson - 1.2293| < 0.0001 := by
  norm_num [thirdRoundedSimpson, abs_lt]

private theorem logRatio_midpoint1 :
    |logRatio ((1 : ℝ) / 12) - 1.0411| < 0.0001 := by
  have hb := log_one_add_bounds (x := (1 : ℝ) / 12) (by norm_num) 5
  apply logRatio_abs_sub_lt_of_bounds
    (L := 2 * logHalfSum ((1 : ℝ) / 12) 5)
    (U := 2 * logHalfUpper ((1 : ℝ) / 12) 5)
  · norm_num
  · norm_num
  · norm_num
  · norm_num [logHalfSum, logSeriesT]
  · exact hb.1
  · exact hb.2
  · norm_num [logHalfUpper, logHalfSum, logSeriesT]
  · norm_num [logHalfUpper, logHalfSum, logSeriesT]

private theorem logRatio_midpoint2 :
    |logRatio ((1 : ℝ) / 4) - 1.1204| < 0.0001 := by
  have hb := log_one_add_bounds (x := (1 : ℝ) / 4) (by norm_num) 5
  apply logRatio_abs_sub_lt_of_bounds
    (L := 2 * logHalfSum ((1 : ℝ) / 4) 5)
    (U := 2 * logHalfUpper ((1 : ℝ) / 4) 5)
  · norm_num
  · norm_num
  · norm_num
  · norm_num [logHalfSum, logSeriesT]
  · exact hb.1
  · exact hb.2
  · norm_num [logHalfUpper, logHalfSum, logSeriesT]
  · norm_num [logHalfUpper, logHalfSum, logSeriesT]

private theorem logRatio_midpoint3 :
    |logRatio ((5 : ℝ) / 12) - 1.1963| < 0.0001 := by
  have hb := log_one_add_bounds (x := (5 : ℝ) / 12) (by norm_num) 5
  apply logRatio_abs_sub_lt_of_bounds
    (L := 2 * logHalfSum ((5 : ℝ) / 12) 5)
    (U := 2 * logHalfUpper ((5 : ℝ) / 12) 5)
  · norm_num
  · norm_num
  · norm_num
  · norm_num [logHalfSum, logSeriesT]
  · exact hb.1
  · exact hb.2
  · norm_num [logHalfUpper, logHalfSum, logSeriesT]
  · norm_num [logHalfUpper, logHalfSum, logSeriesT]

private theorem logRatio_midpoint4 :
    |logRatio ((7 : ℝ) / 12) - 1.2694| < 0.0001 := by
  have hb := log_one_add_bounds (x := (7 : ℝ) / 12) (by norm_num) 5
  apply logRatio_abs_sub_lt_of_bounds
    (L := 2 * logHalfSum ((7 : ℝ) / 12) 5)
    (U := 2 * logHalfUpper ((7 : ℝ) / 12) 5)
  · norm_num
  · norm_num
  · norm_num
  · norm_num [logHalfSum, logSeriesT]
  · exact hb.1
  · exact hb.2
  · norm_num [logHalfUpper, logHalfSum, logSeriesT]
  · norm_num [logHalfUpper, logHalfSum, logSeriesT]

private theorem logRatio_midpoint5 :
    |logRatio ((3 : ℝ) / 4) - 1.3402| < 0.0001 := by
  have hb := log_one_add_bounds (x := (3 : ℝ) / 4) (by norm_num) 5
  apply logRatio_abs_sub_lt_of_bounds
    (L := 2 * logHalfSum ((3 : ℝ) / 4) 5)
    (U := 2 * logHalfUpper ((3 : ℝ) / 4) 5)
  · norm_num
  · norm_num
  · norm_num
  · norm_num [logHalfSum, logSeriesT]
  · exact hb.1
  · exact hb.2
  · norm_num [logHalfUpper, logHalfSum, logSeriesT]
  · norm_num [logHalfUpper, logHalfSum, logSeriesT]

private theorem logRatio_midpoint6 :
    |logRatio ((11 : ℝ) / 12) - 1.4090| < 0.0001 := by
  have hb := log_one_add_bounds (x := (11 : ℝ) / 12) (by norm_num) 5
  apply logRatio_abs_sub_lt_of_bounds
    (L := 2 * logHalfSum ((11 : ℝ) / 12) 5)
    (U := 2 * logHalfUpper ((11 : ℝ) / 12) 5)
  · norm_num
  · norm_num
  · norm_num
  · norm_num [logHalfSum, logSeriesT]
  · exact hb.1
  · exact hb.2
  · norm_num [logHalfUpper, logHalfSum, logSeriesT]
  · norm_num [logHalfUpper, logHalfSum, logSeriesT]

theorem gap82 : |thirdIntegral - 1.2293| < 0.001 := by
  have hint {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
      IntervalIntegrable logMean volume a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc hab
    exact continuousOn_logMean.mono (by
      intro x hx
      change (-1 : ℝ) < x
      linarith [ha, hx.1])
  have hi0 := logMean_interval_integral_bounds
    (a := (0 : ℝ)) (b := 1 / 6) (by norm_num) (by norm_num)
  have hi1 := logMean_interval_integral_bounds
    (a := (1 : ℝ) / 6) (b := 1 / 3) (by norm_num) (by norm_num)
  have hi2 := logMean_interval_integral_bounds
    (a := (1 : ℝ) / 3) (b := 1 / 2) (by norm_num) (by norm_num)
  have hi3 := logMean_interval_integral_bounds
    (a := (1 : ℝ) / 2) (b := 2 / 3) (by norm_num) (by norm_num)
  have hi4 := logMean_interval_integral_bounds
    (a := (2 : ℝ) / 3) (b := 5 / 6) (by norm_num) (by norm_num)
  have hi5 := logMean_interval_integral_bounds
    (a := (5 : ℝ) / 6) (b := 1) (by norm_num) (by norm_num)
  have hint0 := hint (a := (0 : ℝ)) (b := 1 / 6) (by norm_num) (by norm_num)
  have hint1 := hint (a := (1 : ℝ) / 6) (b := 1 / 3) (by norm_num) (by norm_num)
  have hint2 := hint (a := (1 : ℝ) / 3) (b := 1 / 2) (by norm_num) (by norm_num)
  have hint3 := hint (a := (1 : ℝ) / 2) (b := 2 / 3) (by norm_num) (by norm_num)
  have hint4 := hint (a := (2 : ℝ) / 3) (b := 5 / 6) (by norm_num) (by norm_num)
  have hint5 := hint (a := (5 : ℝ) / 6) (b := 1) (by norm_num) (by norm_num)
  have hadd01 := intervalIntegral.integral_add_adjacent_intervals hint0 hint1
  have hint01 := hint0.trans hint1
  have hadd012 := intervalIntegral.integral_add_adjacent_intervals hint01 hint2
  have hint012 := hint01.trans hint2
  have hadd0123 := intervalIntegral.integral_add_adjacent_intervals hint012 hint3
  have hint0123 := hint012.trans hint3
  have hadd01234 := intervalIntegral.integral_add_adjacent_intervals hint0123 hint4
  have hint01234 := hint0123.trans hint4
  have hadd012345 := intervalIntegral.integral_add_adjacent_intervals hint01234 hint5
  have hsum :
      (((((∫ x in (0 : ℝ)..1 / 6, logMean x) +
          (∫ x in (1 : ℝ) / 6..1 / 3, logMean x)) +
          (∫ x in (1 : ℝ) / 3..1 / 2, logMean x)) +
          (∫ x in (1 : ℝ) / 2..2 / 3, logMean x)) +
          (∫ x in (2 : ℝ) / 3..5 / 6, logMean x)) +
          (∫ x in (5 : ℝ) / 6..1, logMean x) =
        (∫ x in (0 : ℝ)..1, logMean x) := by
    rw [hadd01, hadd012, hadd0123, hadd01234, hadd012345]
  have hlower :
      (1 / 6 : ℝ) *
          ((logMean 0 + logMean (1 / 6)) / 2 +
            (logMean (1 / 6) + logMean (1 / 3)) / 2 +
            (logMean (1 / 3) + logMean (1 / 2)) / 2 +
            (logMean (1 / 2) + logMean (2 / 3)) / 2 +
            (logMean (2 / 3) + logMean (5 / 6)) / 2 +
            (logMean (5 / 6) + logMean 1) / 2) ≤
        (∫ x in (0 : ℝ)..1, logMean x) := by
    rw [← hsum]
    nlinarith [hi0.1, hi1.1, hi2.1, hi3.1, hi4.1, hi5.1]
  have hupper :
      (∫ x in (0 : ℝ)..1, logMean x) ≤
        (1 / 6 : ℝ) *
          (logMean (1 / 12) + logMean (1 / 4) + logMean (5 / 12) +
            logMean (7 / 12) + logMean (3 / 4) + logMean (11 / 12)) := by
    rw [← hsum]
    nlinarith [hi0.2, hi1.2, hi2.2, hi3.2, hi4.2, hi5.2]
  have hn0 : logMean 0 = 1 := by
    rw [logMean_eq_logRatio (by norm_num)]
    norm_num [logRatio]
  have hn1 : |logMean ((1 : ℝ) / 6) - 1.0812| < 0.0001 := by
    rw [logMean_eq_logRatio (by norm_num)]
    simpa only [thirdSample, gap68] using gap69
  have hn2 : |logMean ((1 : ℝ) / 3) - 1.1587| < 0.0001 := by
    rw [logMean_eq_logRatio (by norm_num)]
    simpa only [thirdSample, gap70] using gap71
  have hn3 : |logMean ((1 : ℝ) / 2) - 1.2332| < 0.0001 := by
    rw [logMean_eq_logRatio (by norm_num)]
    simpa only [thirdSample, gap72] using gap73
  have hn4 : |logMean ((2 : ℝ) / 3) - 1.3051| < 0.0001 := by
    rw [logMean_eq_logRatio (by norm_num)]
    simpa only [thirdSample, gap74] using gap75
  have hn5 : |logMean ((5 : ℝ) / 6) - 1.3748| < 0.0001 := by
    rw [logMean_eq_logRatio (by norm_num)]
    simpa only [thirdSample, gap76] using gap77
  have hn6 : |logMean (1 : ℝ) - 1.4427| < 0.0001 := by
    rw [logMean_eq_logRatio (by norm_num)]
    simpa only [thirdSample, gap78] using gap79
  have hm1 : |logMean ((1 : ℝ) / 12) - 1.0411| < 0.0001 := by
    rw [logMean_eq_logRatio (by norm_num)]
    exact logRatio_midpoint1
  have hm2 : |logMean ((1 : ℝ) / 4) - 1.1204| < 0.0001 := by
    rw [logMean_eq_logRatio (by norm_num)]
    exact logRatio_midpoint2
  have hm3 : |logMean ((5 : ℝ) / 12) - 1.1963| < 0.0001 := by
    rw [logMean_eq_logRatio (by norm_num)]
    exact logRatio_midpoint3
  have hm4 : |logMean ((7 : ℝ) / 12) - 1.2694| < 0.0001 := by
    rw [logMean_eq_logRatio (by norm_num)]
    exact logRatio_midpoint4
  have hm5 : |logMean ((3 : ℝ) / 4) - 1.3402| < 0.0001 := by
    rw [logMean_eq_logRatio (by norm_num)]
    exact logRatio_midpoint5
  have hm6 : |logMean ((11 : ℝ) / 12) - 1.4090| < 0.0001 := by
    rw [logMean_eq_logRatio (by norm_num)]
    exact logRatio_midpoint6
  rw [abs_lt] at hn1 hn2 hn3 hn4 hn5 hn6 hm1 hm2 hm3 hm4 hm5 hm6
  have hlowerNum : (1.2283 : ℝ) <
      (1 / 6 : ℝ) *
        ((logMean 0 + logMean (1 / 6)) / 2 +
          (logMean (1 / 6) + logMean (1 / 3)) / 2 +
          (logMean (1 / 3) + logMean (1 / 2)) / 2 +
          (logMean (1 / 2) + logMean (2 / 3)) / 2 +
          (logMean (2 / 3) + logMean (5 / 6)) / 2 +
          (logMean (5 / 6) + logMean 1) / 2) := by
    rw [hn0]
    linarith
  have hupperNum :
      (1 / 6 : ℝ) *
          (logMean (1 / 12) + logMean (1 / 4) + logMean (5 / 12) +
            logMean (7 / 12) + logMean (3 / 4) + logMean (11 / 12)) <
        1.2303 := by
    linarith
  have hthird : thirdIntegral = (∫ x in (0 : ℝ)..1, logMean x) := by
    unfold thirdIntegral
    apply intervalIntegral.integral_congr
    intro x hx
    exact (logMean_eq_logRatio (by simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      using hx)).symm
  rw [hthird, abs_lt]
  constructor <;> linarith

end

end ProofGap.Exercise2536
