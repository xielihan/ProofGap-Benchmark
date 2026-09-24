import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open MeasureTheory Set
open scoped Interval

namespace ProofGap.Exercise2486

noncomputable section

def profile (a x : ℝ) : ℝ := x * Real.sqrt (x / a)

def surfaceArea (a : ℝ) : ℝ :=
  2 * Real.pi * ∫ x in 0..a,
    profile a x * Real.sqrt (1 + 9 * x / (4 * a))

private def radicand (c x : ℝ) : ℝ := (x + c) ^ 2 - c ^ 2

private def firstAntiderivative (c x : ℝ) : ℝ :=
  radicand c x * Real.sqrt (radicand c x) / 3

private def sqrtAntiderivative (c x : ℝ) : ℝ :=
  (x + c) * Real.sqrt (radicand c x) / 2 -
    c ^ 2 / 2 * Real.log ((x + c + Real.sqrt (radicand c x)) / c)

private theorem firstAntiderivative_hasDerivAt (c x : ℝ) (hc : 0 < c) (hx : 0 < x) :
    HasDerivAt (firstAntiderivative c)
      ((x + c) * Real.sqrt (radicand c x)) x := by
  have hxc : 0 < x + 2 * c := by linarith
  have hmul : 0 < x * (x + 2 * c) := mul_pos hx hxc
  have hqpos : 0 < radicand c x := by
    unfold radicand
    nlinarith
  have ht : HasDerivAt (fun y : ℝ => y + c) 1 x := by
    convert (hasDerivAt_id x).add (hasDerivAt_const x c) using 1 <;> simp [id]
  have hq : HasDerivAt (radicand c) (2 * (x + c)) x := by
    unfold radicand
    convert (ht.pow 2).sub (hasDerivAt_const x (c ^ 2)) using 1 <;> norm_num <;> ring
  have hr := hq.sqrt hqpos.ne'
  have htotal := (hq.mul hr).div_const 3
  unfold firstAntiderivative
  convert htotal using 1
  have hr0 : Real.sqrt (radicand c x) ≠ 0 := Real.sqrt_ne_zero'.mpr hqpos
  have hrsq : (Real.sqrt (radicand c x)) ^ 2 = radicand c x :=
    Real.sq_sqrt hqpos.le
  simp only [Pi.mul_apply] at *
  field_simp [hr0]
  rw [hrsq]
  ring

private theorem sqrtAntiderivative_hasDerivAt (c x : ℝ) (hc : 0 < c) (hx : 0 < x) :
    HasDerivAt (sqrtAntiderivative c) (Real.sqrt (radicand c x)) x := by
  have hxc : 0 < x + 2 * c := by linarith
  have hmul : 0 < x * (x + 2 * c) := mul_pos hx hxc
  have hqpos : 0 < radicand c x := by
    unfold radicand
    nlinarith
  have ht : HasDerivAt (fun y : ℝ => y + c) 1 x := by
    convert (hasDerivAt_id x).add (hasDerivAt_const x c) using 1 <;> simp [id]
  have hq : HasDerivAt (radicand c) (2 * (x + c)) x := by
    unfold radicand
    convert (ht.pow 2).sub (hasDerivAt_const x (c ^ 2)) using 1 <;> norm_num <;> ring
  have hr := hq.sqrt hqpos.ne'
  have hsum : HasDerivAt
      (fun y : ℝ => y + c + Real.sqrt (radicand c y))
      (1 + 2 * (x + c) / (2 * Real.sqrt (radicand c x))) x := by
    convert ht.add hr using 1 <;> ring
  have harg := hsum.div_const c
  have hargpos : 0 <
      (x + c + Real.sqrt (radicand c x)) / c := by positivity
  have hlog := harg.log hargpos.ne'
  have hr0 : Real.sqrt (radicand c x) ≠ 0 := Real.sqrt_ne_zero'.mpr hqpos
  have hnum0 : x + c + Real.sqrt (radicand c x) ≠ 0 := by positivity
  have hrsq : (Real.sqrt (radicand c x)) ^ 2 = radicand c x :=
    Real.sq_sqrt hqpos.le
  have hlogSimple : HasDerivAt
      (fun y : ℝ => Real.log
        ((y + c + Real.sqrt (radicand c y)) / c))
      (1 / Real.sqrt (radicand c x)) x := by
    convert hlog using 1
    simp only [Pi.add_apply] at *
    field_simp [hc.ne', hr0, hnum0]
    ring
  have hfirst := (ht.mul hr).div_const 2
  have htotal := hfirst.sub (hlogSimple.const_mul (c ^ 2 / 2))
  unfold sqrtAntiderivative
  convert htotal using 1
  simp only [Pi.mul_apply] at *
  field_simp [hr0]
  rw [hrsq]
  unfold radicand
  ring

theorem gap1 (a x : ℝ) (ha : 0 < a) (hx : 0 < x) :
    Real.sqrt (1 + deriv (profile a) x ^ 2) =
      Real.sqrt (1 + 9 * x / (4 * a)) := by
  have hxa : 0 < x / a := div_pos hx ha
  have hs : HasDerivAt (fun t : ℝ => Real.sqrt (t / a))
      ((1 / a) / (2 * Real.sqrt (x / a))) x := by
    simpa [id] using ((hasDerivAt_id x).div_const a).sqrt hxa.ne'
  have hsne : Real.sqrt (x / a) ≠ 0 := Real.sqrt_ne_zero'.mpr hxa
  have hssq : (Real.sqrt (x / a)) ^ 2 = x / a := Real.sq_sqrt hxa.le
  have hprofile : HasDerivAt (profile a)
      ((3 / 2 : ℝ) * Real.sqrt (x / a)) x := by
    unfold profile
    convert (hasDerivAt_id x).mul hs using 1
    field_simp [ha.ne', hsne]
    simp only [id_eq]
    rw [hssq]
    field_simp [ha.ne']
    norm_num
  rw [hprofile.deriv]
  congr 1
  rw [mul_pow, hssq]
  field_simp [ha.ne']
  ring_nf

theorem gap2 (a Pₓ : ℝ) (ha : 0 < a) (hP : Pₓ = surfaceArea a) :
    Pₓ = 2 * Real.pi * ∫ x in 0..a,
      x * Real.sqrt (x / a) * Real.sqrt (1 + 9 * x / (4 * a)) := by
  rw [hP]
  rfl

theorem gap3 (a Pₓ : ℝ) (ha : 0 < a) (hP : Pₓ = surfaceArea a) :
    Pₓ = 3 * Real.pi / a * ∫ x in 0..a,
      x * Real.sqrt (x ^ 2 + 4 * a * x / 9) := by
  rw [gap2 a Pₓ ha hP]
  calc
    2 * Real.pi * ∫ x in 0..a,
        x * Real.sqrt (x / a) * Real.sqrt (1 + 9 * x / (4 * a)) =
        ∫ x in 0..a, (2 * Real.pi) *
          (x * Real.sqrt (x / a) * Real.sqrt (1 + 9 * x / (4 * a))) := by
      rw [intervalIntegral.integral_const_mul]
    _ = ∫ x in 0..a, (3 * Real.pi / a) *
          (x * Real.sqrt (x ^ 2 + 4 * a * x / 9)) := by
      apply intervalIntegral.integral_congr
      intro x hxint
      change (2 * Real.pi) *
          (x * Real.sqrt (x / a) * Real.sqrt (1 + 9 * x / (4 * a))) =
        (3 * Real.pi / a) *
          (x * Real.sqrt (x ^ 2 + 4 * a * x / 9))
      rw [uIcc_of_le ha.le] at hxint
      have hxa : 0 ≤ x / a := div_nonneg hxint.1 ha.le
      have hone : 0 ≤ 1 + 9 * x / (4 * a) := by
        have : 0 ≤ 9 * x / (4 * a) :=
          div_nonneg (mul_nonneg (by norm_num) hxint.1)
            (mul_nonneg (by norm_num) ha.le)
        linarith
      have hquad : 0 ≤ x ^ 2 + 4 * a * x / 9 := by
        have : 0 ≤ 4 * a * x / 9 :=
          div_nonneg (mul_nonneg (mul_nonneg (by norm_num) ha.le) hxint.1) (by norm_num)
        positivity
      have hroot : Real.sqrt (x / a) * Real.sqrt (1 + 9 * x / (4 * a)) =
          (3 / (2 * a)) * Real.sqrt (x ^ 2 + 4 * a * x / 9) := by
        apply (sq_eq_sq₀ (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
          (mul_nonneg (by positivity) (Real.sqrt_nonneg _))).mp
        rw [mul_pow, Real.sq_sqrt hxa, Real.sq_sqrt hone, mul_pow,
          Real.sq_sqrt hquad]
        field_simp [ha.ne']
        ring
      rw [show x * Real.sqrt (x / a) * Real.sqrt (1 + 9 * x / (4 * a)) =
        x * (Real.sqrt (x / a) * Real.sqrt (1 + 9 * x / (4 * a))) by ring,
        hroot]
      field_simp [ha.ne']
    _ = 3 * Real.pi / a * ∫ x in 0..a,
          x * Real.sqrt (x ^ 2 + 4 * a * x / 9) := by
      rw [intervalIntegral.integral_const_mul]

theorem gap4 (a Pₓ : ℝ) (ha : 0 < a) (hP : Pₓ = surfaceArea a) :
    Pₓ =
      3 * Real.pi / a * (∫ x in 0..a,
        (x + 2 * a / 9) *
          Real.sqrt ((x + 2 * a / 9) ^ 2 - (2 * a / 9) ^ 2)) -
      3 * Real.pi / a * (2 * a / 9) *
        ∫ x in 0..a, Real.sqrt (x ^ 2 + 4 * a * x / 9) := by
  rw [gap3 a Pₓ ha hP]
  have hqcont : Continuous (fun x : ℝ =>
      Real.sqrt (x ^ 2 + 4 * a * x / 9)) := by
    fun_prop
  have hxqint : IntervalIntegrable
      (fun x : ℝ => x * Real.sqrt (x ^ 2 + 4 * a * x / 9)) volume 0 a :=
    (continuous_id.mul hqcont).intervalIntegrable 0 a
  have hcqint : IntervalIntegrable
      (fun x : ℝ => (2 * a / 9) * Real.sqrt (x ^ 2 + 4 * a * x / 9))
      volume 0 a :=
    (continuous_const.mul hqcont).intervalIntegrable 0 a
  have hfirst :
      (∫ x in 0..a, (x + 2 * a / 9) *
          Real.sqrt ((x + 2 * a / 9) ^ 2 - (2 * a / 9) ^ 2)) =
        (∫ x in 0..a, x * Real.sqrt (x ^ 2 + 4 * a * x / 9)) +
          (2 * a / 9) * ∫ x in 0..a, Real.sqrt (x ^ 2 + 4 * a * x / 9) := by
    calc
      (∫ x in 0..a, (x + 2 * a / 9) *
          Real.sqrt ((x + 2 * a / 9) ^ 2 - (2 * a / 9) ^ 2)) =
          ∫ x in 0..a,
            x * Real.sqrt (x ^ 2 + 4 * a * x / 9) +
              (2 * a / 9) * Real.sqrt (x ^ 2 + 4 * a * x / 9) := by
        apply intervalIntegral.integral_congr
        intro x hx
        change (x + 2 * a / 9) *
            Real.sqrt ((x + 2 * a / 9) ^ 2 - (2 * a / 9) ^ 2) =
          x * Real.sqrt (x ^ 2 + 4 * a * x / 9) +
            (2 * a / 9) * Real.sqrt (x ^ 2 + 4 * a * x / 9)
        rw [show (x + 2 * a / 9) ^ 2 - (2 * a / 9) ^ 2 =
          x ^ 2 + 4 * a * x / 9 by ring]
        ring
      _ = (∫ x in 0..a, x * Real.sqrt (x ^ 2 + 4 * a * x / 9)) +
          (2 * a / 9) * ∫ x in 0..a, Real.sqrt (x ^ 2 + 4 * a * x / 9) := by
        rw [intervalIntegral.integral_add hxqint hcqint,
          intervalIntegral.integral_const_mul]
  rw [hfirst]
  ring

theorem gap5 (a Pₓ : ℝ) (ha : 0 < a) (hP : Pₓ = surfaceArea a) :
    Pₓ =
      13 * Real.sqrt 13 / 27 * Real.pi * a ^ 2 -
      11 * Real.sqrt 13 / 81 * Real.pi * a ^ 2 +
      4 * Real.pi * a ^ 2 / 243 *
        Real.log ((11 + 3 * Real.sqrt 13) / 2) := by
  let c : ℝ := 2 * a / 9
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have hrad (x : ℝ) : radicand c x = x ^ 2 + 4 * a * x / 9 := by
    dsimp [c, radicand]
    ring
  have hrad0 : radicand c 0 = 0 := by
    rw [hrad]
    ring
  have hradA : radicand c a = 13 * a ^ 2 / 9 := by
    rw [hrad]
    ring
  have hs13sq : (Real.sqrt 13) ^ 2 = 13 := Real.sq_sqrt (by norm_num)
  have hsqrtA : Real.sqrt (radicand c a) = a * Real.sqrt 13 / 3 := by
    rw [hradA]
    apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
    rw [Real.sq_sqrt (by positivity), div_pow, mul_pow, hs13sq]
    ring
  have hF1cont : Continuous (firstAntiderivative c) := by
    unfold firstAntiderivative radicand
    fun_prop
  have hI1int : IntervalIntegrable
      (fun x : ℝ => (x + c) * Real.sqrt (radicand c x)) volume 0 a := by
    exact (by
      unfold radicand
      fun_prop : Continuous
        (fun x : ℝ => (x + c) * Real.sqrt (radicand c x))).intervalIntegrable 0 a
  have hFTC1 :
      (∫ x in 0..a, (x + c) * Real.sqrt (radicand c x)) =
        firstAntiderivative c a - firstAntiderivative c 0 := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ha.le
      hF1cont.continuousOn
      (fun x hx => firstAntiderivative_hasDerivAt c x hc hx.1) hI1int
  have hI1rad :
      (∫ x in 0..a, (x + c) * Real.sqrt (radicand c x)) =
        13 * Real.sqrt 13 * a ^ 3 / 81 := by
    rw [hFTC1]
    unfold firstAntiderivative
    rw [hsqrtA, hradA, hrad0]
    simp
    ring
  have hF2cont : ContinuousOn (sqrtAntiderivative c) (Icc (0 : ℝ) a) := by
    intro x hx
    have hx0 : 0 ≤ x := hx.1
    have hradx : 0 ≤ radicand c x := by
      rw [hrad]
      positivity
    have hargpos : 0 <
        (x + c + Real.sqrt (radicand c x)) / c := by positivity
    unfold sqrtAntiderivative radicand
    apply ContinuousAt.continuousWithinAt
    fun_prop (disch := positivity)
  have hI2int : IntervalIntegrable
      (fun x : ℝ => Real.sqrt (radicand c x)) volume 0 a := by
    exact (by
      unfold radicand
      fun_prop : Continuous
        (fun x : ℝ => Real.sqrt (radicand c x))).intervalIntegrable 0 a
  have hFTC2 :
      (∫ x in 0..a, Real.sqrt (radicand c x)) =
        sqrtAntiderivative c a - sqrtAntiderivative c 0 := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ha.le hF2cont
      (fun x hx => sqrtAntiderivative_hasDerivAt c x hc hx.1) hI2int
  have hargA :
      (a + c + Real.sqrt (radicand c a)) / c =
        (11 + 3 * Real.sqrt 13) / 2 := by
    rw [hsqrtA]
    dsimp [c]
    field_simp [ha.ne']
    ring
  have hF2a : sqrtAntiderivative c a =
      11 * Real.sqrt 13 * a ^ 2 / 54 -
        2 * a ^ 2 / 81 * Real.log ((11 + 3 * Real.sqrt 13) / 2) := by
    unfold sqrtAntiderivative
    rw [hargA, hsqrtA]
    dsimp [c]
    ring
  have hF20 : sqrtAntiderivative c 0 = 0 := by
    unfold sqrtAntiderivative
    rw [hrad0]
    simp [hc.ne']
  have hI2rad :
      (∫ x in 0..a, Real.sqrt (radicand c x)) =
        11 * Real.sqrt 13 * a ^ 2 / 54 -
          2 * a ^ 2 / 81 * Real.log ((11 + 3 * Real.sqrt 13) / 2) := by
    rw [hFTC2, hF2a, hF20, sub_zero]
  have hI1 :
      (∫ x in 0..a, (x + 2 * a / 9) *
        Real.sqrt ((x + 2 * a / 9) ^ 2 - (2 * a / 9) ^ 2)) =
          13 * Real.sqrt 13 * a ^ 3 / 81 := by
    change (∫ x in 0..a, (x + c) * Real.sqrt (radicand c x)) = _
    exact hI1rad
  have hI2 :
      (∫ x in 0..a, Real.sqrt (x ^ 2 + 4 * a * x / 9)) =
        11 * Real.sqrt 13 * a ^ 2 / 54 -
          2 * a ^ 2 / 81 * Real.log ((11 + 3 * Real.sqrt 13) / 2) := by
    calc
      (∫ x in 0..a, Real.sqrt (x ^ 2 + 4 * a * x / 9)) =
          ∫ x in 0..a, Real.sqrt (radicand c x) := by
        apply intervalIntegral.integral_congr
        intro x hx
        change Real.sqrt (x ^ 2 + 4 * a * x / 9) = Real.sqrt (radicand c x)
        rw [hrad]
      _ = _ := hI2rad
  rw [gap4 a Pₓ ha hP, hI1, hI2]
  field_simp [ha.ne']
  ring

theorem gap6 (a Pₓ : ℝ) (ha : 0 < a) (hP : Pₓ = surfaceArea a) :
    Pₓ = 4 * Real.pi * a ^ 2 / 243 *
      (21 * Real.sqrt 13 +
        2 * Real.log ((3 + Real.sqrt 13) / 2)) := by
  have hs13sq : (Real.sqrt 13) ^ 2 = 13 := Real.sq_sqrt (by norm_num)
  have hsq : ((3 + Real.sqrt 13) / 2) ^ 2 =
      (11 + 3 * Real.sqrt 13) / 2 := by
    nlinarith
  have hlog : Real.log ((11 + 3 * Real.sqrt 13) / 2) =
      2 * Real.log ((3 + Real.sqrt 13) / 2) := by
    rw [← hsq, Real.log_pow]
    norm_num
  rw [gap5 a Pₓ ha hP, hlog]
  ring

end

end ProofGap.Exercise2486
