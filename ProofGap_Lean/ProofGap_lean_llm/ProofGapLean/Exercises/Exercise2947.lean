import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Complex.AbelLimit
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

namespace ProofGap.Exercise2947

noncomputable section

open scoped Interval
open Filter
open Topology

def coefficientIntegral (a : ℝ) (n : ℕ) : ℝ :=
  2 / Real.pi *
    ∫ x in 0..Real.pi,
      Real.sinh (a * x) * Real.sin ((n : ℝ) * x)

def firstParts (a : ℝ) (n : ℕ) : ℝ :=
  2 / Real.pi *
    (((-1 / (n : ℝ) * Real.sinh (a * Real.pi) *
          Real.cos ((n : ℝ) * Real.pi)) -
        (-1 / (n : ℝ) * Real.sinh (a * 0) *
          Real.cos ((n : ℝ) * 0))) +
      a / (n : ℝ) *
        ∫ x in 0..Real.pi,
          Real.cos ((n : ℝ) * x) * Real.cosh (a * x))

def reducedParts (a : ℝ) (n : ℕ) : ℝ :=
  2 / Real.pi *
    (((-1 : ℝ) ^ (n + 1) / (n : ℝ)) *
        Real.sinh (a * Real.pi) -
      a ^ 2 / (n : ℝ) ^ 2 *
        ∫ x in 0..Real.pi,
          Real.sinh (a * x) * Real.sin ((n : ℝ) * x))

def fourierSeries (a x : ℝ) : ℝ :=
  2 * Real.sinh (a * Real.pi) / Real.pi *
    ∑' k : ℕ,
      (-1 : ℝ) ^ (k + 2) *
        ((k + 1 : ℝ) * Real.sin ((k + 1 : ℝ) * x) /
          ((k + 1 : ℝ) ^ 2 + a ^ 2))

private theorem sinh_sin_integral_parts
    (a : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    (∫ x in (0 : ℝ)..Real.pi,
        Real.sinh (a * x) * Real.sin ((n : ℝ) * x)) =
      ((-1 / (n : ℝ)) * Real.sinh (a * Real.pi) *
          Real.cos ((n : ℝ) * Real.pi) -
        (-1 / (n : ℝ)) * Real.sinh (a * 0) *
          Real.cos ((n : ℝ) * 0)) +
        a / (n : ℝ) *
          ∫ x in (0 : ℝ)..Real.pi,
            Real.cos ((n : ℝ) * x) * Real.cosh (a * x) := by
  have hn0 : (n : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  let u : ℝ → ℝ := fun x => Real.sinh (a * x)
  let u' : ℝ → ℝ := fun x => a * Real.cosh (a * x)
  let v : ℝ → ℝ := fun x => -1 / (n : ℝ) * Real.cos ((n : ℝ) * x)
  let v' : ℝ → ℝ := fun x => Real.sin ((n : ℝ) * x)
  have hu : ∀ x ∈ Set.uIcc (0 : ℝ) Real.pi,
      HasDerivAt u (u' x) x := by
    intro x hx
    dsimp [u, u']
    convert (Real.hasDerivAt_sinh (a * x)).comp x
      ((hasDerivAt_id x).const_mul a) using 1 <;> ring
  have hv : ∀ x ∈ Set.uIcc (0 : ℝ) Real.pi,
      HasDerivAt v (v' x) x := by
    intro x hx
    dsimp [v, v']
    have hinner : HasDerivAt (fun y : ℝ => (n : ℝ) * y) (n : ℝ) x := by
      simpa only [id_eq, mul_one] using (hasDerivAt_id x).const_mul (n : ℝ)
    convert ((Real.hasDerivAt_cos ((n : ℝ) * x)).comp x hinner).const_mul
      (-1 / (n : ℝ)) using 1
    field_simp [hn0]
  have huInt : IntervalIntegrable u' MeasureTheory.volume 0 Real.pi := by
    apply Continuous.intervalIntegrable
    exact continuous_const.mul
      (Real.continuous_cosh.comp (continuous_const.mul continuous_id))
  have hvInt : IntervalIntegrable v' MeasureTheory.volume 0 Real.pi := by
    apply Continuous.intervalIntegrable
    exact Real.continuous_sin.comp (continuous_const.mul continuous_id)
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    hu hv huInt hvInt
  have hint :
      (∫ x in (0 : ℝ)..Real.pi, u' x * v x) =
        -(a / (n : ℝ)) *
          ∫ x in (0 : ℝ)..Real.pi,
            Real.cos ((n : ℝ) * x) * Real.cosh (a * x) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x hx
    dsimp [u', v]
    ring
  dsimp [u, v, v'] at hparts
  rw [hint] at hparts
  linarith

private theorem cos_cosh_integral_parts
    (a : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    (∫ x in (0 : ℝ)..Real.pi,
        Real.cos ((n : ℝ) * x) * Real.cosh (a * x)) =
      -(a / (n : ℝ)) *
        ∫ x in (0 : ℝ)..Real.pi,
          Real.sinh (a * x) * Real.sin ((n : ℝ) * x) := by
  have hn0 : (n : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  let u : ℝ → ℝ := fun x => Real.cosh (a * x)
  let u' : ℝ → ℝ := fun x => a * Real.sinh (a * x)
  let v : ℝ → ℝ := fun x => Real.sin ((n : ℝ) * x) / (n : ℝ)
  let v' : ℝ → ℝ := fun x => Real.cos ((n : ℝ) * x)
  have hu : ∀ x ∈ Set.uIcc (0 : ℝ) Real.pi,
      HasDerivAt u (u' x) x := by
    intro x hx
    dsimp [u, u']
    convert (Real.hasDerivAt_cosh (a * x)).comp x
      ((hasDerivAt_id x).const_mul a) using 1 <;> ring
  have hv : ∀ x ∈ Set.uIcc (0 : ℝ) Real.pi,
      HasDerivAt v (v' x) x := by
    intro x hx
    dsimp [v, v']
    have hinner : HasDerivAt (fun y : ℝ => (n : ℝ) * y) (n : ℝ) x := by
      simpa only [id_eq, mul_one] using (hasDerivAt_id x).const_mul (n : ℝ)
    convert ((Real.hasDerivAt_sin ((n : ℝ) * x)).comp x hinner).div_const
      (n : ℝ) using 1
    field_simp [hn0]
  have huInt : IntervalIntegrable u' MeasureTheory.volume 0 Real.pi := by
    apply Continuous.intervalIntegrable
    exact continuous_const.mul
      (Real.continuous_sinh.comp (continuous_const.mul continuous_id))
  have hvInt : IntervalIntegrable v' MeasureTheory.volume 0 Real.pi := by
    apply Continuous.intervalIntegrable
    exact Real.continuous_cos.comp (continuous_const.mul continuous_id)
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    hu hv huInt hvInt
  have hint :
      (∫ x in (0 : ℝ)..Real.pi, u' x * v x) =
        a / (n : ℝ) *
          ∫ x in (0 : ℝ)..Real.pi,
            Real.sinh (a * x) * Real.sin ((n : ℝ) * x) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x hx
    dsimp [u', v]
    ring
  dsimp [u, v, v'] at hparts
  rw [hint] at hparts
  simp only [Real.sin_nat_mul_pi, Real.sin_zero, zero_div,
    mul_zero, sub_zero] at hparts
  simpa [mul_comm] using hparts

private theorem two_pi_pos : (0 : ℝ) < 2 * Real.pi := by
  positivity

private theorem neg_pi_lt_pi : -Real.pi < Real.pi := by
  linarith [Real.pi_pos]

private def slope (a : ℝ) : ℝ :=
  Real.sinh (a * Real.pi) / Real.pi

private def adjustedSinhC (a x : ℝ) : ℂ :=
  (Real.sinh (a * x) - slope a * x : ℝ)

private def adjustedSinhC' (a x : ℝ) : ℂ :=
  (a * Real.cosh (a * x) - slope a : ℝ)

private def adjustedSinhC'' (a x : ℝ) : ℂ :=
  (a ^ 2 * Real.sinh (a * x) : ℝ)

private theorem hasDerivAt_adjustedSinhC (a x : ℝ) :
    HasDerivAt (adjustedSinhC a) (adjustedSinhC' a x) x := by
  have hsinh :
      HasDerivAt (fun y : ℝ => Real.sinh (a * y))
        (a * Real.cosh (a * x)) x := by
    convert (Real.hasDerivAt_sinh (a * x)).comp x
      ((hasDerivAt_id x).const_mul a) using 1 <;> ring
  have hlinear :
      HasDerivAt (fun y : ℝ => slope a * y) (slope a) x := by
    simpa only [id_eq, mul_one] using
      (hasDerivAt_id x).const_mul (slope a)
  convert (hsinh.sub hlinear).ofReal_comp using 1 <;>
    simp [adjustedSinhC, adjustedSinhC']

private theorem hasDerivAt_adjustedSinhC' (a x : ℝ) :
    HasDerivAt (adjustedSinhC' a) (adjustedSinhC'' a x) x := by
  have hcosh :
      HasDerivAt (fun y : ℝ => a * Real.cosh (a * y))
        (a ^ 2 * Real.sinh (a * x)) x := by
    have h :=
      ((Real.hasDerivAt_cosh (a * x)).comp x
        ((hasDerivAt_id x).const_mul a)).const_mul a
    convert h using 1 <;> ring
  convert (hcosh.sub_const (slope a)).ofReal_comp using 1 <;>
    simp [adjustedSinhC', adjustedSinhC'']

private theorem adjustedSinhC_endpoints (a : ℝ) :
    adjustedSinhC a Real.pi = adjustedSinhC a (-Real.pi) := by
  norm_cast
  simp [adjustedSinhC, slope, mul_neg, Real.sinh_neg,
    Real.pi_ne_zero]

private theorem adjustedSinhC'_endpoints (a : ℝ) :
    adjustedSinhC' a Real.pi = adjustedSinhC' a (-Real.pi) := by
  norm_cast
  simp [adjustedSinhC', slope, mul_neg, Real.cosh_neg]

private def linearC (x : ℝ) : ℂ := (x : ℂ)

private theorem fourierCoeffOn_one_eq_zero (n : ℤ) (hn : n ≠ 0) :
    fourierCoeffOn neg_pi_lt_pi (fun _ : ℝ => (1 : ℂ)) n = 0 := by
  have h := fourierCoeffOn_of_hasDerivAt neg_pi_lt_pi hn
    (f := fun _ : ℝ => (1 : ℂ)) (f' := fun _ : ℝ => (0 : ℂ))
    (fun x hx => hasDerivAt_const x 1)
    ((continuous_const : Continuous (fun _ : ℝ => (0 : ℂ))).intervalIntegrable _ _)
  simpa [fourierCoeffOn_eq_integral] using h

private theorem fourier_at_neg_pi (n : ℤ) :
    fourier (-n) ((-Real.pi : ℝ) : AddCircle (2 * Real.pi)) =
      (-1 : ℂ) ^ n := by
  rw [fourier_coe_apply]
  have harg :
      2 * (Real.pi : ℂ) * Complex.I * ((-n : ℤ) : ℂ) *
          (((-Real.pi : ℝ) : ℂ)) / (((2 * Real.pi : ℝ) : ℂ)) =
        (n : ℂ) * ((Real.pi : ℂ) * Complex.I) := by
    push_cast
    field_simp [Real.pi_ne_zero]
  rw [harg, Complex.exp_int_mul, Complex.exp_pi_mul_I]

private theorem fourierCoeffOn_linearC_eq (n : ℤ) (hn : n ≠ 0) :
    fourierCoeffOn neg_pi_lt_pi linearC n =
      Complex.I * (-1 : ℂ) ^ n / (n : ℂ) := by
  have h := fourierCoeffOn_of_hasDerivAt neg_pi_lt_pi hn
    (f := linearC) (f' := fun _ : ℝ => (1 : ℂ))
    (fun x hx => by
      simpa [linearC] using (hasDerivAt_id x).ofReal_comp)
    ((continuous_const : Continuous (fun _ : ℝ => (1 : ℂ))).intervalIntegrable _ _)
  have hfourier :
      fourier (-n)
          ((-Real.pi : ℝ) :
            AddCircle (Real.pi - -Real.pi)) =
        (-1 : ℂ) ^ n := by
    rw [fourier_coe_apply]
    have harg :
        2 * (Real.pi : ℂ) * Complex.I * ((-n : ℤ) : ℂ) *
            (((-Real.pi : ℝ) : ℂ)) /
              (((Real.pi - -Real.pi : ℝ) : ℂ)) =
          (n : ℂ) * ((Real.pi : ℂ) * Complex.I) := by
      push_cast
      field_simp [Real.pi_ne_zero]
      ring
    rw [harg, Complex.exp_int_mul, Complex.exp_pi_mul_I]
  rw [h, fourierCoeffOn_one_eq_zero n hn, hfourier]
  simp only [linearC, mul_zero, sub_zero]
  push_cast
  field_simp [show (n : ℂ) ≠ 0 by exact_mod_cast hn,
    Real.pi_ne_zero, Complex.I_ne_zero]
  rw [Complex.I_sq]
  ring_nf

private theorem fourierCoeffOn_add
    (f g : ℝ → ℂ) (hf : Continuous f) (hg : Continuous g)
    (n : ℤ) :
    fourierCoeffOn neg_pi_lt_pi (fun x => f x + g x) n =
      fourierCoeffOn neg_pi_lt_pi f n +
        fourierCoeffOn neg_pi_lt_pi g n := by
  rw [fourierCoeffOn_eq_integral, fourierCoeffOn_eq_integral,
    fourierCoeffOn_eq_integral]
  simp_rw [smul_add]
  rw [intervalIntegral.integral_add
    ((by fun_prop : Continuous (fun x : ℝ =>
      fourier (-n)
        (x : AddCircle (Real.pi - -Real.pi)) • f x)).intervalIntegrable _ _)
    ((by fun_prop : Continuous (fun x : ℝ =>
      fourier (-n)
        (x : AddCircle (Real.pi - -Real.pi)) • g x)).intervalIntegrable _ _)]
  module

private def adjustedCoeff (a : ℝ) (n : ℤ) : ℂ :=
  -Complex.I * (slope a : ℂ) * (a : ℂ) ^ 2 * (-1 : ℂ) ^ n /
    ((n : ℂ) * ((n : ℂ) ^ 2 + (a : ℂ) ^ 2))

private theorem fourierCoeffOn_adjusted_zero (a : ℝ) :
    fourierCoeffOn neg_pi_lt_pi (adjustedSinhC a) 0 = 0 := by
  have hodd (x : ℝ) :
      adjustedSinhC a (-x) = -adjustedSinhC a x := by
    norm_cast
    simp [adjustedSinhC, slope, mul_neg, Real.sinh_neg]
    ring
  have hcomp :
      (∫ x in -Real.pi..Real.pi, adjustedSinhC a (-x)) =
        ∫ x in -Real.pi..Real.pi, adjustedSinhC a x := by
    simpa only [neg_neg] using
      (intervalIntegral.integral_comp_neg
        (f := adjustedSinhC a) (a := -Real.pi) (b := Real.pi))
  have hneg :
      (∫ x in -Real.pi..Real.pi, adjustedSinhC a (-x)) =
        -(∫ x in -Real.pi..Real.pi, adjustedSinhC a x) := by
    calc
      (∫ x in -Real.pi..Real.pi, adjustedSinhC a (-x)) =
          ∫ x in -Real.pi..Real.pi, -adjustedSinhC a x := by
            apply intervalIntegral.integral_congr
            intro x hx
            exact hodd x
      _ = -(∫ x in -Real.pi..Real.pi, adjustedSinhC a x) := by
        rw [intervalIntegral.integral_neg]
  have hint :
      (∫ x in -Real.pi..Real.pi, adjustedSinhC a x) = 0 := by
    exact CharZero.eq_neg_self_iff.mp (hcomp.symm.trans hneg)
  rw [fourierCoeffOn_eq_integral]
  simp [hint, fourier_zero]

private theorem fourierCoeffOn_adjusted_eq
    (a : ℝ) (n : ℤ) :
    fourierCoeffOn neg_pi_lt_pi (adjustedSinhC a) n =
      adjustedCoeff a n := by
  by_cases hn : n = 0
  · subst n
    rw [fourierCoeffOn_adjusted_zero]
    simp [adjustedCoeff]
  · have h1 := fourierCoeffOn_of_hasDerivAt neg_pi_lt_pi hn
      (f := adjustedSinhC a) (f' := adjustedSinhC' a)
      (fun x hx => hasDerivAt_adjustedSinhC a x)
      ((by
        unfold adjustedSinhC'
        fun_prop : Continuous (adjustedSinhC' a)).intervalIntegrable _ _)
    have h2 := fourierCoeffOn_of_hasDerivAt neg_pi_lt_pi hn
      (f := adjustedSinhC' a) (f' := adjustedSinhC'' a)
      (fun x hx => hasDerivAt_adjustedSinhC' a x)
      ((by
        unfold adjustedSinhC''
        fun_prop : Continuous (adjustedSinhC'' a)).intervalIntegrable _ _)
    have hsecond :
        fourierCoeffOn neg_pi_lt_pi (adjustedSinhC'' a) n =
          (a : ℂ) ^ 2 *
            (fourierCoeffOn neg_pi_lt_pi (adjustedSinhC a) n +
              (slope a : ℂ) *
                fourierCoeffOn neg_pi_lt_pi linearC n) := by
      rw [show adjustedSinhC'' a =
          fun x => (a : ℂ) ^ 2 *
            (adjustedSinhC a x + (slope a : ℂ) * linearC x) by
            funext x
            norm_cast
            simp only [adjustedSinhC'', adjustedSinhC, linearC]
            push_cast
            ring]
      rw [fourierCoeffOn.const_mul]
      congr 1
      rw [fourierCoeffOn_add]
      · rw [fourierCoeffOn.const_mul]
      · unfold adjustedSinhC
        fun_prop
      · unfold linearC
        fun_prop
    simp only [adjustedSinhC_endpoints, sub_self, mul_zero, zero_mul,
      zero_sub] at h1
    simp only [adjustedSinhC'_endpoints, sub_self, mul_zero, zero_mul,
      zero_sub] at h2
    rw [hsecond] at h2
    rw [fourierCoeffOn_linearC_eq n hn] at h2
    generalize hC :
      fourierCoeffOn neg_pi_lt_pi (adjustedSinhC a) n = C at h1 h2
    unfold adjustedCoeff
    have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    have hdenR : 0 < (n : ℝ) ^ 2 + a ^ 2 := by positivity
    have hdenC : (n : ℂ) ^ 2 + (a : ℂ) ^ 2 ≠ 0 := by
      exact_mod_cast hdenR.ne'
    push_cast at h1 h2 ⊢
    field_simp [hnC, hdenC, Real.pi_ne_zero,
      Complex.I_ne_zero] at h1 h2 ⊢
    have hD :
        fourierCoeffOn neg_pi_lt_pi (adjustedSinhC' a) n =
          C * Complex.I * (n : ℂ) := by
      linear_combination (-1 / 2 : ℂ) * h1
    rw [hD] at h2
    ring_nf at h2
    rw [Complex.I_sq] at h2
    ring_nf at h2 ⊢
    linear_combination (-1 / 2 : ℂ) * h2

private theorem summable_adjustedCoeff (a : ℝ) :
    Summable (adjustedCoeff a) := by
  have hbase :
      Summable (fun n : ℤ => (1 : ℝ) / |(n : ℝ)| ^ (3 : ℝ)) := by
    simpa using
      (Real.summable_one_div_int_add_rpow 0 3).mpr (by norm_num)
  have hscaled :=
    hbase.mul_left (|slope a| * a ^ 2)
  apply hscaled.of_norm_bounded
  intro n
  by_cases hn : n = 0
  · subst n
    simp [adjustedCoeff]
  · have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    have hnabs : 0 < |(n : ℝ)| := abs_pos.mpr hnR
    have hden : 0 < (n : ℝ) ^ 2 + a ^ 2 := by positivity
    simp only [adjustedCoeff, norm_div, norm_mul, norm_neg,
      Complex.norm_I, one_mul, norm_pow, Complex.norm_real,
      norm_zpow, norm_one, one_zpow, Int.cast_abs,
      Complex.norm_intCast, mul_one]
    have hdenCast :
        (n : ℂ) ^ 2 + (a : ℂ) ^ 2 =
          (((n : ℝ) ^ 2 + a ^ 2 : ℝ) : ℂ) := by
      push_cast
      rfl
    rw [hdenCast, Complex.norm_real]
    simp only [Complex.norm_real, Real.norm_eq_abs]
    change |slope a| * |a| ^ 2 /
        (|(n : ℝ)| * |(n : ℝ) ^ 2 + a ^ 2|) ≤
      |slope a| * a ^ 2 * (1 / |(n : ℝ)| ^ 3)
    rw [abs_of_pos hden, sq_abs]
    have hden_le :
        |(n : ℝ)| ^ 3 ≤
          |(n : ℝ)| * ((n : ℝ) ^ 2 + a ^ 2) := by
      have hpow :
          |(n : ℝ)| ^ 3 =
            |(n : ℝ)| * (n : ℝ) ^ 2 := by
        rw [pow_succ, sq_abs]
        ring
      rw [hpow]
      gcongr
      nlinarith [sq_nonneg a]
    simpa [div_eq_mul_inv] using
      (div_le_div_of_nonneg_left
        (mul_nonneg (abs_nonneg (slope a)) (sq_nonneg a))
        (pow_pos hnabs 3) hden_le)

private def periodizedAdjusted (a : ℝ) :
    AddCircle (2 * Real.pi) → ℂ :=
  letI : Fact (0 < 2 * Real.pi) := ⟨two_pi_pos⟩
  AddCircle.liftIoc (2 * Real.pi) (-Real.pi) (adjustedSinhC a)

private theorem continuous_periodizedAdjusted (a : ℝ) :
    Continuous (periodizedAdjusted a) := by
  letI : Fact (0 < 2 * Real.pi) := ⟨two_pi_pos⟩
  unfold periodizedAdjusted
  apply AddCircle.liftIoc_continuous
  · convert (adjustedSinhC_endpoints a).symm using 1 <;> ring
  · unfold adjustedSinhC
    fun_prop

private theorem fourierCoeff_periodizedAdjusted_eq
    (a : ℝ) (n : ℤ) :
    letI : Fact (0 < 2 * Real.pi) := ⟨two_pi_pos⟩
    fourierCoeff (periodizedAdjusted a) n = adjustedCoeff a n := by
  letI : Fact (0 < 2 * Real.pi) := ⟨two_pi_pos⟩
  rw [periodizedAdjusted, fourierCoeff_liftIoc_eq]
  convert fourierCoeffOn_adjusted_eq a n using 1 <;> ring

private theorem hasSum_adjusted_fourier
    (a x : ℝ) (hx₀ : -Real.pi < x) (hx₁ : x < Real.pi) :
    letI : Fact (0 < 2 * Real.pi) := ⟨two_pi_pos⟩
    HasSum
      (fun n : ℤ =>
        adjustedCoeff a n *
          fourier n ((x : ℝ) : AddCircle (2 * Real.pi)))
      (adjustedSinhC a x) := by
  letI : Fact (0 < 2 * Real.pi) := ⟨two_pi_pos⟩
  let F : C(AddCircle (2 * Real.pi), ℂ) :=
    ⟨periodizedAdjusted a, continuous_periodizedAdjusted a⟩
  have hcoeff : ∀ n : ℤ, fourierCoeff F n = adjustedCoeff a n := by
    intro n
    exact fourierCoeff_periodizedAdjusted_eq a n
  have hsummable : Summable (fourierCoeff F) :=
    (summable_adjustedCoeff a).congr
      (fun n => (hcoeff n).symm)
  have hs :=
    has_pointwise_sum_fourier_series_of_summable hsummable
      ((x : ℝ) : AddCircle (2 * Real.pi))
  simp_rw [hcoeff, smul_eq_mul] at hs
  have hxmem : x ∈ Set.Ioc (-Real.pi) (-Real.pi + 2 * Real.pi) := by
    constructor
    · exact hx₀
    · convert hx₁.le using 1 <;> ring
  have hF :
      F ((x : ℝ) : AddCircle (2 * Real.pi)) =
        adjustedSinhC a x := by
    change periodizedAdjusted a
        ((x : ℝ) : AddCircle (2 * Real.pi)) =
      adjustedSinhC a x
    unfold periodizedAdjusted
    rw [AddCircle.liftIoc_coe_apply hxmem]
  rw [hF] at hs
  exact hs

private theorem adjustedCoeff_neg (a : ℝ) (n : ℤ) :
    adjustedCoeff a (-n) = -adjustedCoeff a n := by
  simp [adjustedCoeff]
  have hsign :
      ((-1 : ℂ) ^ n)⁻¹ = (-1 : ℂ) ^ n := by
    simp only [neg_one_zpow_eq_ite]
    split_ifs <;> norm_num
  rw [hsign]
  ring

private theorem fourier_sub_pair (n : ℕ) (x : ℝ) :
    letI : Fact (0 < 2 * Real.pi) := ⟨two_pi_pos⟩
    fourier (n : ℤ)
          ((x : ℝ) : AddCircle (2 * Real.pi)) -
        fourier (-(n : ℤ))
          ((x : ℝ) : AddCircle (2 * Real.pi)) =
      (2 * Complex.I * Real.sin ((n : ℝ) * x) : ℂ) := by
  letI : Fact (0 < 2 * Real.pi) := ⟨two_pi_pos⟩
  rw [fourier_coe_apply, fourier_coe_apply]
  push_cast
  have hpos :
      2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) *
          (x : ℂ) / (2 * (Real.pi : ℂ)) =
        (n : ℂ) * (x : ℂ) * Complex.I := by
    field_simp [Real.pi_ne_zero]
  have hneg :
      2 * (Real.pi : ℂ) * Complex.I * (-(n : ℂ)) *
          (x : ℂ) / (2 * (Real.pi : ℂ)) =
        -((n : ℂ) * (x : ℂ) * Complex.I) := by
    field_simp [Real.pi_ne_zero]
  rw [hpos, hneg]
  rw [Complex.exp_mul_I,
    show -((n : ℂ) * (x : ℂ) * Complex.I) =
      (-((n : ℂ) * (x : ℂ))) * Complex.I by ring,
    Complex.exp_mul_I]
  rw [Complex.cos_neg, Complex.sin_neg]
  push_cast
  ring

private theorem hasSum_adjusted_tail
    (a x : ℝ) (hx₀ : -Real.pi < x) (hx₁ : x < Real.pi) :
    HasSum
      (fun k : ℕ =>
        2 * slope a * a ^ 2 * (-1 : ℝ) ^ (k + 1) *
          Real.sin ((k + 1 : ℝ) * x) /
            ((k + 1 : ℝ) *
              ((k + 1 : ℝ) ^ 2 + a ^ 2)))
      (Real.sinh (a * x) - slope a * x) := by
  letI : Fact (0 < 2 * Real.pi) := ⟨two_pi_pos⟩
  have hp :=
    (hasSum_adjusted_fourier a x hx₀ hx₁).nat_add_neg
  have ht := (hasSum_nat_add_iff' 1).mpr hp
  have hc :
      HasSum
        (fun k : ℕ =>
          ((2 * slope a * a ^ 2 * (-1 : ℝ) ^ (k + 1) *
            Real.sin ((k + 1 : ℝ) * x) /
              ((k + 1 : ℝ) *
                ((k + 1 : ℝ) ^ 2 + a ^ 2)) : ℝ) : ℂ))
        (adjustedSinhC a x) := by
    convert ht using 1
    · funext k
      rw [adjustedCoeff_neg]
      push_cast
      have hpair := fourier_sub_pair (k + 1) x
      push_cast at hpair
      rw [show
          adjustedCoeff a ((k : ℤ) + 1) *
                fourier ((k : ℤ) + 1)
                  ((x : ℝ) : AddCircle (2 * Real.pi)) +
              -adjustedCoeff a ((k : ℤ) + 1) *
                fourier (-((k : ℤ) + 1))
                  ((x : ℝ) : AddCircle (2 * Real.pi)) =
            adjustedCoeff a ((k : ℤ) + 1) *
              (fourier ((k : ℤ) + 1)
                  ((x : ℝ) : AddCircle (2 * Real.pi)) -
                fourier (-((k : ℤ) + 1))
                  ((x : ℝ) : AddCircle (2 * Real.pi))) by ring,
        hpair]
      unfold adjustedCoeff
      push_cast
      field_simp
      rw [Complex.I_sq]
      rw [show (k : ℤ) + 1 = ((k + 1 : ℕ) : ℤ) by omega,
        zpow_natCast]
      ring
    · simp [adjustedCoeff]
  have hr := Complex.reCLM.hasSum hc
  simpa only [Complex.reCLM_apply, Complex.ofReal_re,
    Complex.sub_re, Complex.sinh_ofReal_re,
    Complex.sin_ofReal_re, adjustedSinhC] using hr

private theorem hasSum_sawtooth
    (x : ℝ) (hx₀ : -Real.pi < x) (hx₁ : x < Real.pi) :
    HasSum
      (fun k : ℕ =>
        (-1 : ℝ) ^ (k + 2) *
          Real.sin ((k + 1 : ℝ) * x) / (k + 1 : ℝ))
      (x / 2) (SummationFilter.conditional ℕ) := by
  let y : ℝ := x + Real.pi
  have hy₀ : 0 < y := by
    dsimp [y]
    linarith
  have hy₂ : y < 2 * Real.pi := by
    dsimp [y]
    linarith
  have hyneg : -(2 * Real.pi) < y := by
    linarith [Real.pi_pos]
  have hcosne : Real.cos y ≠ 1 := by
    intro h
    have hyzero :=
      (Real.cos_eq_one_iff_of_lt_of_lt hyneg hy₂).mp h
    linarith
  have hcoslt : Real.cos y < 1 :=
    lt_of_le_of_ne (Real.cos_le_one y) hcosne
  let q : ℂ := Complex.exp ((y : ℂ) * Complex.I)
  have hqnorm : ‖q‖ = 1 := by
    simpa [q] using Complex.norm_exp_ofReal_mul_I y
  have hqne : q ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp [q, Complex.exp_mul_I] at hre
    exact hcosne hre
  have hqre : q.re = Real.cos y := by
    dsimp [q]
    rw [Complex.exp_mul_I]
    simp [Complex.cos_ofReal_re, Complex.sin_ofReal_re]
  have hslit : 1 - q ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    left
    change 0 < 1 - q.re
    rw [hqre]
    linarith
  let θ : ℝ := y / 2 - Real.pi / 2
  have hθ : θ ∈ Set.Ioc (-Real.pi) Real.pi := by
    constructor <;> dsimp [θ] <;> linarith [Real.pi_pos]
  have hsin : 0 < Real.sin (y / 2) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · linarith
    · linarith
  have hfactor :
      1 - q =
        ((2 * Real.sin (y / 2) : ℝ) : ℂ) *
          (Complex.cos (θ : ℂ) +
            Complex.sin (θ : ℂ) * Complex.I) := by
    dsimp [q]
    rw [Complex.exp_mul_I,
      ← Complex.ofReal_cos y, ← Complex.ofReal_sin y,
      ← Complex.ofReal_cos θ, ← Complex.ofReal_sin θ]
    rw [show y = 2 * (y / 2) by ring,
      Real.cos_two_mul, Real.sin_two_mul]
    simp [θ, Real.cos_sub, Real.sin_sub]
    push_cast
    have htrig :=
      Complex.sin_sq_add_cos_sq (((y / 2 : ℝ) : ℂ))
    have hycast :
        (((y / 2 : ℝ) : ℂ)) = (y : ℂ) / 2 := by
      push_cast
      rfl
    rw [hycast] at htrig
    linear_combination -2 * htrig
  have harg : Complex.arg (1 - q) = θ := by
    rw [hfactor]
    exact Complex.arg_mul_cos_add_sin_mul_I
      (mul_pos two_pos hsin) hθ
  have hlogim :
      (-Complex.log (1 - q)).im = -x / 2 := by
    simp only [Complex.neg_im, Complex.log_im, harg]
    dsimp [θ, y]
    ring
  let w : ℕ → ℝ := fun k => 1 / (k + 1 : ℝ)
  let z : ℕ → ℝ := fun k => Real.sin ((k + 1 : ℝ) * y)
  let u : ℕ → ℝ := fun k => w k * z k
  have hwanti : Antitone w := by
    apply antitone_nat_of_succ_le
    intro k
    dsimp [w]
    exact one_div_le_one_div_of_le (by positivity) (by norm_num)
  have hwzero : Tendsto w atTop (𝓝 0) := by
    have htop :
        Tendsto (fun k : ℕ => (k : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right atTop 1
        tendsto_natCast_atTop_atTop
    simpa [w, one_div] using tendsto_inv_atTop_zero.comp htop
  have hqpow_im (k : ℕ) :
      (q ^ (k + 1)).im =
        Real.sin ((k + 1 : ℝ) * y) := by
    dsimp [q]
    rw [← Complex.exp_nat_mul]
    rw [show ((k + 1 : ℕ) : ℂ) * ((y : ℂ) * Complex.I) =
        ((((k + 1 : ℕ) : ℝ) * y : ℝ) : ℂ) * Complex.I by
          push_cast
          ring]
    rw [Complex.exp_mul_I]
    simp only [Complex.add_im, Complex.mul_im,
      Complex.cos_ofReal_im, Complex.sin_ofReal_re,
      Complex.I_re, Complex.I_im, zero_add, mul_one,
      mul_zero, add_zero]
    push_cast
    rfl
  have hqbound (N : ℕ) :
      ‖∑ k ∈ Finset.range N, q ^ (k + 1)‖ ≤
        2 / ‖q - 1‖ := by
    have hgeom :
        (∑ k ∈ Finset.range N, q ^ (k + 1)) =
          q * ((q ^ N - 1) / (q - 1)) := by
      calc
        (∑ k ∈ Finset.range N, q ^ (k + 1)) =
            q * ∑ k ∈ Finset.range N, q ^ k := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro k hk
              rw [pow_succ']
        _ = q * ((q ^ N - 1) / (q - 1)) := by
          rw [geom_sum_eq hqne]
    rw [hgeom, norm_mul, norm_div, hqnorm, one_mul]
    apply div_le_div_of_nonneg_right
    · calc
        ‖q ^ N - 1‖ ≤ ‖q ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = 2 := by rw [norm_pow, hqnorm]; norm_num
    · positivity
  have hzbound (N : ℕ) :
      ‖∑ k ∈ Finset.range N, z k‖ ≤
        2 / ‖q - 1‖ := by
    have him :
        (∑ k ∈ Finset.range N, q ^ (k + 1)).im =
          ∑ k ∈ Finset.range N, z k := by
      change Complex.imCLM
          (∑ k ∈ Finset.range N, q ^ (k + 1)) =
        ∑ k ∈ Finset.range N, z k
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro k hk
      exact hqpow_im k
    calc
      ‖∑ k ∈ Finset.range N, z k‖ =
          |(∑ k ∈ Finset.range N, q ^ (k + 1)).im| := by
            rw [Real.norm_eq_abs, him]
      _ ≤ ‖∑ k ∈ Finset.range N, q ^ (k + 1)‖ :=
        Complex.abs_im_le_norm _
      _ ≤ 2 / ‖q - 1‖ := hqbound N
  have hcauchy :
      CauchySeq (fun N => ∑ k ∈ Finset.range N, u k) := by
    convert hwanti.cauchySeq_series_mul_of_tendsto_zero_of_bounded
      hwzero hzbound using 1
  obtain ⟨l, hl⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hradial (r : ℝ) (hr₀ : 0 < r) (hr₁ : r < 1) :
      (∑' k : ℕ, u k * r ^ k) =
        (-Complex.log (1 - (r : ℂ) * q) / (r : ℂ)).im := by
    have hrnorm : ‖(r : ℂ) * q‖ < 1 := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hr₀, hqnorm, mul_one]
      exact hr₁
    have hlog :=
      Complex.hasSum_taylorSeries_neg_log hrnorm
    have hshift :
        HasSum
          (fun k : ℕ =>
            ((r : ℂ) * q) ^ (k + 1) / (k + 1 : ℂ))
          (-Complex.log (1 - (r : ℂ) * q)) := by
      simpa using (hasSum_nat_add_iff' 1).mpr hlog
    have hc :=
      Complex.imCLM.hasSum
        (hshift.mul_left ((r : ℂ)⁻¹))
    calc
      (∑' k : ℕ, u k * r ^ k) =
          ∑' k : ℕ,
            Complex.imCLM
              ((r : ℂ)⁻¹ *
                (((r : ℂ) * q) ^ (k + 1) /
                  (k + 1 : ℂ))) := by
            apply tsum_congr
            intro k
            have heqC :
                (r : ℂ)⁻¹ *
                    (((r : ℂ) * q) ^ (k + 1) /
                      (k + 1 : ℂ)) =
                  (((r ^ k / (k + 1 : ℝ) : ℝ) : ℂ) *
                    q ^ (k + 1)) := by
              rw [mul_pow]
              push_cast
              field_simp [hr₀.ne']
              rw [pow_succ']
              ring
            rw [heqC]
            simp only [Complex.imCLM_apply,
              Complex.mul_im, Complex.ofReal_re,
              Complex.ofReal_im, zero_mul, add_zero,
              hqpow_im]
            dsimp [u, w, z]
            ring
      _ = Complex.imCLM
          ((r : ℂ)⁻¹ *
            -Complex.log (1 - (r : ℂ) * q)) :=
        hc.tsum_eq
      _ = (-Complex.log (1 - (r : ℂ) * q) /
          (r : ℂ)).im := by
        simp [Complex.imCLM_apply, div_eq_mul_inv,
          mul_comm]
  have hab :=
    Real.tendsto_tsum_powerSeries_nhdsWithin_lt hl
  have hinner :
      ContinuousAt (fun r : ℝ => (1 : ℂ) - (r : ℂ) * q) 1 := by
    fun_prop
  have hlogcont :
      ContinuousAt
        (fun r : ℝ =>
          Complex.log ((1 : ℂ) - (r : ℂ) * q)) 1 := by
    apply hinner.clog
    simpa using hslit
  have hfull :
      ContinuousAt
        (fun r : ℝ =>
          (-Complex.log (1 - (r : ℂ) * q) / (r : ℂ)).im) 1 := by
    exact Complex.continuous_im.continuousAt.comp
      (hlogcont.neg.div
        (Complex.ofRealCLM.continuous.continuousAt)
        (by norm_num))
  have heq :
      ∀ᶠ r : ℝ in 𝓝[<] (1 : ℝ),
        (∑' k : ℕ, u k * r ^ k) =
          (-Complex.log (1 - (r : ℂ) * q) / (r : ℂ)).im := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_gt_nhds (zero_lt_one : (0 : ℝ) < 1)).filter_mono
        inf_le_left] with r hr₁ hr₀
    exact hradial r hr₀ hr₁
  have hab' :
      Tendsto
        (fun r : ℝ =>
          (-Complex.log (1 - (r : ℂ) * q) / (r : ℂ)).im)
        (𝓝[<] (1 : ℝ)) (𝓝 l) :=
    hab.congr' heq
  have htarget :
      Tendsto
        (fun r : ℝ =>
          (-Complex.log (1 - (r : ℂ) * q) / (r : ℂ)).im)
        (𝓝[<] (1 : ℝ))
        (𝓝 ((-Complex.log (1 - q)).im)) := by
    simpa using hfull.tendsto.mono_left inf_le_left
  have hlvalue : l = -x / 2 := by
    rw [← hlogim]
    exact tendsto_nhds_unique hab' htarget
  have hu :
      HasSum u (-x / 2) (SummationFilter.conditional ℕ) := by
    rw [HasSum, SummationFilter.conditional_filter_eq_map_range,
      tendsto_map'_iff]
    simpa [Function.comp_def, hlvalue] using hl
  have hneg := hu.neg
  have hseries :
      HasSum
        (fun k : ℕ =>
          (-1 : ℝ) ^ (k + 2) *
            Real.sin ((k + 1 : ℝ) * x) / (k + 1 : ℝ))
        (-(-x / 2)) (SummationFilter.conditional ℕ) := by
    refine hneg.congr_fun ?_
    intro k
    dsimp [u, w, z, y]
    rw [show (k + 1 : ℝ) * (x + Real.pi) =
        (k + 1 : ℝ) * x + (k + 1 : ℕ) * Real.pi by
          push_cast
          ring,
      Real.sin_add_nat_mul_pi]
    rw [show k + 2 = (k + 1) + 1 by omega, pow_succ]
    ring
  convert hseries using 1 <;> ring

private theorem hasSum_sinh_series
    (a x : ℝ) (hx₀ : -Real.pi < x) (hx₁ : x < Real.pi) :
    HasSum
      (fun k : ℕ =>
        2 * Real.sinh (a * Real.pi) / Real.pi *
          ((-1 : ℝ) ^ (k + 2) *
            ((k + 1 : ℝ) * Real.sin ((k + 1 : ℝ) * x) /
              ((k + 1 : ℝ) ^ 2 + a ^ 2))))
      (Real.sinh (a * x))
      (SummationFilter.conditional ℕ) := by
  have hadj :
      HasSum
        (fun k : ℕ =>
          2 * slope a * a ^ 2 * (-1 : ℝ) ^ (k + 1) *
            Real.sin ((k + 1 : ℝ) * x) /
              ((k + 1 : ℝ) *
                ((k + 1 : ℝ) ^ 2 + a ^ 2)))
        (Real.sinh (a * x) - slope a * x)
        (SummationFilter.conditional ℕ) :=
    (hasSum_adjusted_tail a x hx₀ hx₁).mono_left
      (SummationFilter.conditional ℕ).le_atTop
  have hsaw :=
    (hasSum_sawtooth x hx₀ hx₁).mul_left
      (2 * slope a)
  have hsum := hadj.add hsaw
  have hseries :
      HasSum
        (fun k : ℕ =>
          2 * Real.sinh (a * Real.pi) / Real.pi *
            ((-1 : ℝ) ^ (k + 2) *
              ((k + 1 : ℝ) * Real.sin ((k + 1 : ℝ) * x) /
                ((k + 1 : ℝ) ^ 2 + a ^ 2))))
        ((Real.sinh (a * x) - slope a * x) +
          2 * slope a * (x / 2))
        (SummationFilter.conditional ℕ) := by
    refine hsum.congr_fun ?_
    intro k
    have hn : (k + 1 : ℝ) ≠ 0 := by positivity
    have hden : (k + 1 : ℝ) ^ 2 + a ^ 2 ≠ 0 := by
      positivity
    unfold slope
    rw [show k + 2 = (k + 1) + 1 by omega, pow_succ]
    field_simp [hn, hden, Real.pi_ne_zero]
    ring
  convert hseries using 1 <;> ring

theorem gap1 (a : ℝ) (f : ℝ → ℝ)
    (hf : ∀ x, f x = Real.sinh (a * x)) :
    Function.Odd f := by
  intro x
  rw [hf, hf]
  simp

theorem gap2 (c : ℕ → ℝ) (hc : ∀ n, c n = 0) :
    ∀ n : ℕ, c 0 = c n := by
  intro n
  rw [hc, hc]

theorem gap3 (c : ℕ → ℝ) (hc : ∀ n, c 0 = c n)
    (hc0 : c 0 = 0) :
    ∀ n : ℕ, c n = 0 := by
  intro n
  rw [← hc n, hc0]

theorem gap4 (c : ℕ → ℝ) (hc : ∀ n, c n = 0) :
    c 0 = 0 := by
  exact hc 0

theorem gap5 (a : ℝ) (s : ℕ → ℝ)
    (hs : ∀ n : ℕ, 1 ≤ n → s n = coefficientIntegral a n) :
    ∀ n : ℕ, 1 ≤ n → s n = coefficientIntegral a n := by
  exact hs

theorem gap6 (a : ℝ) (s : ℕ → ℝ)
    (hs : ∀ n : ℕ, 1 ≤ n → s n = coefficientIntegral a n) :
    ∀ n : ℕ, 1 ≤ n → s n = firstParts a n := by
  intro n hn
  rw [hs n hn]
  unfold coefficientIntegral firstParts
  rw [sinh_sin_integral_parts a n hn]

theorem gap7 (a : ℝ) (s : ℕ → ℝ)
    (hs : ∀ n : ℕ, 1 ≤ n → s n = firstParts a n) :
    ∀ n : ℕ, 1 ≤ n → s n = reducedParts a n := by
  intro n hn
  rw [hs n hn]
  have hn0 : (n : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  unfold firstParts reducedParts
  rw [cos_cosh_integral_parts a n hn]
  simp only [Real.sinh_zero, Real.cos_zero, mul_zero, Real.cos_nat_mul_pi]
  field_simp [hn0]
  ring

theorem gap8 (a : ℝ) (s : ℕ → ℝ)
    (hs : ∀ n : ℕ, 1 ≤ n → s n = coefficientIntegral a n) :
    ∀ n : ℕ, 1 ≤ n →
      reducedParts a n =
        2 * (-1 : ℝ) ^ (n + 1) / ((n : ℝ) * Real.pi) *
            Real.sinh (a * Real.pi) -
          a ^ 2 / (n : ℝ) ^ 2 * s n := by
  intro n hn
  rw [hs n hn]
  unfold reducedParts coefficientIntegral
  ring

theorem gap9 (a : ℝ) (s : ℕ → ℝ)
    (hs : ∀ n : ℕ, 1 ≤ n → s n = coefficientIntegral a n) :
    ∀ n : ℕ, 1 ≤ n →
      s n =
        2 * (-1 : ℝ) ^ (n + 1) / ((n : ℝ) * Real.pi) *
            Real.sinh (a * Real.pi) -
          a ^ 2 / (n : ℝ) ^ 2 * s n := by
  intro n hn
  calc
    s n = reducedParts a n := gap7 a s (gap6 a s hs) n hn
    _ = 2 * (-1 : ℝ) ^ (n + 1) / ((n : ℝ) * Real.pi) *
          Real.sinh (a * Real.pi) -
        a ^ 2 / (n : ℝ) ^ 2 * s n := gap8 a s hs n hn

theorem gap10 (a : ℝ) (s : ℕ → ℝ)
    (hs : ∀ n : ℕ, 1 ≤ n → s n = coefficientIntegral a n) :
    ∀ n : ℕ, 1 ≤ n →
      s n =
        ((-1 : ℝ) ^ (n + 1) * 2 * (n : ℝ)) /
            (((n : ℝ) ^ 2 + a ^ 2) * Real.pi) *
          Real.sinh (a * Real.pi) := by
  intro n hn
  have hn0 : (n : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have hden : (n : ℝ) ^ 2 + a ^ 2 ≠ 0 := by
    positivity
  have hrec := gap9 a s hs n hn
  field_simp [hn0, Real.pi_ne_zero, hden] at hrec ⊢
  nlinarith

theorem gap11 (a : ℝ) (f : ℝ → ℝ)
    (hf : ∀ x, f x = Real.sinh (a * x)) :
    ∀ x, -Real.pi < x → x < Real.pi →
      ProofGap.SeriesHasSum
        (fun k : ℕ =>
          2 * Real.sinh (a * Real.pi) / Real.pi *
            ((-1 : ℝ) ^ (k + 2) *
              ((k + 1 : ℝ) * Real.sin ((k + 1 : ℝ) * x) /
                ((k + 1 : ℝ) ^ 2 + a ^ 2))))
        (f x) := by
  intro x hx₀ hx₁
  rw [hf x]
  exact hasSum_sinh_series a x hx₀ hx₁

theorem gap12 (a x : ℝ) (hx₀ : -Real.pi < x)
    (hx₁ : x < Real.pi) :
    ProofGap.SeriesHasSum
      (fun k : ℕ =>
        2 * Real.sinh (a * Real.pi) / Real.pi *
          ((-1 : ℝ) ^ (k + 2) *
            ((k + 1 : ℝ) * Real.sin ((k + 1 : ℝ) * x) /
              ((k + 1 : ℝ) ^ 2 + a ^ 2))))
      (Real.sinh (a * x)) := by
  exact hasSum_sinh_series a x hx₀ hx₁

theorem gap13 (a : ℝ) (f : ℝ → ℝ)
    (hf : ∀ x, f x = Real.sinh (a * x)) :
    ∀ x, f x = Real.sinh (a * x) := by
  exact hf

end

end ProofGap.Exercise2947
