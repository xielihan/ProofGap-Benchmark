import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Summable
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

namespace ProofGap.Exercise2945

noncomputable section

open scoped Interval

def Nonintegral (a : ℝ) : Prop :=
  ∀ z : ℤ, a ≠ (z : ℝ)

def coefficientIntegral (a : ℝ) (n : ℕ) : ℝ :=
  2 / Real.pi *
    ∫ x in 0..Real.pi,
      Real.cos (a * x) * Real.cos ((n : ℝ) * x)

def productToSumIntegral (a : ℝ) (n : ℕ) : ℝ :=
  1 / Real.pi *
    ∫ x in 0..Real.pi,
      (Real.cos (((n : ℝ) + a) * x) +
        Real.cos (((n : ℝ) - a) * x))

def fourierSeries (a x : ℝ) : ℝ :=
  2 * Real.sin (a * Real.pi) / Real.pi *
    (1 / (2 * a) +
      ∑' k : ℕ,
        (-1 : ℝ) ^ (k + 2) *
          (a * Real.cos ((k + 1 : ℝ) * x) /
            ((k + 1 : ℝ) ^ 2 - a ^ 2)))

private theorem nonintegral_ne_zero {a : ℝ} (ha : Nonintegral a) :
    a ≠ 0 := by
  simpa using ha 0

private theorem integral_cos_mul (c : ℝ) (hc : c ≠ 0) :
    (∫ x in (0 : ℝ)..Real.pi, Real.cos (c * x)) =
      Real.sin (c * Real.pi) / c := by
  have hderiv : ∀ x : ℝ,
      HasDerivAt (fun y : ℝ => Real.sin (c * y) / c)
        (Real.cos (c * x)) x := by
    intro x
    have hinner : HasDerivAt (fun y : ℝ => c * y) c x := by
      simpa only [id_eq, mul_one] using (hasDerivAt_id x).const_mul c
    convert
      ((Real.hasDerivAt_sin (c * x)).comp x hinner).div_const c using 1
    field_simp [hc]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hderiv x)
    ((Real.continuous_cos.comp
      (continuous_const.mul continuous_id)).intervalIntegrable 0 Real.pi)]
  simp

private theorem sin_nat_add_mul_pi (a : ℝ) (n : ℕ) :
    Real.sin (((n : ℝ) + a) * Real.pi) =
      (-1 : ℝ) ^ n * Real.sin (a * Real.pi) := by
  rw [add_mul, Real.sin_add, Real.sin_nat_mul_pi,
    Real.cos_nat_mul_pi]
  ring

private theorem sin_nat_sub_mul_pi (a : ℝ) (n : ℕ) :
    Real.sin (((n : ℝ) - a) * Real.pi) =
      -(-1 : ℝ) ^ n * Real.sin (a * Real.pi) := by
  rw [sub_mul, Real.sin_sub, Real.sin_nat_mul_pi,
    Real.cos_nat_mul_pi]
  ring

private def shiftCosC (a x : ℝ) : ℂ :=
  Real.cos (a * (x - Real.pi))

private def shiftCosC' (a x : ℝ) : ℂ :=
  (-(a * Real.sin (a * (x - Real.pi))) : ℝ)

private def shiftCosC'' (a x : ℝ) : ℂ :=
  (-(a ^ 2 * Real.cos (a * (x - Real.pi))) : ℝ)

private theorem hasDerivAt_shiftCosC (a x : ℝ) :
    HasDerivAt (shiftCosC a) (shiftCosC' a x) x := by
  have hinner :
      HasDerivAt (fun y : ℝ => a * (y - Real.pi)) a x := by
    convert ((hasDerivAt_id x).sub_const Real.pi).const_mul a using 1 <;>
      ring
  have hreal :
      HasDerivAt (fun y : ℝ => Real.cos (a * (y - Real.pi)))
        (-Real.sin (a * (x - Real.pi)) * a) x :=
    by
      simpa only [Function.comp_apply] using
        (Real.hasDerivAt_cos (a * (x - Real.pi))).comp x hinner
  convert hreal.ofReal_comp using 1 <;>
    simp [shiftCosC, shiftCosC'] <;> ring

private theorem hasDerivAt_shiftCosC' (a x : ℝ) :
    HasDerivAt (shiftCosC' a) (shiftCosC'' a x) x := by
  have hinner :
      HasDerivAt (fun y : ℝ => a * (y - Real.pi)) a x := by
    convert ((hasDerivAt_id x).sub_const Real.pi).const_mul a using 1 <;>
      ring
  have hreal :
      HasDerivAt (fun y : ℝ => -(a * Real.sin (a * (y - Real.pi))))
        (-(a * (Real.cos (a * (x - Real.pi)) * a))) x :=
    by
      simpa only [Function.comp_apply] using
        (((Real.hasDerivAt_sin (a * (x - Real.pi))).comp x hinner).const_mul a).neg
  change HasDerivAt
    (fun y : ℝ => ((-(a * Real.sin (a * (y - Real.pi))) : ℝ) : ℂ))
    (((-(a ^ 2 * Real.cos (a * (x - Real.pi))) : ℝ) : ℂ)) x
  convert hreal.ofReal_comp using 1
  norm_cast
  ring

private theorem two_pi_pos : (0 : ℝ) < 2 * Real.pi := by
  positivity

private theorem fourierCoeffOn_shiftCosC_eq
    (a : ℝ) (ha : Nonintegral a) (n : ℤ) :
    fourierCoeffOn two_pi_pos (shiftCosC a) n =
      (a * Real.sin (a * Real.pi) /
        (Real.pi * (a ^ 2 - (n : ℝ) ^ 2)) : ℝ) := by
  have ha0 : a ≠ 0 := by simpa using ha 0
  by_cases hn : n = 0
  · subst n
    rw [fourierCoeffOn_eq_integral]
    simp only [smul_eq_mul, Complex.real_smul,
      Complex.ofReal_div, Complex.ofReal_one]
    simp only [neg_zero, fourier_zero, one_mul, shiftCosC,
      Int.cast_zero, zero_pow, sub_zero]
    rw [intervalIntegral.integral_ofReal]
    have hderiv : ∀ x : ℝ,
        HasDerivAt
          (fun y : ℝ => Real.sin (a * (y - Real.pi)) / a)
          (Real.cos (a * (x - Real.pi))) x := by
      intro x
      have hinner :
          HasDerivAt (fun y : ℝ => a * (y - Real.pi)) a x := by
        convert ((hasDerivAt_id x).sub_const Real.pi).const_mul a using 1 <;>
          ring
      convert
        ((Real.hasDerivAt_sin (a * (x - Real.pi))).comp x hinner).div_const a
          using 1
      field_simp [ha0]
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => hderiv x)
      ((Real.continuous_cos.comp
        (continuous_const.mul
          (continuous_id.sub continuous_const))).intervalIntegrable _ _)]
    change ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ((Real.sin (a * (2 * Real.pi - Real.pi)) / a -
          Real.sin (a * (0 - Real.pi)) / a : ℝ) : ℂ) =
      ((a * Real.sin (a * Real.pi) : ℝ) : ℂ) /
        ((Real.pi * (a ^ 2 - (0 : ℝ) ^ 2) : ℝ) : ℂ)
    norm_cast
    simp
    field_simp [ha0, Real.pi_ne_zero]
    ring_nf
  · have hncast : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    have ha_n : a ≠ (n : ℝ) := by
      simpa using ha n
    have ha_neg_n : a ≠ -(n : ℝ) := by
      simpa using ha (-n)
    have hplus : a + (n : ℝ) ≠ 0 := by
      intro h
      apply ha_neg_n
      linarith
    have hden : a ^ 2 - (n : ℝ) ^ 2 ≠ 0 := by
      rw [sq_sub_sq]
      exact mul_ne_zero hplus (sub_ne_zero.mpr ha_n)
    have h1 := fourierCoeffOn_of_hasDerivAt two_pi_pos hn
      (fun x _ => hasDerivAt_shiftCosC a x)
      ((by
        unfold shiftCosC'
        fun_prop : Continuous (shiftCosC' a)).intervalIntegrable _ _)
    have h2 := fourierCoeffOn_of_hasDerivAt two_pi_pos hn
      (fun x _ => hasDerivAt_shiftCosC' a x)
      ((by
        unfold shiftCosC''
        fun_prop : Continuous (shiftCosC'' a)).intervalIntegrable _ _)
    have hsecond :
        fourierCoeffOn two_pi_pos (shiftCosC'' a) n =
          (-(a ^ 2) : ℂ) *
            fourierCoeffOn two_pi_pos (shiftCosC a) n := by
      rw [show shiftCosC'' a =
          fun x => (-(a ^ 2) : ℂ) * shiftCosC a x by
            funext x
            simp [shiftCosC'', shiftCosC],
        fourierCoeffOn.const_mul]
    rw [h2, hsecond] at h1
    have htwopi : 2 * Real.pi - Real.pi = Real.pi := by ring
    have hnegpi : (0 : ℝ) - Real.pi = -Real.pi := by ring
    simp [shiftCosC, shiftCosC', htwopi, hnegpi,
      Real.cos_neg, Real.sin_neg, fourier_coe_apply] at h1
    generalize hC :
        fourierCoeffOn _ (shiftCosC a) n = C at h1
    field_simp [hncast, Real.pi_ne_zero,
      Complex.I_ne_zero] at h1
    rw [Complex.I_sq] at h1
    ring_nf at h1
    rw [show (Real.pi : ℂ) * (a : ℂ) =
      (a : ℂ) * Real.pi by ring] at h1
    push_cast
    rw [eq_div_iff]
    · rw [← sub_eq_zero]
      calc
        C * ((Real.pi : ℂ) * ((a : ℂ) ^ 2 - (n : ℂ) ^ 2)) -
            (a : ℂ) * Complex.sin ((a : ℂ) * Real.pi) =
            (-1 / 2 : ℂ) *
              (C * (n : ℂ) ^ 2 * Real.pi * 2 -
                (C * Real.pi * (a : ℂ) ^ 2 * 2 -
                  (a : ℂ) * Complex.sin ((a : ℂ) * Real.pi) * 2)) := by
                    ring
        _ = 0 := by
          apply mul_eq_zero_of_right
          exact sub_eq_zero.mpr h1
    · exact_mod_cast mul_ne_zero Real.pi_ne_zero hden

private def coeff (a : ℝ) (n : ℤ) : ℂ :=
  (a * Real.sin (a * Real.pi) /
    (Real.pi * (a ^ 2 - (n : ℝ) ^ 2)) : ℝ)

private theorem summable_coeff (a : ℝ) (ha : Nonintegral a) :
    Summable (coeff a) := by
  have hbase :=
    EisensteinSeries.summable_linear_sub_mul_linear_add (a : ℂ) 1 1
  have hscaled :=
    hbase.mul_left ((a * Real.sin (a * Real.pi) / Real.pi : ℝ) : ℂ)
  apply hscaled.congr
  intro n
  unfold coeff
  have ha_n : a ≠ (n : ℝ) := by
    simpa using ha n
  have ha_neg_n : a ≠ -(n : ℝ) := by
    simpa using ha (-n)
  have hplus : a + (n : ℝ) ≠ 0 := by
    intro h
    apply ha_neg_n
    linarith
  have hden : a ^ 2 - (n : ℝ) ^ 2 ≠ 0 := by
    rw [sq_sub_sq]
    exact mul_ne_zero hplus (sub_ne_zero.mpr ha_n)
  push_cast
  simp only [Int.cast_one, one_mul]
  field_simp [Real.pi_ne_zero, hden]
  ring

private def periodizedCos (a : ℝ) : AddCircle (2 * Real.pi) → ℂ :=
  letI : Fact (0 < 2 * Real.pi) := ⟨two_pi_pos⟩
  AddCircle.liftIco (2 * Real.pi) 0 (shiftCosC a)

private theorem continuous_periodizedCos (a : ℝ) :
    Continuous (periodizedCos a) := by
  letI : Fact (0 < 2 * Real.pi) := ⟨two_pi_pos⟩
  unfold periodizedCos
  apply AddCircle.liftIco_zero_continuous
  · simp only [shiftCosC, sub_zero, Complex.ofReal_inj]
    rw [show a * (0 - Real.pi) = -(a * Real.pi) by ring,
      show a * (2 * Real.pi - Real.pi) = a * Real.pi by ring,
      Real.cos_neg]
  · exact (by
      unfold shiftCosC
      fun_prop : Continuous (shiftCosC a)).continuousOn

private theorem fourierCoeff_periodizedCos_eq
    (a : ℝ) (ha : Nonintegral a) (n : ℤ) :
    letI : Fact (0 < 2 * Real.pi) := ⟨two_pi_pos⟩
    fourierCoeff (periodizedCos a) n = coeff a n := by
  letI : Fact (0 < 2 * Real.pi) := ⟨two_pi_pos⟩
  rw [periodizedCos, fourierCoeff_liftIco_eq]
  simpa [coeff] using fourierCoeffOn_shiftCosC_eq a ha n

private theorem hasSum_coeff_fourier
    (a x : ℝ) (ha : Nonintegral a)
    (hx₀ : -Real.pi < x) (hx₁ : x < Real.pi) :
    letI : Fact (0 < 2 * Real.pi) := ⟨two_pi_pos⟩
    HasSum
      (fun n : ℤ =>
        coeff a n * fourier n ((x + Real.pi : ℝ) :
          AddCircle (2 * Real.pi)))
      (Real.cos (a * x) : ℂ) := by
  letI : Fact (0 < 2 * Real.pi) := ⟨two_pi_pos⟩
  let F : C(AddCircle (2 * Real.pi), ℂ) :=
    ⟨periodizedCos a, continuous_periodizedCos a⟩
  have hcoeff : ∀ n : ℤ, fourierCoeff F n = coeff a n := by
    intro n
    exact fourierCoeff_periodizedCos_eq a ha n
  have hsummable : Summable (fourierCoeff F) :=
    (summable_coeff a ha).congr (fun n => (hcoeff n).symm)
  have hs :=
    has_pointwise_sum_fourier_series_of_summable hsummable
      ((x + Real.pi : ℝ) : AddCircle (2 * Real.pi))
  simp_rw [hcoeff, smul_eq_mul] at hs
  have hy :
      x + Real.pi ∈ Set.Ico (0 : ℝ) (0 + 2 * Real.pi) := by
    constructor
    · linarith [Real.pi_pos]
    · simp only [zero_add]
      linarith [Real.pi_pos]
  have hF :
      F ((x + Real.pi : ℝ) : AddCircle (2 * Real.pi)) =
        (Real.cos (a * x) : ℂ) := by
    change periodizedCos a
        ((x + Real.pi : ℝ) : AddCircle (2 * Real.pi)) =
      (Real.cos (a * x) : ℂ)
    unfold periodizedCos
    rw [AddCircle.liftIco_coe_apply hy]
    simp [shiftCosC]
  rw [hF] at hs
  exact hs

private theorem coeff_neg (a : ℝ) (n : ℤ) :
    coeff a (-n) = coeff a n := by
  simp [coeff]

private theorem fourier_pair (n : ℕ) (x : ℝ) :
    letI : Fact (0 < 2 * Real.pi) := ⟨two_pi_pos⟩
    fourier (n : ℤ)
          ((x + Real.pi : ℝ) : AddCircle (2 * Real.pi)) +
        fourier (-(n : ℤ))
          ((x + Real.pi : ℝ) : AddCircle (2 * Real.pi)) =
      ((2 * (-1 : ℝ) ^ n * Real.cos ((n : ℝ) * x) : ℝ) : ℂ) := by
  letI : Fact (0 < 2 * Real.pi) := ⟨two_pi_pos⟩
  rw [fourier_coe_apply, fourier_coe_apply]
  have hpos :
      2 * (Real.pi : ℂ) * Complex.I * ((n : ℤ) : ℂ) *
            (((x + Real.pi : ℝ)) : ℂ) /
              (((2 * Real.pi : ℝ)) : ℂ) =
        (((n : ℝ) * (x + Real.pi) : ℝ) : ℂ) * Complex.I := by
    push_cast
    field_simp [Real.pi_ne_zero]
  have hneg :
      2 * (Real.pi : ℂ) * Complex.I * ((-(n : ℤ) : ℤ) : ℂ) *
            (((x + Real.pi : ℝ)) : ℂ) /
              (((2 * Real.pi : ℝ)) : ℂ) =
        -(((n : ℝ) * (x + Real.pi) : ℝ) : ℂ) * Complex.I := by
    push_cast
    field_simp [Real.pi_ne_zero]
  rw [hpos, hneg, ← Complex.two_cos, ← Complex.ofReal_cos]
  norm_cast
  rw [show (n : ℝ) * (x + Real.pi) =
      (n : ℝ) * x + n * Real.pi by push_cast; ring,
    Real.cos_add_nat_mul_pi]
  push_cast
  ring

private theorem hasSum_paired_tail
    (a x : ℝ) (ha : Nonintegral a)
    (hx₀ : -Real.pi < x) (hx₁ : x < Real.pi) :
    letI : Fact (0 < 2 * Real.pi) := ⟨two_pi_pos⟩
    HasSum
      (fun k : ℕ =>
        coeff a (k + 1 : ℕ) *
          (fourier (k + 1 : ℕ)
              ((x + Real.pi : ℝ) : AddCircle (2 * Real.pi)) +
            fourier (-(k + 1 : ℤ))
              ((x + Real.pi : ℝ) : AddCircle (2 * Real.pi))))
      ((Real.cos (a * x) : ℂ) - coeff a 0) := by
  letI : Fact (0 < 2 * Real.pi) := ⟨two_pi_pos⟩
  have hp :=
    (hasSum_coeff_fourier a x ha hx₀ hx₁).nat_add_neg
  have ht := (hasSum_nat_add_iff' 1).mpr hp
  convert ht using 1 with k
  · funext k
    rw [coeff_neg]
    push_cast
    ring
  · simp [coeff, fourier_zero]

private theorem hasSum_fourierSeries_tail
    (a x : ℝ) (ha : Nonintegral a)
    (hx₀ : -Real.pi < x) (hx₁ : x < Real.pi) :
    HasSum
      (fun k : ℕ =>
        2 * Real.sin (a * Real.pi) / Real.pi *
          ((-1 : ℝ) ^ (k + 2) *
            (a * Real.cos ((k + 1 : ℝ) * x) /
              ((k + 1 : ℝ) ^ 2 - a ^ 2))))
      (Real.cos (a * x) -
        Real.sin (a * Real.pi) / (a * Real.pi)) := by
  letI : Fact (0 < 2 * Real.pi) := ⟨two_pi_pos⟩
  have hp := hasSum_paired_tail a x ha hx₀ hx₁
  have hc :
      HasSum
        (fun k : ℕ =>
          ((2 * Real.sin (a * Real.pi) / Real.pi *
            ((-1 : ℝ) ^ (k + 2) *
              (a * Real.cos ((k + 1 : ℝ) * x) /
                ((k + 1 : ℝ) ^ 2 - a ^ 2))) : ℝ) : ℂ))
        (((Real.cos (a * x) : ℂ) - coeff a 0)) := by
    refine hp.congr_fun ?_
    intro k
    have hpair :
        fourier ((k + 1 : ℕ) : ℤ)
              ((x + Real.pi : ℝ) : AddCircle (2 * Real.pi)) +
            fourier (-((k : ℤ) + 1))
              ((x + Real.pi : ℝ) : AddCircle (2 * Real.pi)) =
          ((2 * (-1 : ℝ) ^ (k + 1) *
            Real.cos ((k + 1 : ℝ) * x) : ℝ) : ℂ) := by
      convert fourier_pair (k + 1) x using 1 <;>
        push_cast <;> ring
    rw [hpair]
    unfold coeff
    norm_cast
    push_cast
    have ha_nat : a ≠ (k : ℝ) + 1 := by
      simpa using ha ((k : ℤ) + 1)
    have ha_neg_nat : a ≠ -((k : ℝ) + 1) := by
      simpa using ha (-((k : ℤ) + 1))
    have hplus : a + ((k : ℝ) + 1) ≠ 0 := by
      intro h
      apply ha_neg_nat
      linarith
    have hden : a ^ 2 - ((k : ℝ) + 1) ^ 2 ≠ 0 := by
      rw [sq_sub_sq]
      exact mul_ne_zero hplus (sub_ne_zero.mpr ha_nat)
    have hden' : ((k : ℝ) + 1) ^ 2 - a ^ 2 ≠ 0 := by
      intro h
      apply hden
      linarith
    rw [show k + 2 = (k + 1) + 1 by omega, pow_succ]
    field_simp [Real.pi_ne_zero, hden, hden']
    ring
  have hr := Complex.reCLM.hasSum hc
  have ha0 : a ≠ 0 := by simpa using ha 0
  simp only [Complex.reCLM_apply, Complex.ofReal_re,
    Complex.sub_re] at hr
  have hcoeff0 :
      (coeff a 0).re =
        Real.sin (a * Real.pi) / (a * Real.pi) := by
    unfold coeff
    simp only [Complex.ofReal_re]
    field_simp [ha0, Real.pi_ne_zero]
    ring
  rw [hcoeff0] at hr
  exact hr

private theorem fourierSeries_eq_cos
    (a x : ℝ) (ha : Nonintegral a)
    (hx₀ : -Real.pi < x) (hx₁ : x < Real.pi) :
    fourierSeries a x = Real.cos (a * x) := by
  have hs := hasSum_fourierSeries_tail a x ha hx₀ hx₁
  have hts := hs.tsum_eq
  unfold fourierSeries
  rw [mul_add, ← tsum_mul_left, hts]
  have ha0 : a ≠ 0 := by simpa using ha 0
  field_simp [ha0, Real.pi_ne_zero]
  ring

theorem gap1 (a : ℝ) (f : ℝ → ℝ) (ha : Nonintegral a)
    (hf : ∀ x, f x = Real.cos (a * x)) :
    Function.Even f := by
  intro x
  rw [hf, hf]
  simp

theorem gap2 (a : ℝ) (f : ℝ → ℝ) (s : ℕ → ℝ)
    (hf : ∀ x, f x = Real.cos (a * x))
    (hs : ∀ n : ℕ, 1 ≤ n →
      s n = 1 / Real.pi * ∫ x in -Real.pi..Real.pi,
        f x * Real.sin ((n : ℝ) * x)) :
    ∀ n : ℕ, 1 ≤ n → s n = 0 := by
  intro n hn
  rw [hs n hn]
  let g : ℝ → ℝ := fun x => f x * Real.sin ((n : ℝ) * x)
  have hodd (x : ℝ) : g (-x) = -g x := by
    simp [g, hf, mul_neg]
  have hcomp :
      (∫ x in -Real.pi..Real.pi, g (-x)) =
        ∫ x in -Real.pi..Real.pi, g x := by
    simpa only [neg_neg] using
      (intervalIntegral.integral_comp_neg
        (f := g) (a := -Real.pi) (b := Real.pi))
  have hneg :
      (∫ x in -Real.pi..Real.pi, g (-x)) =
        -(∫ x in -Real.pi..Real.pi, g x) := by
    calc
      (∫ x in -Real.pi..Real.pi, g (-x)) =
          ∫ x in -Real.pi..Real.pi, -g x := by
            apply intervalIntegral.integral_congr
            intro x hx
            exact hodd x
      _ = -(∫ x in -Real.pi..Real.pi, g x) := by
        rw [intervalIntegral.integral_neg]
  have hintegral : (∫ x in -Real.pi..Real.pi, g x) = 0 := by
    linarith
  rw [show (fun x => f x * Real.sin ((n : ℝ) * x)) = g by rfl,
    hintegral]
  ring

theorem gap3 (a : ℝ) (c : ℕ → ℝ)
    (hc : c 0 =
      2 / Real.pi * ∫ x in 0..Real.pi, Real.cos (a * x)) :
    c 0 =
      2 / Real.pi * ∫ x in 0..Real.pi, Real.cos (a * x) := by
  exact hc

theorem gap4 (a : ℝ) (ha : Nonintegral a) :
    2 / Real.pi * (∫ x in 0..Real.pi, Real.cos (a * x)) =
      2 / (a * Real.pi) * Real.sin (a * Real.pi) := by
  rw [integral_cos_mul a (nonintegral_ne_zero ha)]
  field_simp [nonintegral_ne_zero ha, Real.pi_ne_zero]

theorem gap5 (a : ℝ) (c : ℕ → ℝ) (ha : Nonintegral a)
    (hc : c 0 =
      2 / Real.pi * ∫ x in 0..Real.pi, Real.cos (a * x)) :
    c 0 = 2 / (a * Real.pi) * Real.sin (a * Real.pi) := by
  rw [hc, gap4 a ha]

theorem gap6 (a : ℝ) (c : ℕ → ℝ)
    (hc : ∀ n : ℕ, 1 ≤ n → c n = coefficientIntegral a n) :
    ∀ n : ℕ, 1 ≤ n → c n = coefficientIntegral a n := by
  exact hc

theorem gap7 (a : ℝ) :
    ∀ n : ℕ, 1 ≤ n →
      coefficientIntegral a n = productToSumIntegral a n := by
  intro n hn
  have hint :
      (∫ x in (0 : ℝ)..Real.pi,
        (Real.cos (((n : ℝ) + a) * x) +
          Real.cos (((n : ℝ) - a) * x))) =
        2 * ∫ x in (0 : ℝ)..Real.pi,
          Real.cos (a * x) * Real.cos ((n : ℝ) * x) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x hx
    dsimp only
    rw [add_mul, sub_mul, Real.cos_add, Real.cos_sub]
    ring
  unfold coefficientIntegral productToSumIntegral
  rw [hint]
  ring

theorem gap8 (a : ℝ) (ha : Nonintegral a) :
    ∀ n : ℕ, 1 ≤ n →
      productToSumIntegral a n =
        2 * Real.sin (a * Real.pi) / Real.pi *
          (((-1 : ℝ) ^ (n + 1) * a) /
            ((n : ℝ) ^ 2 - a ^ 2)) := by
  intro n hn
  have ha_nat : a ≠ (n : ℝ) := by
    simpa using ha (n : ℤ)
  have ha_neg_nat : a ≠ -(n : ℝ) := by
    simpa using ha (-(n : ℤ))
  have hplus : (n : ℝ) + a ≠ 0 := by
    intro h
    apply ha_neg_nat
    linarith
  have hminus : (n : ℝ) - a ≠ 0 := by
    exact sub_ne_zero.mpr ha_nat.symm
  have hden : (n : ℝ) ^ 2 - a ^ 2 ≠ 0 := by
    rw [sq_sub_sq]
    exact mul_ne_zero hplus hminus
  have hintPlus :
      IntervalIntegrable (fun x : ℝ =>
        Real.cos (((n : ℝ) + a) * x))
        MeasureTheory.volume 0 Real.pi :=
    (Real.continuous_cos.comp
      (continuous_const.mul continuous_id)).intervalIntegrable _ _
  have hintMinus :
      IntervalIntegrable (fun x : ℝ =>
        Real.cos (((n : ℝ) - a) * x))
        MeasureTheory.volume 0 Real.pi :=
    (Real.continuous_cos.comp
      (continuous_const.mul continuous_id)).intervalIntegrable _ _
  unfold productToSumIntegral
  rw [intervalIntegral.integral_add hintPlus hintMinus,
    integral_cos_mul ((n : ℝ) + a) hplus,
    integral_cos_mul ((n : ℝ) - a) hminus,
    sin_nat_add_mul_pi a n, sin_nat_sub_mul_pi a n]
  rw [pow_succ]
  field_simp [Real.pi_ne_zero, hplus, hminus, hden]
  ring

theorem gap9 (a : ℝ) (c : ℕ → ℝ) (ha : Nonintegral a)
    (hc : ∀ n : ℕ, 1 ≤ n → c n = coefficientIntegral a n) :
    ∀ n : ℕ, 1 ≤ n →
      c n =
        2 * Real.sin (a * Real.pi) / Real.pi *
          (((-1 : ℝ) ^ (n + 1) * a) /
            ((n : ℝ) ^ 2 - a ^ 2)) := by
  intro n hn
  rw [hc n hn, gap7 a n hn, gap8 a ha n hn]

theorem gap10 (a : ℝ) (f : ℝ → ℝ) (ha : Nonintegral a)
    (hf : ∀ x, f x = Real.cos (a * x)) :
    ∀ x, -Real.pi < x → x < Real.pi →
      f x = fourierSeries a x := by
  intro x hx₀ hx₁
  rw [hf x, fourierSeries_eq_cos a x ha hx₀ hx₁]

theorem gap11 (a x : ℝ) (ha : Nonintegral a)
    (hx₀ : -Real.pi < x) (hx₁ : x < Real.pi) :
    fourierSeries a x = Real.cos (a * x) := by
  exact fourierSeries_eq_cos a x ha hx₀ hx₁

theorem gap12 (a : ℝ) (f : ℝ → ℝ)
    (hf : ∀ x, f x = Real.cos (a * x)) :
    ∀ x, f x = Real.cos (a * x) := by
  exact hf

end

end ProofGap.Exercise2945
