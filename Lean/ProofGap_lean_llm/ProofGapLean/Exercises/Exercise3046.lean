import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace ProofGap.Exercise3046

noncomputable section

open scoped BigOperators Interval

def unitPoint (x : ℝ) : ℂ :=
  Complex.exp (Complex.I * (x : ℂ))

def complexFunction (x : ℝ) : ℂ :=
  Complex.exp (unitPoint x)

def realFunction (x : ℝ) : ℝ :=
  Real.exp (Real.cos x) * Real.cos (Real.sin x)

def fourierIntegral (n : ℕ) : ℝ :=
  ∫ x in (0 : ℝ)..2 * Real.pi,
    realFunction x * Real.cos ((n : ℝ) * x)

def modeIntegral (k : ℤ) : ℂ :=
  ∫ x in (0 : ℝ)..2 * Real.pi,
    Complex.exp (Complex.I * (k : ℂ) * (x : ℂ))

def complexExpSeries (x : ℝ) : ℂ :=
  ∑' m : ℕ, unitPoint x ^ m / (m.factorial : ℂ)

private theorem modeIntegral_eq (k : ℤ) :
    modeIntegral k =
      if k = 0 then (2 * Real.pi : ℝ) else 0 := by
  by_cases hk : k = 0
  · subst k
    unfold modeIntegral
    simp only [Int.cast_zero, mul_zero, zero_mul, Complex.exp_zero]
    rw [intervalIntegral.integral_const]
    change (((2 * Real.pi - 0 : ℝ) : ℂ) * 1) =
      ((2 * Real.pi : ℝ) : ℂ)
    norm_num
  · rw [if_neg hk]
    unfold modeIntegral
    have hc : Complex.I * (k : ℂ) ≠ 0 := by
      exact mul_ne_zero Complex.I_ne_zero (Int.cast_ne_zero.mpr hk)
    rw [show (fun x : ℝ =>
        Complex.exp (Complex.I * (k : ℂ) * (x : ℂ))) =
        fun x : ℝ => Complex.exp ((Complex.I * (k : ℂ)) * x) by rfl]
    rw [integral_exp_mul_complex hc]
    rw [show Complex.exp ((Complex.I * (k : ℂ)) * (2 * Real.pi : ℝ)) = 1 by
      convert Complex.exp_int_mul_two_pi_mul_I k using 1 <;>
        push_cast <;> ring]
    simp

private theorem cos_mode_eq (n : ℕ) (x : ℝ) :
    (Real.cos ((n : ℝ) * x) : ℂ) =
      (1 / 2 : ℂ) *
        (Complex.exp (Complex.I * (n : ℂ) * (x : ℂ)) +
          Complex.exp (-Complex.I * (n : ℂ) * (x : ℂ))) := by
  rw [Complex.ofReal_cos]
  unfold Complex.cos
  have hp :
      (((n : ℝ) * x : ℝ) : ℂ) * Complex.I =
        Complex.I * (n : ℂ) * (x : ℂ) := by
    push_cast
    ring
  have hn :
      -(((n : ℝ) * x : ℝ) : ℂ) * Complex.I =
        -Complex.I * (n : ℂ) * (x : ℂ) := by
    push_cast
    ring
  rw [hp, hn]
  ring

private theorem complexExpSeries_eq (x : ℝ) :
    complexExpSeries x = complexFunction x := by
  unfold complexExpSeries complexFunction
  rw [Complex.exp_eq_exp_ℂ, NormedSpace.exp_eq_tsum_div]

private def fourierSeriesTerm (n m : ℕ) (x : ℝ) : ℂ :=
  unitPoint x ^ m / (m.factorial : ℂ) *
    (Complex.exp (Complex.I * (n : ℂ) * (x : ℂ)) +
      Complex.exp (-Complex.I * (n : ℂ) * (x : ℂ)))

private theorem norm_unitPoint (x : ℝ) :
    ‖unitPoint x‖ = 1 := by
  unfold unitPoint
  rw [Complex.norm_exp]
  simp [Complex.mul_re]

private theorem norm_exp_mode (n : ℕ) (x : ℝ) :
    ‖Complex.exp (Complex.I * (n : ℂ) * (x : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]
  simp [Complex.mul_re]

private theorem norm_exp_neg_mode (n : ℕ) (x : ℝ) :
    ‖Complex.exp (-Complex.I * (n : ℂ) * (x : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]
  simp [Complex.mul_re]

private theorem norm_fourierSeriesTerm_le (n m : ℕ) (x : ℝ) :
    ‖fourierSeriesTerm n m x‖ ≤ 2 / (m.factorial : ℝ) := by
  have hsum :
      ‖Complex.exp (Complex.I * (n : ℂ) * (x : ℂ)) +
          Complex.exp (-Complex.I * (n : ℂ) * (x : ℂ))‖ ≤ 2 := by
    calc
      _ ≤ ‖Complex.exp (Complex.I * (n : ℂ) * (x : ℂ))‖ +
          ‖Complex.exp (-Complex.I * (n : ℂ) * (x : ℂ))‖ :=
        norm_add_le _ _
      _ = 2 := by
        rw [norm_exp_mode, norm_exp_neg_mode]
        norm_num
  unfold fourierSeriesTerm
  rw [norm_mul, norm_div, norm_pow, norm_unitPoint, Complex.norm_natCast]
  simp only [one_pow]
  calc
    1 / (m.factorial : ℝ) *
          ‖Complex.exp (Complex.I * (n : ℂ) * (x : ℂ)) +
            Complex.exp (-Complex.I * (n : ℂ) * (x : ℂ))‖
        ≤ 1 / (m.factorial : ℝ) * 2 :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 2 / (m.factorial : ℝ) := by ring

private theorem summable_two_div_factorial :
    Summable (fun m : ℕ => 2 / (m.factorial : ℝ)) := by
  simpa [one_pow] using
    (Real.summable_pow_div_factorial (1 : ℝ)).mul_left 2

private theorem summable_complex_coeff (x : ℝ) :
    Summable (fun m : ℕ => unitPoint x ^ m / (m.factorial : ℂ)) := by
  apply Summable.of_norm
  convert Real.summable_pow_div_factorial (1 : ℝ) using 1
  funext m
  rw [norm_div, norm_pow, norm_unitPoint, Complex.norm_natCast]

private theorem fourierSeriesTerm_hasSum (n : ℕ) (x : ℝ) :
    HasSum (fun m : ℕ => fourierSeriesTerm n m x)
      (complexExpSeries x *
        (Complex.exp (Complex.I * (n : ℂ) * (x : ℂ)) +
          Complex.exp (-Complex.I * (n : ℂ) * (x : ℂ)))) := by
  simpa only [fourierSeriesTerm, complexExpSeries] using
    (summable_complex_coeff x).hasSum.mul_right
      (Complex.exp (Complex.I * (n : ℂ) * (x : ℂ)) +
        Complex.exp (-Complex.I * (n : ℂ) * (x : ℂ)))

private theorem continuous_fourierSeriesTerm (n m : ℕ) :
    Continuous (fourierSeriesTerm n m) := by
  unfold fourierSeriesTerm unitPoint
  fun_prop

private theorem integral_fourierSeriesTerm_hasSum (n : ℕ) :
    HasSum
      (fun m : ℕ =>
        ∫ x in (0 : ℝ)..2 * Real.pi, fourierSeriesTerm n m x)
      (∫ x in (0 : ℝ)..2 * Real.pi,
        complexExpSeries x *
          (Complex.exp (Complex.I * (n : ℂ) * (x : ℂ)) +
            Complex.exp (-Complex.I * (n : ℂ) * (x : ℂ)))) := by
  apply intervalIntegral.hasSum_integral_of_dominated_convergence
    (fun m : ℕ => fun _ : ℝ => 2 / (m.factorial : ℝ))
  · intro m
    exact (continuous_fourierSeriesTerm n m).aestronglyMeasurable
  · intro m
    filter_upwards with x hx
    exact norm_fourierSeriesTerm_le n m x
  · filter_upwards with x hx
    exact summable_two_div_factorial
  · exact intervalIntegrable_const
  · filter_upwards with x hx
    exact fourierSeriesTerm_hasSum n x

private theorem unitPoint_pow_eq_mode (m : ℕ) (x : ℝ) :
    unitPoint x ^ m =
      Complex.exp (Complex.I * (m : ℂ) * (x : ℂ)) := by
  unfold unitPoint
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

private theorem exp_mode_mul_eq_add (m n : ℕ) (x : ℝ) :
    Complex.exp (Complex.I * (m : ℂ) * (x : ℂ)) *
        Complex.exp (Complex.I * (n : ℂ) * (x : ℂ)) =
      Complex.exp
        (Complex.I * (((m : ℤ) + (n : ℤ) : ℤ) : ℂ) * (x : ℂ)) := by
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem exp_mode_mul_eq_sub (m n : ℕ) (x : ℝ) :
    Complex.exp (Complex.I * (m : ℂ) * (x : ℂ)) *
        Complex.exp (-Complex.I * (n : ℂ) * (x : ℂ)) =
      Complex.exp
        (Complex.I * (((m : ℤ) - (n : ℤ) : ℤ) : ℂ) * (x : ℂ)) := by
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem fourierSeriesTerm_eq_modes (n m : ℕ) (x : ℝ) :
    fourierSeriesTerm n m x =
      (1 / (m.factorial : ℂ)) *
        (Complex.exp
            (Complex.I * (((m : ℤ) + (n : ℤ) : ℤ) : ℂ) * (x : ℂ)) +
          Complex.exp
            (Complex.I * (((m : ℤ) - (n : ℤ) : ℤ) : ℂ) * (x : ℂ))) := by
  calc
    fourierSeriesTerm n m x =
        (1 / (m.factorial : ℂ)) *
          (Complex.exp (Complex.I * (m : ℂ) * (x : ℂ)) *
              Complex.exp (Complex.I * (n : ℂ) * (x : ℂ)) +
            Complex.exp (Complex.I * (m : ℂ) * (x : ℂ)) *
              Complex.exp (-Complex.I * (n : ℂ) * (x : ℂ))) := by
      unfold fourierSeriesTerm
      rw [unitPoint_pow_eq_mode]
      ring
    _ = _ := by
      rw [exp_mode_mul_eq_add, exp_mode_mul_eq_sub]

private theorem integral_fourierSeriesTerm_eq_modes (n m : ℕ) :
    (∫ x in (0 : ℝ)..2 * Real.pi, fourierSeriesTerm n m x) =
      (1 / (m.factorial : ℂ)) *
        (modeIntegral ((m : ℤ) + (n : ℤ)) +
          modeIntegral ((m : ℤ) - (n : ℤ))) := by
  let plusMode : ℝ → ℂ := fun x =>
    Complex.exp
      (Complex.I * (((m : ℤ) + (n : ℤ) : ℤ) : ℂ) * (x : ℂ))
  let minusMode : ℝ → ℂ := fun x =>
    Complex.exp
      (Complex.I * (((m : ℤ) - (n : ℤ) : ℤ) : ℂ) * (x : ℂ))
  have hplus : IntervalIntegrable plusMode MeasureTheory.volume
      0 (2 * Real.pi) := by
    apply Continuous.intervalIntegrable
    dsimp [plusMode]
    fun_prop
  have hminus : IntervalIntegrable minusMode MeasureTheory.volume
      0 (2 * Real.pi) := by
    apply Continuous.intervalIntegrable
    dsimp [minusMode]
    fun_prop
  calc
    (∫ x in (0 : ℝ)..2 * Real.pi, fourierSeriesTerm n m x) =
        ∫ x in (0 : ℝ)..2 * Real.pi,
          (1 / (m.factorial : ℂ)) * (plusMode x + minusMode x) := by
      apply intervalIntegral.integral_congr
      intro x hx
      exact fourierSeriesTerm_eq_modes n m x
    _ = (1 / (m.factorial : ℂ)) *
        ∫ x in (0 : ℝ)..2 * Real.pi, plusMode x + minusMode x := by
      exact intervalIntegral.integral_const_mul _ _
    _ = (1 / (m.factorial : ℂ)) *
        ((∫ x in (0 : ℝ)..2 * Real.pi, plusMode x) +
          ∫ x in (0 : ℝ)..2 * Real.pi, minusMode x) := by
      rw [intervalIntegral.integral_add hplus hminus]
    _ = (1 / (m.factorial : ℂ)) *
        (modeIntegral ((m : ℤ) + (n : ℤ)) +
          modeIntegral ((m : ℤ) - (n : ℤ))) := by
      rfl

private theorem norm_modeIntegral_le (k : ℤ) :
    ‖modeIntegral k‖ ≤ 2 * Real.pi := by
  rw [modeIntegral_eq]
  split_ifs
  · rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : 0 ≤ 2 * Real.pi)]
  · simp
    positivity

private theorem summable_two_pi_div_factorial :
    Summable (fun m : ℕ => (2 * Real.pi) / (m.factorial : ℝ)) := by
  simpa [one_pow] using
    (Real.summable_pow_div_factorial (1 : ℝ)).mul_left
      (2 * Real.pi)

private theorem summable_mode_re_coeff (k : ℕ → ℤ) :
    Summable (fun m : ℕ =>
      (1 / (m.factorial : ℝ)) * (modeIntegral (k m)).re) := by
  apply Summable.of_norm_bounded summable_two_pi_div_factorial
  intro m
  have hcoeff : 0 ≤ 1 / (m.factorial : ℝ) := by positivity
  calc
    ‖(1 / (m.factorial : ℝ)) * (modeIntegral (k m)).re‖ =
        (1 / (m.factorial : ℝ)) * |(modeIntegral (k m)).re| := by
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg hcoeff]
    _ ≤ (1 / (m.factorial : ℝ)) * ‖modeIntegral (k m)‖ :=
      mul_le_mul_of_nonneg_left
        (Complex.abs_re_le_norm (modeIntegral (k m))) hcoeff
    _ ≤ (1 / (m.factorial : ℝ)) * (2 * Real.pi) :=
      mul_le_mul_of_nonneg_left (norm_modeIntegral_le (k m)) hcoeff
    _ = (2 * Real.pi) / (m.factorial : ℝ) := by ring

private theorem integral_series_re_eq_mode_sums (n : ℕ) :
    (∫ x in (0 : ℝ)..2 * Real.pi,
      complexExpSeries x *
        (Complex.exp (Complex.I * (n : ℂ) * (x : ℂ)) +
          Complex.exp (-Complex.I * (n : ℂ) * (x : ℂ)))).re =
      (∑' m : ℕ, (1 / (m.factorial : ℝ)) *
        (modeIntegral ((m : ℤ) + (n : ℤ))).re) +
      (∑' m : ℕ, (1 / (m.factorial : ℝ)) *
        (modeIntegral ((m : ℤ) - (n : ℤ))).re) := by
  have hre := Complex.hasSum_re (integral_fourierSeriesTerm_hasSum n)
  have hre' :
      HasSum
        (fun m : ℕ =>
          (1 / (m.factorial : ℝ)) *
            ((modeIntegral ((m : ℤ) + (n : ℤ))).re +
              (modeIntegral ((m : ℤ) - (n : ℤ))).re))
        (∫ x in (0 : ℝ)..2 * Real.pi,
          complexExpSeries x *
            (Complex.exp (Complex.I * (n : ℂ) * (x : ℂ)) +
              Complex.exp (-Complex.I * (n : ℂ) * (x : ℂ)))).re := by
    convert hre using 1
    funext m
    rw [integral_fourierSeriesTerm_eq_modes]
    have hcast :
        (1 / (m.factorial : ℂ)) =
          ((1 / (m.factorial : ℝ) : ℝ) : ℂ) := by
      push_cast
      rfl
    rw [hcast]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, Complex.add_re]
  have hplus :
      Summable (fun m : ℕ => (1 / (m.factorial : ℝ)) *
        (modeIntegral ((m : ℤ) + (n : ℤ))).re) :=
    summable_mode_re_coeff (fun m => (m : ℤ) + (n : ℤ))
  have hminus :
      Summable (fun m : ℕ => (1 / (m.factorial : ℝ)) *
        (modeIntegral ((m : ℤ) - (n : ℤ))).re) :=
    summable_mode_re_coeff (fun m => (m : ℤ) - (n : ℤ))
  calc
    (∫ x in (0 : ℝ)..2 * Real.pi,
      complexExpSeries x *
        (Complex.exp (Complex.I * (n : ℂ) * (x : ℂ)) +
          Complex.exp (-Complex.I * (n : ℂ) * (x : ℂ)))).re =
        ∑' m : ℕ,
          (1 / (m.factorial : ℝ)) *
            ((modeIntegral ((m : ℤ) + (n : ℤ))).re +
              (modeIntegral ((m : ℤ) - (n : ℤ))).re) :=
      hre'.tsum_eq.symm
    _ = ∑' m : ℕ,
        ((1 / (m.factorial : ℝ)) *
            (modeIntegral ((m : ℤ) + (n : ℤ))).re +
          (1 / (m.factorial : ℝ)) *
            (modeIntegral ((m : ℤ) - (n : ℤ))).re) := by
      apply tsum_congr
      intro m
      ring
    _ = (∑' m : ℕ, (1 / (m.factorial : ℝ)) *
          (modeIntegral ((m : ℤ) + (n : ℤ))).re) +
        (∑' m : ℕ, (1 / (m.factorial : ℝ)) *
          (modeIntegral ((m : ℤ) - (n : ℤ))).re) :=
      hplus.tsum_add hminus

theorem gap1 (u v : ℝ) (w : ℂ)
    (hw : w = (u : ℂ) + Complex.I * (v : ℂ)) :
    w.re = u := by
  subst w
  simp

theorem gap2 (x : ℝ) :
    (complexFunction x).re = realFunction x := by
  unfold complexFunction unitPoint realFunction
  rw [show Complex.I * (x : ℂ) = (x : ℂ) * Complex.I by ring,
    Complex.exp_ofReal_mul_I]
  rw [Complex.exp_re]
  simp
  rw [Complex.cos_ofReal_re, Complex.sin_ofReal_re]

theorem gap3 (n : ℕ) :
    fourierIntegral n =
      (∫ x in (0 : ℝ)..2 * Real.pi,
        complexFunction x * (Real.cos ((n : ℝ) * x) : ℂ)).re := by
  have hf :
      IntervalIntegrable
        (fun x : ℝ =>
          complexFunction x * (Real.cos ((n : ℝ) * x) : ℂ))
        MeasureTheory.volume 0 (2 * Real.pi) := by
    apply Continuous.intervalIntegrable
    unfold complexFunction unitPoint
    fun_prop
  calc
    fourierIntegral n =
        ∫ x in (0 : ℝ)..2 * Real.pi,
          (complexFunction x * (Real.cos ((n : ℝ) * x) : ℂ)).re := by
      unfold fourierIntegral
      apply intervalIntegral.integral_congr
      intro x hx
      change realFunction x * Real.cos ((n : ℝ) * x) =
        (complexFunction x * (Real.cos ((n : ℝ) * x) : ℂ)).re
      rw [← gap2 x]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        mul_zero, sub_zero]
    _ = (∫ x in (0 : ℝ)..2 * Real.pi,
        complexFunction x * (Real.cos ((n : ℝ) * x) : ℂ)).re := by
      simpa only [Complex.reCLM_apply] using
        (Complex.reCLM.intervalIntegral_comp_comm hf)

theorem gap4 (n : ℕ) :
    fourierIntegral n =
      (∫ x in (0 : ℝ)..2 * Real.pi,
        complexFunction x * (1 / 2 : ℂ) *
          (Complex.exp (Complex.I * (n : ℂ) * (x : ℂ)) +
            Complex.exp (-Complex.I * (n : ℂ) * (x : ℂ)))).re := by
  rw [gap3 n]
  congr 1
  apply intervalIntegral.integral_congr
  intro x hx
  change complexFunction x * (Real.cos ((n : ℝ) * x) : ℂ) =
    complexFunction x * (1 / 2 : ℂ) *
      (Complex.exp (Complex.I * (n : ℂ) * (x : ℂ)) +
        Complex.exp (-Complex.I * (n : ℂ) * (x : ℂ)))
  rw [cos_mode_eq n x]
  ring

theorem gap5 (n : ℕ) :
    fourierIntegral n =
      (1 / 2 : ℝ) *
        (∫ x in (0 : ℝ)..2 * Real.pi,
          complexExpSeries x *
            (Complex.exp (Complex.I * (n : ℂ) * (x : ℂ)) +
              Complex.exp (-Complex.I * (n : ℂ) * (x : ℂ)))).re := by
  rw [gap4 n]
  have hint :
      (∫ x in (0 : ℝ)..2 * Real.pi,
        complexFunction x * (1 / 2 : ℂ) *
          (Complex.exp (Complex.I * (n : ℂ) * (x : ℂ)) +
            Complex.exp (-Complex.I * (n : ℂ) * (x : ℂ)))) =
        (1 / 2 : ℂ) *
          ∫ x in (0 : ℝ)..2 * Real.pi,
            complexExpSeries x *
              (Complex.exp (Complex.I * (n : ℂ) * (x : ℂ)) +
                Complex.exp (-Complex.I * (n : ℂ) * (x : ℂ))) := by
    calc
      (∫ x in (0 : ℝ)..2 * Real.pi,
        complexFunction x * (1 / 2 : ℂ) *
          (Complex.exp (Complex.I * (n : ℂ) * (x : ℂ)) +
            Complex.exp (-Complex.I * (n : ℂ) * (x : ℂ)))) =
          ∫ x in (0 : ℝ)..2 * Real.pi,
            (1 / 2 : ℂ) *
              (complexExpSeries x *
                (Complex.exp (Complex.I * (n : ℂ) * (x : ℂ)) +
                  Complex.exp (-Complex.I * (n : ℂ) * (x : ℂ)))) := by
        apply intervalIntegral.integral_congr
        intro x hx
        change
          complexFunction x * (1 / 2 : ℂ) *
              (Complex.exp (Complex.I * (n : ℂ) * (x : ℂ)) +
                Complex.exp (-Complex.I * (n : ℂ) * (x : ℂ))) =
            (1 / 2 : ℂ) *
              (complexExpSeries x *
                (Complex.exp (Complex.I * (n : ℂ) * (x : ℂ)) +
                  Complex.exp (-Complex.I * (n : ℂ) * (x : ℂ))))
        rw [complexExpSeries_eq]
        ring
      _ = (1 / 2 : ℂ) *
          ∫ x in (0 : ℝ)..2 * Real.pi,
            complexExpSeries x *
              (Complex.exp (Complex.I * (n : ℂ) * (x : ℂ)) +
                Complex.exp (-Complex.I * (n : ℂ) * (x : ℂ))) := by
        exact intervalIntegral.integral_const_mul _ _
  rw [hint]
  norm_num

theorem gap6 (n : ℕ) :
    fourierIntegral n =
      (1 / 2 : ℝ) *
        ((∑' m : ℕ, (1 / (m.factorial : ℝ)) *
          (modeIntegral ((m : ℤ) + (n : ℤ))).re) +
        (∑' m : ℕ, (1 / (m.factorial : ℝ)) *
          (modeIntegral ((m : ℤ) - (n : ℤ))).re)) := by
  rw [gap5 n]
  congr 1
  exact integral_series_re_eq_mode_sums n

theorem gap7 (k : ℤ) :
    modeIntegral k =
      if k = 0 then (2 * Real.pi : ℝ) else 0 := by
  exact modeIntegral_eq k

theorem gap8 (n m : ℕ) (hn : n = 0) :
    modeIntegral ((m : ℤ) + (n : ℤ)) =
      if m = 0 then (2 * Real.pi : ℝ) else 0 := by
  subst n
  simp [modeIntegral_eq]

theorem gap9 (n m : ℕ) (hn : n = 0) :
    modeIntegral ((m : ℤ) - (n : ℤ)) =
      if m = n then (2 * Real.pi : ℝ) else 0 := by
  subst n
  simp [modeIntegral_eq]

theorem gap10 (n : ℕ) (hn : n = 0) :
    fourierIntegral 0 = (1 / 2 : ℝ) * (2 * Real.pi + 2 * Real.pi) := by
  rw [gap6 0]
  simp_rw [gap8 0 _ rfl, gap9 0 _ rfl]
  simp

theorem gap11 (n : ℕ) (hn : n = 0) :
    (1 / 2 : ℝ) * (2 * Real.pi + 2 * Real.pi) = 2 * Real.pi := by
  ring

theorem gap12 (n : ℕ) (hn : n = 0) :
    fourierIntegral 0 = 2 * Real.pi := by
  calc
    fourierIntegral 0 =
        (1 / 2 : ℝ) * (2 * Real.pi + 2 * Real.pi) := gap10 n hn
    _ = 2 * Real.pi := gap11 n hn

theorem gap13 (n m : ℕ) (hn : 1 ≤ n) :
    modeIntegral ((m : ℤ) + (n : ℤ)) = 0 := by
  have hk : (m : ℤ) + (n : ℤ) ≠ 0 :=
    ne_of_gt
      (add_pos_of_nonneg_of_pos (Int.ofNat_nonneg m)
        (by
          show (0 : ℤ) < (n : ℤ)
          exact_mod_cast hn))
  rw [modeIntegral_eq, if_neg hk]
  norm_num

theorem gap14 (n m : ℕ) (hn : 1 ≤ n) :
    modeIntegral ((m : ℤ) - (n : ℤ)) =
      if m = n then (2 * Real.pi : ℝ) else 0 := by
  rw [modeIntegral_eq]
  by_cases hmn : m = n
  · subst m
    simp
  · rw [if_neg hmn, if_neg]
    exact sub_ne_zero.mpr (by exact_mod_cast hmn)

theorem gap15 (n : ℕ) (hn : 1 ≤ n) :
    fourierIntegral n =
      (1 / 2 : ℝ) * (1 / (n.factorial : ℝ)) * (2 * Real.pi) := by
  rw [gap6 n]
  simp_rw [gap13 n _ hn, gap14 n _ hn]
  simp
  ring

theorem gap16 (n : ℕ) (hn : 1 ≤ n) :
    (1 / 2 : ℝ) * (1 / (n.factorial : ℝ)) * (2 * Real.pi) =
      Real.pi / (n.factorial : ℝ) := by
  ring

theorem gap17 (n : ℕ) (hn : 1 ≤ n) :
    fourierIntegral n = Real.pi / (n.factorial : ℝ) := by
  calc
    fourierIntegral n =
        (1 / 2 : ℝ) * (1 / (n.factorial : ℝ)) *
          (2 * Real.pi) := gap15 n hn
    _ = Real.pi / (n.factorial : ℝ) := gap16 n hn

theorem gap18 (n : ℕ) :
    fourierIntegral n =
      if n = 0 then 2 * Real.pi else Real.pi / (n.factorial : ℝ) := by
  by_cases hn : n = 0
  · rw [if_pos hn]
    subst n
    exact gap12 0 rfl
  · rw [if_neg hn]
    exact gap17 n (by omega)

end

end ProofGap.Exercise3046
