import Mathlib.Algebra.Ring.Periodic
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

namespace ProofGap.Exercise2957

noncomputable section

open scoped Interval

def target (x : ℝ) : ℝ :=
  |Real.sin x|

def coefficientIntegral (n : ℕ) : ℝ :=
  4 / Real.pi *
    ∫ x in 0..Real.pi / 2,
      target x * Real.cos (2 * (n : ℝ) * x)

def productToSumIntegral (n : ℕ) : ℝ :=
  2 / Real.pi *
    ∫ x in 0..Real.pi / 2,
      (Real.sin ((2 * (n : ℝ) + 1) * x) -
        Real.sin ((2 * (n : ℝ) - 1) * x))

def antiderivative (n : ℕ) (x : ℝ) : ℝ :=
  2 / Real.pi *
    (-1 / (2 * (n : ℝ) + 1) *
        Real.cos ((2 * (n : ℝ) + 1) * x) +
      1 / (2 * (n : ℝ) - 1) *
        Real.cos ((2 * (n : ℝ) - 1) * x))

def antiderivativeEval (n : ℕ) : ℝ :=
  antiderivative n (Real.pi / 2) - antiderivative n 0

def fourierSeries (x : ℝ) : ℝ :=
  2 / Real.pi -
    4 / Real.pi *
      ∑' k : ℕ,
        Real.cos (2 * (k + 1 : ℝ) * x) /
          (4 * (k + 1 : ℝ) ^ 2 - 1)

private theorem integral_sin_mul (c : ℝ) (hc : c ≠ 0) (u v : ℝ) :
    (∫ x in u..v, Real.sin (c * x)) =
      -Real.cos (c * v) / c - (-Real.cos (c * u) / c) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x hx
    have hinner : HasDerivAt (fun y : ℝ => c * y) c x := by
      simpa only [id_eq, mul_one] using (hasDerivAt_id x).const_mul c
    convert (((Real.hasDerivAt_cos (c * x)).comp x hinner).neg).div_const c
      using 1
    field_simp [hc]
  · exact (Real.continuous_sin.comp
      (continuous_const.mul continuous_id)).intervalIntegrable u v

theorem gap1 (f : ℝ → ℝ) (hf : ∀ x, f x = target x) :
    Function.Periodic f Real.pi := by
  intro x
  rw [hf, hf]
  simp [target, Real.sin_add_pi]

theorem gap2 (f : ℝ → ℝ) (hf : ∀ x, f x = target x) :
    Continuous f := by
  rw [funext hf]
  exact Real.continuous_sin.abs

theorem gap3 (f : ℝ → ℝ) (hf : ∀ x, f x = target x) :
    Function.Even f := by
  intro x
  rw [hf, hf]
  simp [target]

theorem gap4 (s : ℕ → ℝ)
    (hs : ∀ n : ℕ, 1 ≤ n → s n = 0) :
    ∀ n : ℕ, 1 ≤ n → s n = 0 := by
  exact hs

theorem gap5 (c : ℕ → ℝ)
    (hc : c 0 =
      4 / Real.pi * ∫ x in 0..Real.pi / 2, target x) :
    c 0 =
      4 / Real.pi * ∫ x in 0..Real.pi / 2, target x := by
  exact hc

theorem gap6 :
    4 / Real.pi * (∫ x in 0..Real.pi / 2, target x) =
      4 / Real.pi * ∫ x in 0..Real.pi / 2, Real.sin x := by
  congr 1
  apply intervalIntegral.integral_congr
  intro x hx
  have hx' : x ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := by
    simpa [Set.uIcc_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 2)] using hx
  unfold target
  rw [abs_of_nonneg]
  exact Real.sin_nonneg_of_nonneg_of_le_pi hx'.1
    (hx'.2.trans (by linarith [Real.pi_pos]))

theorem gap7 :
    4 / Real.pi * (∫ x in 0..Real.pi / 2, Real.sin x) =
      4 / Real.pi := by
  rw [integral_sin]
  simp

theorem gap8 (c : ℕ → ℝ)
    (hc : c 0 =
      4 / Real.pi * ∫ x in 0..Real.pi / 2, target x) :
    c 0 = 4 / Real.pi := by
  rw [hc, gap6, gap7]

theorem gap9 (c : ℕ → ℝ)
    (hc : ∀ n : ℕ, 1 ≤ n → c n = coefficientIntegral n) :
    ∀ n : ℕ, 1 ≤ n → c n = coefficientIntegral n := by
  exact hc

theorem gap10 :
    ∀ n : ℕ, 1 ≤ n →
      coefficientIntegral n = productToSumIntegral n := by
  intro n hn
  have hint :
      (∫ x in (0 : ℝ)..Real.pi / 2,
        (Real.sin ((2 * (n : ℝ) + 1) * x) -
          Real.sin ((2 * (n : ℝ) - 1) * x))) =
        2 * ∫ x in (0 : ℝ)..Real.pi / 2,
          target x * Real.cos (2 * (n : ℝ) * x) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x hx
    have hx' : x ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := by
      simpa [Set.uIcc_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 2)] using hx
    have hsin : target x = Real.sin x := by
      unfold target
      rw [abs_of_nonneg]
      exact Real.sin_nonneg_of_nonneg_of_le_pi hx'.1
        (hx'.2.trans (by linarith [Real.pi_pos]))
    change Real.sin ((2 * (n : ℝ) + 1) * x) -
        Real.sin ((2 * (n : ℝ) - 1) * x) =
      2 * (target x * Real.cos (2 * (n : ℝ) * x))
    rw [hsin]
    rw [show (2 * (n : ℝ) + 1) * x = 2 * (n : ℝ) * x + x by ring,
      show (2 * (n : ℝ) - 1) * x = 2 * (n : ℝ) * x - x by ring,
      Real.sin_add, Real.sin_sub]
    ring
  unfold coefficientIntegral productToSumIntegral
  rw [hint]
  ring

theorem gap11 (c : ℕ → ℝ)
    (hc : ∀ n : ℕ, 1 ≤ n → c n = coefficientIntegral n) :
    ∀ n : ℕ, 1 ≤ n → c n = productToSumIntegral n := by
  intro n hn
  rw [hc n hn, gap10 n hn]

theorem gap12 (c : ℕ → ℝ)
    (hc : ∀ n : ℕ, 1 ≤ n → c n = productToSumIntegral n) :
    ∀ n : ℕ, 1 ≤ n → c n = antiderivativeEval n := by
  intro n hn
  rw [hc n hn]
  have hplus : 2 * (n : ℝ) + 1 ≠ 0 := by positivity
  have hminus : 2 * (n : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  have hintPlus : IntervalIntegrable
      (fun x : ℝ => Real.sin ((2 * (n : ℝ) + 1) * x))
      MeasureTheory.volume 0 (Real.pi / 2) :=
    (Real.continuous_sin.comp
      (continuous_const.mul continuous_id)).intervalIntegrable _ _
  have hintMinus : IntervalIntegrable
      (fun x : ℝ => Real.sin ((2 * (n : ℝ) - 1) * x))
      MeasureTheory.volume 0 (Real.pi / 2) :=
    (Real.continuous_sin.comp
      (continuous_const.mul continuous_id)).intervalIntegrable _ _
  unfold productToSumIntegral antiderivativeEval antiderivative
  rw [intervalIntegral.integral_sub hintPlus hintMinus,
    integral_sin_mul (2 * (n : ℝ) + 1) hplus 0 (Real.pi / 2),
    integral_sin_mul (2 * (n : ℝ) - 1) hminus 0 (Real.pi / 2)]
  simp only [mul_zero, Real.cos_zero]
  ring

theorem gap13 :
    ∀ n : ℕ, 1 ≤ n →
      antiderivativeEval n =
        -(4 / Real.pi) * (1 / (4 * (n : ℝ) ^ 2 - 1)) := by
  intro n hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hplus : 2 * (n : ℝ) + 1 ≠ 0 := by positivity
  have hminus : 2 * (n : ℝ) - 1 ≠ 0 := by nlinarith
  have hden : 4 * (n : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
  have hden' : -1 + (n : ℝ) ^ 2 * 4 ≠ 0 := by nlinarith
  have hcosPlus :
      Real.cos ((2 * (n : ℝ) + 1) * (Real.pi / 2)) = 0 := by
    rw [show (2 * (n : ℝ) + 1) * (Real.pi / 2) =
      (n : ℝ) * Real.pi + Real.pi / 2 by ring,
      Real.cos_add, Real.cos_nat_mul_pi, Real.sin_nat_mul_pi,
      Real.cos_pi_div_two, Real.sin_pi_div_two]
    ring
  have hcosMinus :
      Real.cos ((2 * (n : ℝ) - 1) * (Real.pi / 2)) = 0 := by
    rw [show (2 * (n : ℝ) - 1) * (Real.pi / 2) =
      (n : ℝ) * Real.pi - Real.pi / 2 by ring,
      Real.cos_sub, Real.cos_nat_mul_pi, Real.sin_nat_mul_pi,
      Real.cos_pi_div_two, Real.sin_pi_div_two]
    ring
  unfold antiderivativeEval antiderivative
  rw [hcosPlus, hcosMinus]
  simp only [mul_zero, add_zero, Real.cos_zero]
  rw [show 4 * (n : ℝ) ^ 2 - 1 =
    (2 * (n : ℝ) + 1) * (2 * (n : ℝ) - 1) by ring]
  field_simp [Real.pi_ne_zero, hplus, hminus]
  ring

theorem gap14 (c : ℕ → ℝ)
    (hc : ∀ n : ℕ, 1 ≤ n → c n = coefficientIntegral n) :
    ∀ n : ℕ, 1 ≤ n →
      c n = -(4 / Real.pi) * (1 / (4 * (n : ℝ) ^ 2 - 1)) := by
  intro n hn
  calc
    c n = productToSumIntegral n := gap11 c hc n hn
    _ = antiderivativeEval n :=
      gap12 (fun m => productToSumIntegral m) (fun m hm => rfl) n hn
    _ = -(4 / Real.pi) * (1 / (4 * (n : ℝ) ^ 2 - 1)) := gap13 n hn

private local instance piPositiveFact : Fact (0 < Real.pi) := ⟨Real.pi_pos⟩

private def realSinComplex (x : ℝ) : ℂ := Real.sin x

private def realCosComplex (x : ℝ) : ℂ := Real.cos x

private theorem realSinComplex_coeff_ne (n : ℤ) (hn : n ≠ 0) :
    fourierCoeffOn Real.pi_pos realSinComplex n =
      -(2 : ℂ) / ((Real.pi : ℂ) * (4 * (n : ℂ) ^ 2 - 1)) := by
  have hs := fourierCoeffOn_of_hasDerivAt Real.pi_pos hn
    (f := realSinComplex) (f' := realCosComplex)
    (fun x hx => (Real.hasDerivAt_sin x).ofReal_comp)
    ((Complex.continuous_ofReal.comp Real.continuous_cos).intervalIntegrable _ _)
  have hc := fourierCoeffOn_of_hasDerivAt Real.pi_pos hn
    (f := realCosComplex) (f' := fun x => -(realSinComplex x))
    (fun x hx => by
      convert (Real.hasDerivAt_cos x).ofReal_comp using 1 <;>
        simp [realSinComplex, realCosComplex])
    ((Complex.continuous_ofReal.comp Real.continuous_sin).neg.intervalIntegrable _ _)
  simp only [realSinComplex, realCosComplex, Real.sin_pi, Real.sin_zero,
    Complex.ofReal_zero, sub_self, mul_zero, zero_sub, Real.cos_pi,
    Real.cos_zero, Complex.ofReal_neg, Complex.ofReal_one, one_mul] at hs hc
  simp only [sub_zero] at hs hc
  rw [show fourierCoeffOn Real.pi_pos
      (fun x => -((Real.sin x : ℝ) : ℂ)) n =
        -fourierCoeffOn Real.pi_pos realSinComplex n by
    simpa [realSinComplex] using
      (fourierCoeffOn.const_mul realSinComplex (-1) n Real.pi_pos)] at hc
  simp only [fourier_coe_apply, Complex.ofReal_zero, mul_zero, zero_div,
    Complex.exp_zero, one_mul] at hc
  have hnR : (1 : ℝ) ≤ |(n : ℝ)| := by
    exact_mod_cast Int.one_le_abs hn
  have hdenR : 4 * (n : ℝ) ^ 2 - 1 ≠ 0 := by
    nlinarith [sq_abs (n : ℝ)]
  have hdenC : 4 * (n : ℂ) ^ 2 - 1 ≠ 0 := by
    exact_mod_cast hdenR
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have hpiC : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp [hnC, hpiC, Complex.I_ne_zero] at hs hc
  rw [← hs] at hc
  ring_nf at hc
  rw [Complex.I_sq] at hc
  have hmain : fourierCoeffOn Real.pi_pos realSinComplex n *
      ((Real.pi : ℂ) * (4 * (n : ℂ) ^ 2 - 1)) = -2 := by
    linear_combination -hc
  apply (eq_div_iff (mul_ne_zero hpiC hdenC)).2
  exact hmain

private theorem realSinComplex_coeff_zero :
    fourierCoeffOn Real.pi_pos realSinComplex 0 = (2 : ℂ) / Real.pi := by
  rw [fourierCoeffOn_eq_integral]
  simp only [realSinComplex, sub_zero, neg_zero, fourier_zero, one_smul,
    smul_eq_mul, one_div, one_mul]
  rw [intervalIntegral.integral_ofReal, integral_sin]
  norm_num [Complex.real_smul]
  change (Real.pi⁻¹ : ℝ) • ((2 : ℝ) : ℂ) = 2 / (Real.pi : ℂ)
  rw [Complex.real_smul]
  push_cast
  ring

private def targetComplex (x : ℝ) : ℂ := target x

private theorem targetComplex_periodic :
    Function.Periodic targetComplex Real.pi := by
  intro x
  simp [targetComplex, target, Real.sin_add_pi]

private noncomputable def targetCircle : C(AddCircle Real.pi, ℂ) := by
  letI : Fact (0 < Real.pi) := ⟨Real.pi_pos⟩
  refine ⟨targetComplex_periodic.lift, ?_⟩
  unfold Function.Periodic.lift
  apply continuous_quot_lift
  exact Complex.continuous_ofReal.comp Real.continuous_sin.abs

private theorem targetCircle_coe (x : ℝ) :
    targetCircle (x : AddCircle Real.pi) = targetComplex x := by
  letI : Fact (0 < Real.pi) := ⟨Real.pi_pos⟩
  exact Function.Periodic.lift_coe targetComplex_periodic x

private theorem targetCircle_coeff_eq (n : ℤ) :
    fourierCoeff targetCircle n =
      fourierCoeffOn Real.pi_pos realSinComplex n := by
  letI : Fact (0 < Real.pi) := ⟨Real.pi_pos⟩
  rw [fourierCoeff_eq_intervalIntegral targetCircle n 0,
    fourierCoeffOn_eq_integral realSinComplex n Real.pi_pos]
  simp only [zero_add, sub_zero]
  congr 1
  apply intervalIntegral.integral_congr
  intro x hx
  have hx' : x ∈ Set.Icc (0 : ℝ) Real.pi := by
    simpa [Set.uIcc_of_le Real.pi_pos.le] using hx
  have hs : 0 ≤ Real.sin x :=
    Real.sin_nonneg_of_nonneg_of_le_pi hx'.1 hx'.2
  dsimp only
  rw [targetCircle_coe]
  simp [targetComplex, target, realSinComplex, abs_of_nonneg hs]

private theorem targetCircle_coeff_all (n : ℤ) :
    fourierCoeff targetCircle n =
      -(2 : ℂ) / ((Real.pi : ℂ) * (4 * (n : ℂ) ^ 2 - 1)) := by
  rw [targetCircle_coeff_eq]
  by_cases hn : n = 0
  · subst n
    rw [realSinComplex_coeff_zero]
    simp
  · exact realSinComplex_coeff_ne n hn

private theorem targetCircle_coeff_summable :
    Summable (fourierCoeff targetCircle) := by
  have hbase : Summable (fun n : ℤ =>
      (2 / Real.pi) / |(n : ℝ)| ^ (2 : ℝ)) := by
    exact ((Real.summable_one_div_int_add_rpow 0 2).2 (by norm_num)).mul_left
      (2 / Real.pi) |>.congr (fun n => by
        simp only [add_zero, div_eq_mul_inv]
        ring)
  apply hbase.of_norm_bounded_eventually
  filter_upwards [Filter.eventually_cofinite_ne 0] with n hn
  rw [targetCircle_coeff_all]
  have hnAbs : (1 : ℝ) ≤ |(n : ℝ)| := by
    exact_mod_cast Int.one_le_abs hn
  have hnSq : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by
    nlinarith [sq_abs (n : ℝ)]
  have hdenPos : 0 < 4 * (n : ℝ) ^ 2 - 1 := by nlinarith
  have hpiPos : 0 < Real.pi := Real.pi_pos
  have hdenNorm : ‖4 * (n : ℂ) ^ 2 - 1‖ =
      4 * (n : ℝ) ^ 2 - 1 := by
    rw [show 4 * (n : ℂ) ^ 2 - 1 =
      ((4 * (n : ℝ) ^ 2 - 1 : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hdenPos]
  simp only [norm_div, norm_neg, Complex.norm_ofNat, Complex.norm_mul,
    Complex.norm_real]
  rw [Real.norm_eq_abs, abs_of_pos hpiPos, hdenNorm]
  have hsq : |(n : ℝ)| ^ (2 : ℝ) = (n : ℝ) ^ 2 := by
    rw [Real.rpow_two, sq_abs]
  rw [hsq]
  rw [div_div]
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  nlinarith

private theorem fourier_nat_coe (m : ℕ) (x : ℝ) :
    fourier (m : ℤ) (x : AddCircle Real.pi) =
      Real.cos (2 * (m : ℝ) * x) +
        Real.sin (2 * (m : ℝ) * x) * Complex.I := by
  rw [fourier_coe_apply]
  have harg :
      2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * (x : ℂ) /
          (Real.pi : ℂ) =
        ((2 * (m : ℝ) * x : ℝ) : ℂ) * Complex.I := by
    field_simp [Real.pi_ne_zero]
    push_cast
    ring
  simp only [Int.cast_natCast]
  rw [harg, Complex.exp_ofReal_mul_I]

private theorem fourier_neg_nat_coe (m : ℕ) (x : ℝ) :
    fourier (-(m : ℤ)) (x : AddCircle Real.pi) =
      Real.cos (2 * (m : ℝ) * x) -
        Real.sin (2 * (m : ℝ) * x) * Complex.I := by
  rw [fourier_coe_apply]
  have harg :
      2 * (Real.pi : ℂ) * Complex.I * (-(m : ℂ)) * (x : ℂ) /
          (Real.pi : ℂ) =
        ((-(2 * (m : ℝ) * x) : ℝ) : ℂ) * Complex.I := by
    field_simp [Real.pi_ne_zero]
    push_cast
    ring
  simp only [Int.cast_neg, Int.cast_natCast]
  rw [harg, Complex.exp_ofReal_mul_I]
  rw [Real.cos_neg, Real.sin_neg]
  push_cast
  ring

private theorem fourier_term_pair (m : ℕ) (hm : 1 ≤ m) (x : ℝ) :
    fourierCoeff targetCircle (m : ℤ) •
          fourier (m : ℤ) (x : AddCircle Real.pi) +
        fourierCoeff targetCircle (-(m : ℤ)) •
          fourier (-(m : ℤ)) (x : AddCircle Real.pi) =
      ((-(4 / Real.pi) *
          (Real.cos (2 * (m : ℝ) * x) /
            (4 * (m : ℝ) ^ 2 - 1)) : ℝ) : ℂ) := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hdenR : 4 * (m : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
  have hdenC : 4 * (m : ℂ) ^ 2 - 1 ≠ 0 := by exact_mod_cast hdenR
  rw [targetCircle_coeff_all, targetCircle_coeff_all,
    fourier_nat_coe, fourier_neg_nat_coe]
  simp only [Int.cast_natCast, Int.cast_neg, neg_sq, smul_eq_mul]
  push_cast
  field_simp [Real.pi_ne_zero, hdenR, hdenC]
  ring

set_option maxHeartbeats 1000000 in
private theorem fourierSeries_complex_eq (x : ℝ) :
    (fourierSeries x : ℂ) = targetComplex x := by
  unfold fourierSeries
  let F : ℤ → ℂ := fun n =>
    fourierCoeff targetCircle n • fourier n (x : AddCircle Real.pi)
  have hpoint := has_pointwise_sum_fourier_series_of_summable
    targetCircle_coeff_summable (x : AddCircle Real.pi)
  have hF : Summable F := by
    simpa [F] using hpoint.summable
  have htsum : (∑' n : ℤ, F n) = targetComplex x := by
    simpa [F, targetCircle_coe] using hpoint.tsum_eq
  have hpos :
      (∑' n : ℕ+, F (n : ℤ)) =
        ∑' k : ℕ, F ((k + 1 : ℕ) : ℤ) := by
    simpa using (tsum_pnat_eq_tsum_succ
      (f := fun n : ℕ => F (n : ℤ)))
  have hneg :
      (∑' n : ℕ+, F (-(n : ℤ))) =
        ∑' k : ℕ, F (-((k + 1 : ℕ) : ℤ)) := by
    simpa using (tsum_pnat_eq_tsum_succ
      (f := fun n : ℕ => F (-(n : ℤ))))
  have hInt := summable_int_iff_summable_nat_and_neg.mp hF
  have hposSumm : Summable (fun k : ℕ => F ((k + 1 : ℕ) : ℤ)) :=
    (summable_nat_add_iff 1).2 hInt.1
  have hnegSumm : Summable (fun k : ℕ => F (-((k + 1 : ℕ) : ℤ))) :=
    (summable_nat_add_iff 1).2 hInt.2
  have hdecomp := tsum_int_eq_zero_add_tsum_pnat hF
  rw [hpos, hneg] at hdecomp
  have hdecomp' :
      (∑' n : ℤ, F n) = F 0 +
        ∑' k : ℕ,
          (F ((k + 1 : ℕ) : ℤ) + F (-((k + 1 : ℕ) : ℤ))) := by
    rw [hdecomp, hposSumm.tsum_add hnegSumm]
    ring
  have hpair : ∀ k : ℕ,
      F ((k + 1 : ℕ) : ℤ) + F (-((k + 1 : ℕ) : ℤ)) =
        ((-(4 / Real.pi) *
          (Real.cos (2 * (k + 1 : ℝ) * x) /
            (4 * (k + 1 : ℝ) ^ 2 - 1)) : ℝ) : ℂ) := by
    intro k
    simpa [F] using fourier_term_pair (k + 1) (by omega) x
  rw [tsum_congr hpair] at hdecomp'
  have hzero : F 0 = ((2 / Real.pi : ℝ) : ℂ) := by
    simp [F, targetCircle_coeff_all, fourier_zero]
  rw [hzero] at hdecomp'
  have hseries :
      (∑' k : ℕ,
        ((-(4 / Real.pi) *
          (Real.cos (2 * (k + 1 : ℝ) * x) /
            (4 * (k + 1 : ℝ) ^ 2 - 1)) : ℝ) : ℂ)) =
        (((-(4 / Real.pi)) *
          ∑' k : ℕ, Real.cos (2 * (k + 1 : ℝ) * x) /
            (4 * (k + 1 : ℝ) ^ 2 - 1) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_tsum]
    congr 1
    rw [tsum_mul_left]
  rw [hseries] at hdecomp'
  rw [htsum] at hdecomp'
  symm
  convert hdecomp' using 1
  norm_cast
  ring

private theorem fourierSeries_eq_target (x : ℝ) :
    fourierSeries x = target x := by
  apply Complex.ofReal_injective
  simpa [targetComplex] using fourierSeries_complex_eq x

theorem gap15 (f : ℝ → ℝ) (hf : ∀ x, f x = target x) :
    ∀ x, f x = fourierSeries x := by
  intro x
  calc
    f x = target x := hf x
    _ = fourierSeries x := (fourierSeries_eq_target x).symm

theorem gap16 :
    ∀ x, fourierSeries x = target x := by
  exact fourierSeries_eq_target

theorem gap17 (f : ℝ → ℝ) (hf : ∀ x, f x = target x) :
    ∀ x, f x = target x := by
  exact hf

end

end ProofGap.Exercise2957
