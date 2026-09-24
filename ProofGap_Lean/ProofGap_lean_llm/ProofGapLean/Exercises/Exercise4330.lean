import Mathlib.Analysis.Complex.Poisson
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4330

noncomputable section

open Complex Metric Real Set
open scoped Interval Topology BigOperators

def denominator (ρ φ ψ : ℝ) : ℝ :=
  1 + ρ ^ 2 - 2 * ρ * Real.cos (ψ - φ)

def kernel (ρ φ ψ : ℝ) : ℝ :=
  (1 - ρ * Real.cos (ψ - φ)) / denominator ρ φ ψ

def cartesianNumerator (ρ φ ψ : ℝ) : ℝ :=
  (Real.cos ψ - ρ * Real.cos φ) * Real.cos ψ +
    (Real.sin ψ - ρ * Real.sin φ) * Real.sin ψ

def cartesianDenominator (ρ φ ψ : ℝ) : ℝ :=
  (Real.cos ψ - ρ * Real.cos φ) ^ 2 +
    (Real.sin ψ - ρ * Real.sin φ) ^ 2

def Kcos (m : ℕ) (ρ φ : ℝ) : ℝ :=
  ∫ ψ in (0 : ℝ)..2 * Real.pi,
    Real.cos ((m : ℝ) * ψ) * kernel ρ φ ψ

def Ksin (m : ℕ) (ρ φ : ℝ) : ℝ :=
  ∫ ψ in (0 : ℝ)..2 * Real.pi,
    Real.sin ((m : ℝ) * ψ) * kernel ρ φ ψ

def kernelSeries (ρ θ : ℝ) : ℝ :=
  1 + ∑' n : ℕ,
    ρ ^ (n + 1) * Real.cos (((n + 1 : ℕ) : ℝ) * θ)

private def pois (ρ φ ψ : ℝ) : ℝ :=
  (1 - ρ ^ 2) / denominator ρ φ ψ

private lemma poissonKernel_circle_eq
    (ρ φ θ : ℝ) (hρ0 : 0 ≤ ρ) :
    poissonKernel 0 (ρ * Complex.exp (φ * Complex.I))
        (Complex.exp (θ * Complex.I)) = pois ρ φ θ := by
  simp only [poissonKernel, sub_zero, Complex.norm_mul, Complex.norm_real,
    Real.norm_eq_abs, norm_exp_ofReal_mul_I, abs_of_nonneg hρ0, mul_one,
    pois, denominator]
  congr 1
  · ring
  · rw [← Complex.normSq_eq_norm_sq, Complex.normSq_sub]
    simp [Complex.normSq_eq_norm_sq, Real.cos_sub]
    ring

private theorem poisson_complex_master
    (m : ℕ) (ρ φ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    (1 / (2 * Real.pi) : ℝ) •
        (∫ θ in (0 : ℝ)..2 * Real.pi,
          (pois ρ φ θ : ℂ) * Complex.exp (θ * Complex.I) ^ m) =
      (ρ * Complex.exp (φ * Complex.I)) ^ m := by
  let f : ℂ → ℂ := fun z => z ^ m
  let w : ℂ := ρ * Complex.exp (φ * Complex.I)
  have hf : DiffContOnCl ℂ f (Metric.ball 0 1) :=
    (differentiable_id.pow m).diffContOnCl
  have hw : w ∈ Metric.ball (0 : ℂ) 1 := by
    rw [Metric.mem_ball, dist_zero_right]
    simp [w, abs_of_nonneg hρ0, hρ1]
  have H := hf.circleAverage_poissonKernel_smul hw
  rw [Real.circleAverage_def] at H
  change
    (2 * Real.pi)⁻¹ •
        (∫ θ in (0 : ℝ)..2 * Real.pi,
          poissonKernel 0 w (circleMap 0 1 θ) •
            f (circleMap 0 1 θ)) =
      f w at H
  convert H using 1
  congr 1
  · simp [one_div]
  · apply intervalIntegral.integral_congr
    intro θ hθ
    simp only [f, w, circleMap, zero_add, one_mul]
    norm_num
    rw [poissonKernel_circle_eq ρ φ θ hρ0]

private lemma den_pos_of_nonneg_of_lt_one
    (ρ φ θ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    0 < denominator ρ φ θ := by
  have hc := Real.cos_le_one (θ - φ)
  have hs : 0 < (1 - ρ) ^ 2 := sq_pos_of_pos (sub_pos.mpr hρ1)
  dsimp [denominator]
  nlinarith

private lemma continuous_pois_mul_exp_pow
    (m : ℕ) (ρ φ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    Continuous (fun θ : ℝ =>
      (pois ρ φ θ : ℂ) * Complex.exp (θ * Complex.I) ^ m) := by
  have hd : Continuous (fun θ : ℝ => denominator ρ φ θ) := by
    simp only [denominator]
    fun_prop
  have hp : Continuous (fun θ : ℝ => pois ρ φ θ) := by
    apply Continuous.div (by fun_prop) hd
    intro θ
    exact ne_of_gt (den_pos_of_nonneg_of_lt_one ρ φ θ hρ0 hρ1)
  fun_prop

private lemma exp_nat_mul_I_re (m : ℕ) (x : ℝ) :
    (Complex.exp ((m : ℂ) * ((x : ℂ) * Complex.I))).re =
      Real.cos ((m : ℝ) * x) := by
  rw [show (m : ℂ) * ((x : ℂ) * Complex.I) =
    (((m : ℝ) * x : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact Complex.exp_ofReal_mul_I_re _

private lemma exp_nat_mul_I_im (m : ℕ) (x : ℝ) :
    (Complex.exp ((m : ℂ) * ((x : ℂ) * Complex.I))).im =
      Real.sin ((m : ℝ) * x) := by
  rw [show (m : ℂ) * ((x : ℂ) * Complex.I) =
    (((m : ℝ) * x : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact Complex.exp_ofReal_mul_I_im _

private lemma poisson_cos_master
    (m : ℕ) (ρ φ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    (1 / (2 * Real.pi) : ℝ) *
        (∫ θ in (0 : ℝ)..2 * Real.pi,
          pois ρ φ θ * Real.cos (m * θ)) =
      ρ ^ m * Real.cos (m * φ) := by
  have H := poisson_complex_master m ρ φ hρ0 hρ1
  have hg : IntervalIntegrable
      (fun θ : ℝ => (pois ρ φ θ : ℂ) *
        Complex.exp (θ * Complex.I) ^ m)
      MeasureTheory.volume 0 (2 * Real.pi) :=
    (continuous_pois_mul_exp_pow m ρ φ hρ0 hρ1).intervalIntegrable _ _
  have hcomm := Complex.reCLM.intervalIntegral_comp_comm hg
  simp only [Function.comp_apply, Complex.reCLM_apply] at hcomm
  have Hre := congrArg Complex.re H
  rw [Complex.smul_re] at Hre
  rw [← hcomm] at Hre
  have hre_pow : (((ρ : ℂ) ^ m).re) = ρ ^ m := by
    rw [← Complex.ofReal_pow]
    rfl
  have him_pow : (((ρ : ℂ) ^ m).im) = 0 := by
    rw [← Complex.ofReal_pow]
    rfl
  simpa [Complex.mul_re, ← Complex.exp_nat_mul, mul_assoc,
    mul_pow, exp_nat_mul_I_re, hre_pow, him_pow] using Hre

private lemma poisson_sin_master
    (m : ℕ) (ρ φ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    (1 / (2 * Real.pi) : ℝ) *
        (∫ θ in (0 : ℝ)..2 * Real.pi,
          pois ρ φ θ * Real.sin (m * θ)) =
      ρ ^ m * Real.sin (m * φ) := by
  have H := poisson_complex_master m ρ φ hρ0 hρ1
  have hg : IntervalIntegrable
      (fun θ : ℝ => (pois ρ φ θ : ℂ) *
        Complex.exp (θ * Complex.I) ^ m)
      MeasureTheory.volume 0 (2 * Real.pi) :=
    (continuous_pois_mul_exp_pow m ρ φ hρ0 hρ1).intervalIntegrable _ _
  have hcomm := Complex.imCLM.intervalIntegral_comp_comm hg
  simp only [Complex.imCLM_apply] at hcomm
  have Him := congrArg Complex.im H
  rw [Complex.smul_im] at Him
  rw [← hcomm] at Him
  have hre_pow : (((ρ : ℂ) ^ m).re) = ρ ^ m := by
    rw [← Complex.ofReal_pow]
    rfl
  have him_pow : (((ρ : ℂ) ^ m).im) = 0 := by
    rw [← Complex.ofReal_pow]
    rfl
  simpa [Complex.mul_im, ← Complex.exp_nat_mul, mul_assoc,
    mul_pow, exp_nat_mul_I_re, exp_nat_mul_I_im, hre_pow, him_pow] using Him

private lemma geometric_real_sum
    (ρ θ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    (∑' n : ℕ,
      ρ ^ (n + 1) * Real.cos (((n + 1 : ℕ) : ℝ) * θ)) =
      ((ρ : ℂ) * Complex.exp (θ * Complex.I) *
        (1 - (ρ : ℂ) * Complex.exp (θ * Complex.I))⁻¹).re := by
  let z : ℂ := ρ * Complex.exp (θ * Complex.I)
  have hz : ‖z‖ < 1 := by
    simp [z, abs_of_nonneg hρ0, hρ1]
  have Hc : HasSum (fun n : ℕ => z ^ (n + 1)) (z * (1 - z)⁻¹) := by
    simpa [pow_succ'] using
      (hasSum_geometric_of_norm_lt_one hz).mul_left z
  have Hr := Complex.hasSum_re Hc
  have hterm (n : ℕ) :
      (z ^ (n + 1)).re =
        ρ ^ (n + 1) *
          Real.cos (((n + 1 : ℕ) : ℝ) * θ) := by
    have hre_pow : (((ρ : ℂ) ^ (n + 1)).re) = ρ ^ (n + 1) := by
      rw [← Complex.ofReal_pow]
      rfl
    have him_pow : (((ρ : ℂ) ^ (n + 1)).im) = 0 := by
      rw [← Complex.ofReal_pow]
      rfl
    simp only [z, mul_pow, Complex.mul_re, hre_pow, him_pow,
      zero_mul, sub_zero]
    rw [← Complex.exp_nat_mul]
    exact congrArg (ρ ^ (n + 1) * ·) (exp_nat_mul_I_re (n + 1) θ)
  rw [← Hr.tsum_eq]
  apply tsum_congr
  intro n
  exact (hterm n).symm

private lemma ker_eq_ks
    (ρ θ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    kernel ρ 0 θ = kernelSeries ρ θ := by
  rw [kernelSeries, geometric_real_sum ρ θ hρ0 hρ1]
  have hd : denominator ρ 0 θ ≠ 0 :=
    ne_of_gt (den_pos_of_nonneg_of_lt_one ρ 0 θ hρ0 hρ1)
  simp only [kernel, denominator, sub_zero]
  rw [Complex.mul_re, Complex.inv_re, Complex.inv_im]
  simp only [Complex.mul_re, Complex.mul_im, Complex.one_re, Complex.sub_re,
    Complex.one_im, Complex.sub_im, Complex.neg_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, zero_add, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im, Complex.normSq_apply]
  simp only [sub_zero, add_zero, zero_sub, neg_neg]
  have hD :
      (1 - ρ * Real.cos θ) * (1 - ρ * Real.cos θ) +
          (- (ρ * Real.sin θ)) * (- (ρ * Real.sin θ)) =
        1 + ρ ^ 2 - 2 * ρ * Real.cos θ := by
    nlinarith [Real.sin_sq_add_cos_sq θ]
  rw [hD]
  have hd' : 1 + ρ ^ 2 - 2 * ρ * Real.cos θ ≠ 0 := by
    simpa [denominator] using hd
  have hd'' : 1 + ρ ^ 2 - ρ * Real.cos θ * 2 ≠ 0 := by
    convert hd' using 1 <;> ring
  field_simp [hd', hd'']
  nlinarith [Real.sin_sq_add_cos_sq θ]

private lemma integral_cos_nat_eq_zero (m : ℕ) (hm : 1 ≤ m) :
    (∫ ψ in (0 : ℝ)..2 * Real.pi,
      Real.cos ((m : ℝ) * ψ)) = 0 := by
  have hm0 : (m : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hm)
  rw [intervalIntegral.integral_comp_mul_left Real.cos hm0]
  simp only [zero_mul, integral_cos, Real.sin_zero, sub_zero]
  have hs := Real.sin_add_nat_mul_two_pi 0 m
  simp only [Real.sin_zero] at hs
  rw [show (m : ℝ) * (2 * Real.pi) =
    0 + (m : ℝ) * (2 * Real.pi) by ring, hs]
  simp

private lemma integral_sin_nat_eq_zero (m : ℕ) (hm : 1 ≤ m) :
    (∫ ψ in (0 : ℝ)..2 * Real.pi,
      Real.sin ((m : ℝ) * ψ)) = 0 := by
  have hm0 : (m : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hm)
  rw [intervalIntegral.integral_comp_mul_left Real.sin hm0]
  simp only [zero_mul, integral_sin, Real.cos_zero]
  rw [show (m : ℝ) * (2 * Real.pi) =
    (m : ℝ) * (2 * Real.pi) by rfl,
    Real.cos_nat_mul_two_pi m]
  simp

private lemma integral_cos_sq_nat (m : ℕ) (hm : 1 ≤ m) :
    (∫ θ in (0 : ℝ)..2 * Real.pi,
      Real.cos ((m : ℝ) * θ) ^ 2) = Real.pi := by
  have hpoint (θ : ℝ) :
      Real.cos ((m : ℝ) * θ) ^ 2 =
        (1 + Real.cos (((2 * m : ℕ) : ℝ) * θ)) / 2 := by
    rw [show (((2 * m : ℕ) : ℝ) * θ) =
      2 * ((m : ℝ) * θ) by norm_num; ring, Real.cos_two_mul]
    ring
  rw [intervalIntegral.integral_congr (fun θ _ => hpoint θ),
    intervalIntegral.integral_div,
    intervalIntegral.integral_add,
    intervalIntegral.integral_const,
    integral_cos_nat_eq_zero (2 * m) (by omega)]
  · simp [smul_eq_mul]
  · exact intervalIntegrable_const
  · exact (by fun_prop :
      Continuous (fun x : ℝ => Real.cos ((2 * m : ℕ) * x))).intervalIntegrable _ _

private lemma ker_eq_half_add_pois
    (ρ φ ψ : ℝ) (hden : denominator ρ φ ψ ≠ 0) :
    kernel ρ φ ψ = (1 / 2 : ℝ) + pois ρ φ ψ / 2 := by
  simp only [kernel, pois]
  field_simp [hden]
  simp only [denominator]
  ring

private lemma continuous_pois
    (ρ φ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    Continuous (pois ρ φ) := by
  have hd : Continuous (denominator ρ φ) := by
    change Continuous (fun θ : ℝ =>
      1 + ρ ^ 2 - 2 * ρ * Real.cos (θ - φ))
    fun_prop
  apply Continuous.div
      (show Continuous (fun _ : ℝ => 1 - ρ ^ 2) by fun_prop) hd
  intro θ
  exact ne_of_gt (den_pos_of_nonneg_of_lt_one ρ φ θ hρ0 hρ1)

private lemma interior_Kc
    (m : ℕ) (hm : 1 ≤ m) (ρ φ : ℝ)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    Kcos m ρ φ = Real.pi * ρ ^ m * Real.cos ((m : ℝ) * φ) := by
  have hp := poisson_cos_master m ρ φ hρ0 hρ1
  have hp' :
      (1 / 2 : ℝ) *
          (∫ θ in (0 : ℝ)..2 * Real.pi,
            pois ρ φ θ * Real.cos ((m : ℝ) * θ)) =
        Real.pi * (ρ ^ m * Real.cos ((m : ℝ) * φ)) := by
    calc
      (1 / 2 : ℝ) *
          (∫ θ in (0 : ℝ)..2 * Real.pi,
            pois ρ φ θ * Real.cos ((m : ℝ) * θ)) =
          Real.pi * ((1 / (2 * Real.pi) : ℝ) *
            (∫ θ in (0 : ℝ)..2 * Real.pi,
              pois ρ φ θ * Real.cos ((m : ℝ) * θ))) := by
                field_simp [Real.pi_ne_zero]
      _ = _ := by rw [hp]
  rw [Kcos]
  calc
    (∫ ψ in (0 : ℝ)..2 * Real.pi,
        Real.cos ((m : ℝ) * ψ) * kernel ρ φ ψ) =
      ∫ ψ in (0 : ℝ)..2 * Real.pi,
        ((1 / 2 : ℝ) * Real.cos ((m : ℝ) * ψ) +
          (1 / 2 : ℝ) *
            (pois ρ φ ψ * Real.cos ((m : ℝ) * ψ))) := by
      apply intervalIntegral.integral_congr
      intro ψ hψ
      simp only
      rw [ker_eq_half_add_pois ρ φ ψ
        (ne_of_gt (den_pos_of_nonneg_of_lt_one ρ φ ψ hρ0 hρ1))]
      ring
    _ = (1 / 2 : ℝ) *
          (∫ ψ in (0 : ℝ)..2 * Real.pi,
            Real.cos ((m : ℝ) * ψ)) +
        (1 / 2 : ℝ) *
          (∫ ψ in (0 : ℝ)..2 * Real.pi,
            pois ρ φ ψ * Real.cos ((m : ℝ) * ψ)) := by
      rw [intervalIntegral.integral_add]
      · simp
      · exact (by fun_prop :
          Continuous (fun ψ : ℝ =>
            (1 / 2 : ℝ) * Real.cos ((m : ℝ) * ψ))).intervalIntegrable _ _
      · exact ((continuous_pois ρ φ hρ0 hρ1).mul
          (by fun_prop)).const_mul (1 / 2) |>.intervalIntegrable _ _
    _ = _ := by
      rw [integral_cos_nat_eq_zero m hm]
      simpa only [mul_zero, zero_add, mul_assoc] using hp'

private lemma interior_Ks
    (m : ℕ) (hm : 1 ≤ m) (ρ φ : ℝ)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    Ksin m ρ φ = Real.pi * ρ ^ m * Real.sin ((m : ℝ) * φ) := by
  have hp := poisson_sin_master m ρ φ hρ0 hρ1
  have hp' :
      (1 / 2 : ℝ) *
          (∫ θ in (0 : ℝ)..2 * Real.pi,
            pois ρ φ θ * Real.sin ((m : ℝ) * θ)) =
        Real.pi * (ρ ^ m * Real.sin ((m : ℝ) * φ)) := by
    calc
      (1 / 2 : ℝ) *
          (∫ θ in (0 : ℝ)..2 * Real.pi,
            pois ρ φ θ * Real.sin ((m : ℝ) * θ)) =
          Real.pi * ((1 / (2 * Real.pi) : ℝ) *
            (∫ θ in (0 : ℝ)..2 * Real.pi,
              pois ρ φ θ * Real.sin ((m : ℝ) * θ))) := by
                field_simp [Real.pi_ne_zero]
      _ = _ := by rw [hp]
  rw [Ksin]
  calc
    (∫ ψ in (0 : ℝ)..2 * Real.pi,
        Real.sin ((m : ℝ) * ψ) * kernel ρ φ ψ) =
      ∫ ψ in (0 : ℝ)..2 * Real.pi,
        ((1 / 2 : ℝ) * Real.sin ((m : ℝ) * ψ) +
          (1 / 2 : ℝ) *
            (pois ρ φ ψ * Real.sin ((m : ℝ) * ψ))) := by
      apply intervalIntegral.integral_congr
      intro ψ hψ
      simp only
      rw [ker_eq_half_add_pois ρ φ ψ
        (ne_of_gt (den_pos_of_nonneg_of_lt_one ρ φ ψ hρ0 hρ1))]
      ring
    _ = (1 / 2 : ℝ) *
          (∫ ψ in (0 : ℝ)..2 * Real.pi,
            Real.sin ((m : ℝ) * ψ)) +
        (1 / 2 : ℝ) *
          (∫ ψ in (0 : ℝ)..2 * Real.pi,
            pois ρ φ ψ * Real.sin ((m : ℝ) * ψ)) := by
      rw [intervalIntegral.integral_add]
      · simp
      · exact (by fun_prop :
          Continuous (fun ψ : ℝ =>
            (1 / 2 : ℝ) * Real.sin ((m : ℝ) * ψ))).intervalIntegrable _ _
      · exact ((continuous_pois ρ φ hρ0 hρ1).mul
          (by fun_prop)).const_mul (1 / 2) |>.intervalIntegrable _ _
    _ = _ := by
      rw [integral_sin_nat_eq_zero m hm]
      simpa only [mul_zero, zero_add, mul_assoc] using hp'

private lemma ker_one_eq_half
    (φ ψ : ℝ) (hden : denominator 1 φ ψ ≠ 0) :
    kernel 1 φ ψ = 1 / 2 := by
  rw [ker_eq_half_add_pois 1 φ ψ hden]
  simp [pois]

private lemma ker_one_ae_eq_half (φ : ℝ) :
    ∀ᵐ ψ : ℝ, kernel 1 φ ψ = 1 / 2 := by
  let S : Set ℝ :=
    Set.range (fun n : ℤ => φ + (n : ℝ) * (2 * Real.pi))
  have hSc : S.Countable := Set.countable_range _
  filter_upwards [hSc.ae_notMem MeasureTheory.volume] with ψ hψ
  apply ker_one_eq_half
  intro hzero
  have hc : Real.cos (ψ - φ) = 1 := by
    simp only [denominator, one_pow, one_mul] at hzero
    linarith
  obtain ⟨n, hn⟩ := (Real.cos_eq_one_iff (ψ - φ)).mp hc
  apply hψ
  refine ⟨n, ?_⟩
  linarith

private lemma boundary_Kc_half (m : ℕ) (φ : ℝ) :
    Kcos m 1 φ =
      (1 / 2 : ℝ) *
        (∫ ψ in (0 : ℝ)..2 * Real.pi,
          Real.cos ((m : ℝ) * ψ)) := by
  rw [Kcos]
  calc
    (∫ ψ in (0 : ℝ)..2 * Real.pi,
        Real.cos ((m : ℝ) * ψ) * kernel 1 φ ψ) =
      ∫ ψ in (0 : ℝ)..2 * Real.pi,
        Real.cos ((m : ℝ) * ψ) * (1 / 2 : ℝ) := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [ker_one_ae_eq_half φ] with ψ hψ
      intro hmem
      rw [hψ]
    _ = _ := by
      rw [intervalIntegral.integral_mul_const]
      ring

private lemma boundary_Ks_half (m : ℕ) (φ : ℝ) :
    Ksin m 1 φ =
      (1 / 2 : ℝ) *
        (∫ ψ in (0 : ℝ)..2 * Real.pi,
          Real.sin ((m : ℝ) * ψ)) := by
  rw [Ksin]
  calc
    (∫ ψ in (0 : ℝ)..2 * Real.pi,
        Real.sin ((m : ℝ) * ψ) * kernel 1 φ ψ) =
      ∫ ψ in (0 : ℝ)..2 * Real.pi,
        Real.sin ((m : ℝ) * ψ) * (1 / 2 : ℝ) := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [ker_one_ae_eq_half φ] with ψ hψ
      intro hmem
      rw [hψ]
    _ = _ := by
      rw [intervalIntegral.integral_mul_const]
      ring

private lemma ker_add_two_pi (ρ φ x : ℝ) :
    kernel ρ φ (x + 2 * Real.pi) = kernel ρ φ x := by
  simp only [kernel, denominator]
  rw [show x + 2 * Real.pi - φ = (x - φ) + 2 * Real.pi by ring,
    Real.cos_add_two_pi]

private lemma ker_shift_center (ρ φ θ : ℝ) :
    kernel ρ φ (θ + φ) = kernel ρ 0 θ := by
  simp only [kernel, denominator]
  rw [show θ + φ - φ = θ - 0 by ring]

private lemma periodic_cos_ker (m : ℕ) (ρ φ : ℝ) :
    Function.Periodic
      (fun x : ℝ => Real.cos ((m : ℝ) * x) * kernel ρ φ x)
      (2 * Real.pi) := by
  intro x
  change
    Real.cos ((m : ℝ) * (x + 2 * Real.pi)) *
        kernel ρ φ (x + 2 * Real.pi) =
      Real.cos ((m : ℝ) * x) * kernel ρ φ x
  rw [ker_add_two_pi]
  congr 1
  rw [show (m : ℝ) * (x + 2 * Real.pi) =
    (m : ℝ) * x + (m : ℝ) * (2 * Real.pi) by ring]
  exact Real.cos_add_nat_mul_two_pi ((m : ℝ) * x) m

private lemma periodic_sin_ker (m : ℕ) (ρ φ : ℝ) :
    Function.Periodic
      (fun x : ℝ => Real.sin ((m : ℝ) * x) * kernel ρ φ x)
      (2 * Real.pi) := by
  intro x
  change
    Real.sin ((m : ℝ) * (x + 2 * Real.pi)) *
        kernel ρ φ (x + 2 * Real.pi) =
      Real.sin ((m : ℝ) * x) * kernel ρ φ x
  rw [ker_add_two_pi]
  congr 1
  rw [show (m : ℝ) * (x + 2 * Real.pi) =
    (m : ℝ) * x + (m : ℝ) * (2 * Real.pi) by ring]
  exact Real.sin_add_nat_mul_two_pi ((m : ℝ) * x) m

private lemma shift_Kc (m : ℕ) (ρ φ : ℝ) :
    Kcos m ρ φ =
      ∫ θ in (0 : ℝ)..2 * Real.pi,
        Real.cos ((m : ℝ) * (θ + φ)) * kernel ρ 0 θ := by
  let f : ℝ → ℝ :=
    fun x => Real.cos ((m : ℝ) * x) * kernel ρ φ x
  have hp : Function.Periodic f (2 * Real.pi) :=
    periodic_cos_ker m ρ φ
  have H := hp.intervalIntegral_add_eq 0 φ
  change
    (∫ x in (0 : ℝ)..0 + 2 * Real.pi, f x) =
      ∫ x in φ..φ + 2 * Real.pi, f x at H
  rw [zero_add] at H
  rw [Kcos, H]
  calc
    (∫ x in φ..φ + 2 * Real.pi, f x) =
        ∫ θ in (0 : ℝ)..2 * Real.pi, f (θ + φ) := by
      symm
      convert intervalIntegral.integral_comp_add_right
        (a := 0) (b := 2 * Real.pi) f φ using 1 <;> ring
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro θ hθ
      simp only [f]
      rw [ker_shift_center]

private lemma shift_Ks (m : ℕ) (ρ φ : ℝ) :
    Ksin m ρ φ =
      ∫ θ in (0 : ℝ)..2 * Real.pi,
        Real.sin ((m : ℝ) * (θ + φ)) * kernel ρ 0 θ := by
  let f : ℝ → ℝ :=
    fun x => Real.sin ((m : ℝ) * x) * kernel ρ φ x
  have hp : Function.Periodic f (2 * Real.pi) :=
    periodic_sin_ker m ρ φ
  have H := hp.intervalIntegral_add_eq 0 φ
  change
    (∫ x in (0 : ℝ)..0 + 2 * Real.pi, f x) =
      ∫ x in φ..φ + 2 * Real.pi, f x at H
  rw [zero_add] at H
  rw [Ksin, H]
  calc
    (∫ x in φ..φ + 2 * Real.pi, f x) =
        ∫ θ in (0 : ℝ)..2 * Real.pi, f (θ + φ) := by
      symm
      convert intervalIntegral.integral_comp_add_right
        (a := 0) (b := 2 * Real.pi) f φ using 1 <;> ring
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro θ hθ
      simp only [f]
      rw [ker_shift_center]

private lemma den_pos_of_one_lt
    (ρ φ θ : ℝ) (hρ : 1 < ρ) :
    0 < denominator ρ φ θ := by
  have hc := Real.cos_le_one (θ - φ)
  have hs : 0 < (ρ - 1) ^ 2 := sq_pos_of_pos (sub_pos.mpr hρ)
  have hρ0 : 0 < ρ := lt_trans (by norm_num) hρ
  dsimp [denominator]
  nlinarith

private lemma den_inv_pos_of_one_lt
    (ρ φ θ : ℝ) (hρ : 1 < ρ) :
    0 < denominator ρ⁻¹ φ θ := by
  apply den_pos_of_nonneg_of_lt_one
  · positivity
  · exact inv_lt_one_of_one_lt₀ hρ

private lemma den_scale_inv (ρ φ θ : ℝ) (hρ : 1 < ρ) :
    denominator ρ φ θ = ρ ^ 2 * denominator ρ⁻¹ φ θ := by
  have hρne : ρ ≠ 0 := ne_of_gt (lt_trans (by norm_num) hρ)
  simp only [denominator]
  field_simp [hρne]
  ring

private lemma correction_inv (ρ φ θ : ℝ) (hρ : 1 < ρ) :
    (1 - ρ ^ 2) / (2 * denominator ρ φ θ) =
      ((ρ⁻¹) ^ 2 - 1) / (2 * denominator ρ⁻¹ φ θ) := by
  have hρne : ρ ≠ 0 := ne_of_gt (lt_trans (by norm_num) hρ)
  rw [den_scale_inv ρ φ θ hρ]
  field_simp [hρne]

private lemma ker_inversion (ρ φ θ : ℝ) (hρ : 1 < ρ) :
    kernel ρ φ θ = 1 - kernel ρ⁻¹ φ θ := by
  have hd : denominator ρ φ θ ≠ 0 :=
    ne_of_gt (den_pos_of_one_lt ρ φ θ hρ)
  have hdi : denominator ρ⁻¹ φ θ ≠ 0 :=
    ne_of_gt (den_inv_pos_of_one_lt ρ φ θ hρ)
  rw [ker_eq_half_add_pois ρ φ θ hd,
    ker_eq_half_add_pois ρ⁻¹ φ θ hdi]
  have hc := correction_inv ρ φ θ hρ
  simp only [pois]
  have hc' :
      (1 - ρ ^ 2) / denominator ρ φ θ / 2 =
        - ((1 - (ρ⁻¹) ^ 2) / denominator ρ⁻¹ φ θ / 2) := by
    calc
      (1 - ρ ^ 2) / denominator ρ φ θ / 2 =
          (1 - ρ ^ 2) / (2 * denominator ρ φ θ) := by ring
      _ = ((ρ⁻¹) ^ 2 - 1) /
          (2 * denominator ρ⁻¹ φ θ) := hc
      _ = - ((1 - (ρ⁻¹) ^ 2) /
          denominator ρ⁻¹ φ θ / 2) := by ring
  rw [hc']
  ring

private lemma continuous_ker_of_den_ne
    (ρ φ : ℝ) (hden : ∀ θ, denominator ρ φ θ ≠ 0) :
    Continuous (kernel ρ φ) := by
  have hd : Continuous (denominator ρ φ) := by
    change Continuous (fun θ : ℝ =>
      1 + ρ ^ 2 - 2 * ρ * Real.cos (θ - φ))
    fun_prop
  apply Continuous.div
      (show Continuous (fun θ : ℝ =>
        1 - ρ * Real.cos (θ - φ)) by fun_prop) hd
  exact hden

private lemma outer_Kc_inv
    (m : ℕ) (hm : 1 ≤ m) (ρ φ : ℝ) (hρ : 1 < ρ) :
    Kcos m ρ φ = -Kcos m ρ⁻¹ φ := by
  rw [Kcos, Kcos]
  calc
    (∫ ψ in (0 : ℝ)..2 * Real.pi,
        Real.cos ((m : ℝ) * ψ) * kernel ρ φ ψ) =
      ∫ ψ in (0 : ℝ)..2 * Real.pi,
        (Real.cos ((m : ℝ) * ψ) -
          Real.cos ((m : ℝ) * ψ) * kernel ρ⁻¹ φ ψ) := by
      apply intervalIntegral.integral_congr
      intro ψ hψ
      simp only
      rw [ker_inversion ρ φ ψ hρ]
      ring
    _ = (∫ ψ in (0 : ℝ)..2 * Real.pi,
          Real.cos ((m : ℝ) * ψ)) -
        ∫ ψ in (0 : ℝ)..2 * Real.pi,
          Real.cos ((m : ℝ) * ψ) * kernel ρ⁻¹ φ ψ := by
      rw [intervalIntegral.integral_sub]
      · exact (by fun_prop :
          Continuous (fun ψ : ℝ =>
            Real.cos ((m : ℝ) * ψ))).intervalIntegrable _ _
      · exact ((by fun_prop :
          Continuous (fun ψ : ℝ =>
            Real.cos ((m : ℝ) * ψ))).mul
            (continuous_ker_of_den_ne ρ⁻¹ φ
              (fun θ => ne_of_gt (den_inv_pos_of_one_lt ρ φ θ hρ))))
          |>.intervalIntegrable _ _
    _ = _ := by rw [integral_cos_nat_eq_zero m hm, zero_sub]

private lemma outer_Ks_inv
    (m : ℕ) (hm : 1 ≤ m) (ρ φ : ℝ) (hρ : 1 < ρ) :
    Ksin m ρ φ = -Ksin m ρ⁻¹ φ := by
  rw [Ksin, Ksin]
  calc
    (∫ ψ in (0 : ℝ)..2 * Real.pi,
        Real.sin ((m : ℝ) * ψ) * kernel ρ φ ψ) =
      ∫ ψ in (0 : ℝ)..2 * Real.pi,
        (Real.sin ((m : ℝ) * ψ) -
          Real.sin ((m : ℝ) * ψ) * kernel ρ⁻¹ φ ψ) := by
      apply intervalIntegral.integral_congr
      intro ψ hψ
      simp only
      rw [ker_inversion ρ φ ψ hρ]
      ring
    _ = (∫ ψ in (0 : ℝ)..2 * Real.pi,
          Real.sin ((m : ℝ) * ψ)) -
        ∫ ψ in (0 : ℝ)..2 * Real.pi,
          Real.sin ((m : ℝ) * ψ) * kernel ρ⁻¹ φ ψ := by
      rw [intervalIntegral.integral_sub]
      · exact (by fun_prop :
          Continuous (fun ψ : ℝ =>
            Real.sin ((m : ℝ) * ψ))).intervalIntegrable _ _
      · exact ((by fun_prop :
          Continuous (fun ψ : ℝ =>
            Real.sin ((m : ℝ) * ψ))).mul
            (continuous_ker_of_den_ne ρ⁻¹ φ
              (fun θ => ne_of_gt (den_inv_pos_of_one_lt ρ φ θ hρ))))
          |>.intervalIntegrable _ _
    _ = _ := by rw [integral_sin_nat_eq_zero m hm, zero_sub]

theorem gap1
    (ρ φ ψ : ℝ) (hden : cartesianDenominator ρ φ ψ ≠ 0) :
    cartesianNumerator ρ φ ψ / cartesianDenominator ρ φ ψ =
      (1 - ρ * Real.cos (ψ - φ)) /
        cartesianDenominator ρ φ ψ := by
  congr 1
  simp only [cartesianNumerator, Real.cos_sub]
  nlinarith [Real.sin_sq_add_cos_sq ψ]

theorem gap2 (ρ φ ψ : ℝ) :
    cartesianDenominator ρ φ ψ = denominator ρ φ ψ := by
  simp only [cartesianDenominator, denominator, Real.cos_sub]
  nlinarith [Real.sin_sq_add_cos_sq ψ, Real.sin_sq_add_cos_sq φ]

theorem gap3
    (ρ φ ψ : ℝ) (hden : cartesianDenominator ρ φ ψ ≠ 0) :
    cartesianNumerator ρ φ ψ / cartesianDenominator ρ φ ψ =
      kernel ρ φ ψ := by
  rw [gap1 ρ φ ψ hden, gap2]
  rfl

theorem gap4
    (φ ψ : ℝ) (hregular : denominator 1 φ ψ ≠ 0) :
    kernel 1 φ ψ = 1 / 2 := by
  exact ker_one_eq_half φ ψ hregular

theorem gap5 (m : ℕ) (hm : 1 ≤ m) (φ : ℝ) :
    Kcos m 1 φ =
      (1 / 2 : ℝ) *
        (∫ ψ in (0 : ℝ)..2 * Real.pi,
          Real.cos ((m : ℝ) * ψ)) := by
  exact boundary_Kc_half m φ

theorem gap6 (m : ℕ) (hm : 1 ≤ m) :
    (∫ ψ in (0 : ℝ)..2 * Real.pi,
      Real.cos ((m : ℝ) * ψ)) = 0 := by
  exact integral_cos_nat_eq_zero m hm

theorem gap7 (m : ℕ) (hm : 1 ≤ m) (φ : ℝ) :
    Kcos m 1 φ = 0 := by
  rw [gap5 m hm φ, gap6 m hm, mul_zero]

theorem gap8 (m : ℕ) (hm : 1 ≤ m) (φ : ℝ) :
    Ksin m 1 φ =
      (1 / 2 : ℝ) *
        (∫ ψ in (0 : ℝ)..2 * Real.pi,
          Real.sin ((m : ℝ) * ψ)) := by
  exact boundary_Ks_half m φ

theorem gap9 (m : ℕ) (hm : 1 ≤ m) :
    (∫ ψ in (0 : ℝ)..2 * Real.pi,
      Real.sin ((m : ℝ) * ψ)) = 0 := by
  exact integral_sin_nat_eq_zero m hm

theorem gap10 (m : ℕ) (hm : 1 ≤ m) (φ : ℝ) :
    Ksin m 1 φ = 0 := by
  rw [gap8 m hm φ, gap9 m hm, mul_zero]

theorem gap11
    (ρ θ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    kernel ρ 0 θ = kernelSeries ρ θ := by
  exact ker_eq_ks ρ θ hρ0 hρ1

theorem gap12
    (m : ℕ) (hm : 1 ≤ m) (ρ φ : ℝ)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    Kcos m ρ φ =
      ∫ θ in (0 : ℝ)..2 * Real.pi,
        Real.cos ((m : ℝ) * (θ + φ)) * kernelSeries ρ θ := by
  rw [shift_Kc]
  apply intervalIntegral.integral_congr
  intro θ hθ
  simp only
  rw [gap11 ρ θ hρ0 hρ1]

theorem gap13
    (m : ℕ) (hm : 1 ≤ m) (ρ φ : ℝ)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    Kcos m ρ φ =
      ∫ θ in (0 : ℝ)..2 * Real.pi,
        (Real.cos ((m : ℝ) * θ) * Real.cos ((m : ℝ) * φ) -
          Real.sin ((m : ℝ) * θ) * Real.sin ((m : ℝ) * φ)) *
          kernelSeries ρ θ := by
  rw [gap12 m hm ρ φ hρ0 hρ1]
  apply intervalIntegral.integral_congr
  intro θ hθ
  simp only
  rw [show (m : ℝ) * (θ + φ) =
    (m : ℝ) * θ + (m : ℝ) * φ by ring, Real.cos_add]

theorem gap14
    (m : ℕ) (hm : 1 ≤ m) (ρ φ : ℝ)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    Kcos m ρ φ =
      ρ ^ m * Real.cos ((m : ℝ) * φ) *
        (∫ θ in (0 : ℝ)..2 * Real.pi,
          Real.cos ((m : ℝ) * θ) ^ 2) := by
  rw [interior_Kc m hm ρ φ hρ0 hρ1, integral_cos_sq_nat m hm]
  ring

theorem gap15
    (m : ℕ) (hm : 1 ≤ m) (ρ φ : ℝ)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    ρ ^ m * Real.cos ((m : ℝ) * φ) *
        (∫ θ in (0 : ℝ)..2 * Real.pi,
          Real.cos ((m : ℝ) * θ) ^ 2) =
      Real.pi * ρ ^ m * Real.cos ((m : ℝ) * φ) := by
  rw [integral_cos_sq_nat m hm]
  ring

theorem gap16 (m : ℕ) (hm : 1 ≤ m) :
    (∫ θ in (0 : ℝ)..2 * Real.pi,
      Real.cos ((m : ℝ) * θ) ^ 2) = Real.pi := by
  exact integral_cos_sq_nat m hm

theorem gap17
    (m : ℕ) (hm : 1 ≤ m) (ρ φ : ℝ)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    Kcos m ρ φ =
      Real.pi * ρ ^ m * Real.cos ((m : ℝ) * φ) := by
  exact interior_Kc m hm ρ φ hρ0 hρ1

theorem gap18
    (m : ℕ) (hm : 1 ≤ m) (ρ φ : ℝ)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    Ksin m ρ φ =
      ∫ θ in (0 : ℝ)..2 * Real.pi,
        Real.sin ((m : ℝ) * (θ + φ)) * kernelSeries ρ θ := by
  rw [shift_Ks]
  apply intervalIntegral.integral_congr
  intro θ hθ
  simp only
  rw [gap11 ρ θ hρ0 hρ1]

theorem gap19
    (m : ℕ) (hm : 1 ≤ m) (ρ φ : ℝ)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    Ksin m ρ φ =
      Real.pi * ρ ^ m * Real.sin ((m : ℝ) * φ) := by
  exact interior_Ks m hm ρ φ hρ0 hρ1

theorem gap20
    (m : ℕ) (hm : 1 ≤ m) (ρ φ : ℝ)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    Kcos m ρ φ =
        Real.pi * ρ ^ m * Real.cos ((m : ℝ) * φ) ∧
      Ksin m ρ φ =
        Real.pi * ρ ^ m * Real.sin ((m : ℝ) * φ) := by
  exact ⟨gap17 m hm ρ φ hρ0 hρ1, gap19 m hm ρ φ hρ0 hρ1⟩

theorem gap21
    (ρ φ ψ : ℝ) (hρ : 1 < ρ) :
    kernel ρ φ ψ =
      (1 - ρ * Real.cos (ψ - φ)) / denominator ρ φ ψ := by
  rfl

theorem gap22 (ρ φ ψ : ℝ) :
    1 - ρ * Real.cos (ψ - φ) =
      (1 / 2 : ℝ) *
        (denominator ρ φ ψ + (1 - ρ ^ 2)) := by
  simp only [denominator]
  ring

theorem gap23
    (ρ φ ψ : ℝ) (hden : denominator ρ φ ψ ≠ 0) :
    kernel ρ φ ψ =
      1 / 2 + (1 - ρ ^ 2) / (2 * denominator ρ φ ψ) := by
  rw [ker_eq_half_add_pois ρ φ ψ hden]
  simp only [pois]
  ring

private lemma continuous_outer_correction
    (ρ φ : ℝ) (hρ : 1 < ρ) :
    Continuous (fun ψ : ℝ =>
      (1 - ρ ^ 2) / (2 * denominator ρ φ ψ)) := by
  have hd : Continuous (fun ψ : ℝ => 2 * denominator ρ φ ψ) := by
    simp only [denominator]
    fun_prop
  apply Continuous.div (by fun_prop) hd
  intro ψ
  exact mul_ne_zero (by norm_num)
    (ne_of_gt (den_pos_of_one_lt ρ φ ψ hρ))

theorem gap24
    (m : ℕ) (hm : 1 ≤ m) (ρ φ : ℝ) (hρ : 1 < ρ) :
    Kcos m ρ φ =
      ∫ ψ in (0 : ℝ)..2 * Real.pi,
        Real.cos ((m : ℝ) * ψ) *
          ((1 - ρ ^ 2) / (2 * denominator ρ φ ψ)) := by
  rw [Kcos]
  calc
    (∫ ψ in (0 : ℝ)..2 * Real.pi,
        Real.cos ((m : ℝ) * ψ) * kernel ρ φ ψ) =
      ∫ ψ in (0 : ℝ)..2 * Real.pi,
        (Real.cos ((m : ℝ) * ψ) * (1 / 2 : ℝ) +
          Real.cos ((m : ℝ) * ψ) *
            ((1 - ρ ^ 2) / (2 * denominator ρ φ ψ))) := by
      apply intervalIntegral.integral_congr
      intro ψ hψ
      simp only
      rw [gap23 ρ φ ψ
        (ne_of_gt (den_pos_of_one_lt ρ φ ψ hρ))]
      ring
    _ = (∫ ψ in (0 : ℝ)..2 * Real.pi,
          Real.cos ((m : ℝ) * ψ) * (1 / 2 : ℝ)) +
        ∫ ψ in (0 : ℝ)..2 * Real.pi,
          Real.cos ((m : ℝ) * ψ) *
            ((1 - ρ ^ 2) / (2 * denominator ρ φ ψ)) := by
      rw [intervalIntegral.integral_add]
      · exact (by fun_prop :
          Continuous (fun ψ : ℝ =>
            Real.cos ((m : ℝ) * ψ) * (1 / 2 : ℝ)))
          |>.intervalIntegrable _ _
      · exact ((by fun_prop :
          Continuous (fun ψ : ℝ =>
            Real.cos ((m : ℝ) * ψ))).mul
              (continuous_outer_correction ρ φ hρ))
          |>.intervalIntegrable _ _
    _ = _ := by
      rw [intervalIntegral.integral_mul_const, gap6 m hm]
      ring

theorem gap25
    (ρ φ ψ : ℝ) (hρ : 1 < ρ) :
    (1 - ρ ^ 2) / (2 * denominator ρ φ ψ) =
      ((ρ⁻¹) ^ 2 - 1) /
        (2 * denominator (ρ⁻¹) φ ψ) := by
  exact correction_inv ρ φ ψ hρ

theorem gap26
    (ρ φ ψ : ℝ) (hρ : 1 < ρ) :
    denominator ρ φ ψ =
      ρ ^ 2 * denominator (ρ⁻¹) φ ψ := by
  exact den_scale_inv ρ φ ψ hρ

theorem gap27
    (m : ℕ) (hm : 1 ≤ m) (ρ φ : ℝ) (hρ : 1 < ρ) :
    Kcos m ρ φ = -Kcos m (ρ⁻¹) φ := by
  exact outer_Kc_inv m hm ρ φ hρ

theorem gap28
    (m : ℕ) (hm : 1 ≤ m) (ρ φ : ℝ) (hρ : 1 < ρ) :
    Kcos m (ρ⁻¹) φ =
      Real.pi * (ρ⁻¹) ^ m * Real.cos ((m : ℝ) * φ) := by
  apply gap17 m hm
  · exact le_of_lt (inv_pos.mpr (lt_trans (by norm_num) hρ))
  · exact inv_lt_one_of_one_lt₀ hρ

theorem gap29
    (m : ℕ) (ρ : ℝ) (hρ : 1 < ρ) :
    (ρ⁻¹) ^ m = 1 / ρ ^ m := by
  simpa only [one_div] using (inv_pow ρ m)

theorem gap30
    (m : ℕ) (hm : 1 ≤ m) (ρ φ : ℝ) (hρ : 1 < ρ) :
    Kcos m ρ φ =
      -(Real.pi / ρ ^ m) * Real.cos ((m : ℝ) * φ) := by
  rw [gap27 m hm ρ φ hρ, gap28 m hm ρ φ hρ,
    gap29 m ρ hρ]
  ring

theorem gap31
    (m : ℕ) (hm : 1 ≤ m) (ρ φ : ℝ) (hρ : 1 < ρ) :
    Ksin m ρ φ = -Ksin m (ρ⁻¹) φ := by
  exact outer_Ks_inv m hm ρ φ hρ

theorem gap32
    (m : ℕ) (hm : 1 ≤ m) (ρ φ : ℝ) (hρ : 1 < ρ) :
    Ksin m ρ φ =
      -(Real.pi / ρ ^ m) * Real.sin ((m : ℝ) * φ) := by
  rw [gap31 m hm ρ φ hρ,
    gap19 m hm ρ⁻¹ φ
      (le_of_lt (inv_pos.mpr (lt_trans (by norm_num) hρ)))
      (inv_lt_one_of_one_lt₀ hρ),
    gap29 m ρ hρ]
  ring

theorem gap33
    (m : ℕ) (hm : 1 ≤ m) (ρ φ : ℝ) (hρ : 1 < ρ) :
    Kcos m ρ φ =
        -(Real.pi / ρ ^ m) * Real.cos ((m : ℝ) * φ) ∧
      Ksin m ρ φ =
        -(Real.pi / ρ ^ m) * Real.sin ((m : ℝ) * φ) := by
  exact ⟨gap30 m hm ρ φ hρ, gap32 m hm ρ φ hρ⟩

theorem gap34
    (m : ℕ) (hm : 1 ≤ m) (ρ φ : ℝ) (hρ0 : 0 ≤ ρ) :
    Kcos m ρ φ =
      if ρ < 1 then
        Real.pi * ρ ^ m * Real.cos ((m : ℝ) * φ)
      else if ρ = 1 then 0
      else -(Real.pi / ρ ^ m) * Real.cos ((m : ℝ) * φ) := by
  by_cases hρ1 : ρ < 1
  · rw [if_pos hρ1]
    exact gap17 m hm ρ φ hρ0 hρ1
  · rw [if_neg hρ1]
    by_cases heq : ρ = 1
    · rw [if_pos heq, heq]
      exact gap7 m hm φ
    · rw [if_neg heq]
      have hgt : 1 < ρ := by
        have hle : 1 ≤ ρ := le_of_not_gt hρ1
        exact lt_of_le_of_ne hle (Ne.symm heq)
      exact gap30 m hm ρ φ hgt

theorem gap35
    (m : ℕ) (hm : 1 ≤ m) (ρ φ : ℝ) (hρ0 : 0 ≤ ρ) :
    Ksin m ρ φ =
      if ρ < 1 then
        Real.pi * ρ ^ m * Real.sin ((m : ℝ) * φ)
      else if ρ = 1 then 0
      else -(Real.pi / ρ ^ m) * Real.sin ((m : ℝ) * φ) := by
  by_cases hρ1 : ρ < 1
  · rw [if_pos hρ1]
    exact gap19 m hm ρ φ hρ0 hρ1
  · rw [if_neg hρ1]
    by_cases heq : ρ = 1
    · rw [if_pos heq, heq]
      exact gap10 m hm φ
    · rw [if_neg heq]
      have hgt : 1 < ρ := by
        have hle : 1 ≤ ρ := le_of_not_gt hρ1
        exact lt_of_le_of_ne hle (Ne.symm heq)
      exact gap32 m hm ρ φ hgt

end

end ProofGap.Exercise4330
