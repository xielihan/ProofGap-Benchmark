import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.LogTrigonometric
import Mathlib.Analysis.SpecialFunctions.Integrals.PosLogEqCircleAverage
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3732

noncomputable section

open Filter MeasureTheory
open scoped Interval Topology

def integralValue (a b : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..Real.pi / 2,
    Real.log (a ^ 2 * Real.sin x ^ 2 + b ^ 2 * Real.cos x ^ 2)

def partialA (a b : ℝ) : ℝ :=
  deriv (fun s => integralValue s b) a

def tangentIntegral (a b : ℝ) : ℝ :=
  ∫ t in Set.Ioi (0 : ℝ),
    t ^ 2 / ((t ^ 2 + 1) * (t ^ 2 + b ^ 2 / a ^ 2))

def integrationConstant (b : ℝ) : ℝ :=
  integralValue b b - Real.pi * Real.log (2 * b)

private theorem half_circle_log_distance_zero (r : ℝ) (hr : |r| < 1) :
    (∫ t in (0 : ℝ)..Real.pi,
      Real.log ‖circleMap 0 1 t - (-(r : ℂ))‖) = 0 := by
  let F : ℝ → ℝ := fun t =>
    Real.log ‖circleMap 0 1 t - (-(r : ℂ))‖
  have hra : ‖(-(r : ℂ))‖ < 1 := by
    simpa using hr
  have hcirc :=
    circleAverage_log_norm_sub_const₀ (a := (-(r : ℂ))) hra
  have havg :
      (2 * Real.pi)⁻¹ *
          (∫ t in (0 : ℝ)..2 * Real.pi, F t) = 0 := by
    simpa only [Real.circleAverage, smul_eq_mul, F] using hcirc
  have hcoef : (2 * Real.pi)⁻¹ ≠ 0 :=
    inv_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)
  have hfull :
      (∫ t in (0 : ℝ)..2 * Real.pi, F t) = 0 :=
    (mul_eq_zero.mp havg).resolve_left hcoef
  have hint :
      IntervalIntegrable F volume 0 (2 * Real.pi) := by
    have hc :=
      circleIntegrable_log_norm_sub_const
        (a := (-(r : ℂ))) (c := 0) (r := 1)
    simpa only [CircleIntegrable, F] using hc
  have hpiMem : Real.pi ∈ Set.uIcc (0 : ℝ) (2 * Real.pi) := by
    rw [Set.uIcc_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
    constructor <;> nlinarith [Real.pi_pos]
  have hparts :
      IntervalIntegrable F volume 0 Real.pi ∧
        IntervalIntegrable F volume Real.pi (2 * Real.pi) :=
    (IntervalIntegrable.trans_iff hpiMem).mp hint
  have hsym : ∀ t : ℝ, F (2 * Real.pi - t) = F t := by
    intro t
    dsimp only [F]
    congr 1
    rw [Complex.norm_def, Complex.norm_def]
    congr 1
    simp only [circleMap, zero_add, Complex.exp_ofReal_mul_I]
    simp [Complex.normSq_apply, Real.cos_two_pi_sub,
      Real.sin_two_pi_sub]
  have hsecond :
      (∫ t in Real.pi..2 * Real.pi, F t) =
        ∫ t in (0 : ℝ)..Real.pi, F t := by
    calc
      (∫ t in Real.pi..2 * Real.pi, F t) =
          ∫ t in Real.pi..2 * Real.pi, F (2 * Real.pi - t) := by
        apply intervalIntegral.integral_congr
        intro t _
        exact (hsym t).symm
      _ = ∫ t in (0 : ℝ)..Real.pi, F t := by
        rw [intervalIntegral.integral_comp_sub_left]
        ring_nf
  have hsum :
      (∫ t in (0 : ℝ)..Real.pi, F t) +
          (∫ t in Real.pi..2 * Real.pi, F t) = 0 := by
    rw [intervalIntegral.integral_add_adjacent_intervals
      hparts.1 hparts.2, hfull]
  dsimp only [F] at hsecond hsum ⊢
  rw [hsecond] at hsum
  linarith

private theorem positive_integralValue (A B : ℝ)
    (hA : 0 < A) (hB : 0 < B) :
    integralValue A B = Real.pi * Real.log ((A + B) / 2) := by
  let s := A + B
  let r := (B - A) / s
  let F : ℝ → ℝ := fun t =>
    Real.log ‖circleMap 0 1 t - (-(r : ℂ))‖
  have hs : 0 < s := by dsimp only [s]; linarith
  have hr : |r| < 1 := by
    rw [abs_lt]
    dsimp only [r]
    constructor
    · apply (lt_div_iff₀ hs).2
      dsimp only [s]
      linarith
    · apply (div_lt_iff₀ hs).2
      dsimp only [s]
      linarith
  have hdecomp : ∀ x : ℝ,
      Real.log (A ^ 2 * Real.sin x ^ 2 + B ^ 2 * Real.cos x ^ 2) =
        2 * Real.log (s / 2) + 2 * F (2 * x) := by
    intro x
    let z : ℂ := circleMap 0 1 (2 * x) - (-(r : ℂ))
    have htrig := Real.sin_sq_add_cos_sq x
    have hellipse :
        0 < A ^ 2 * Real.sin x ^ 2 + B ^ 2 * Real.cos x ^ 2 := by
      have hmin : 0 < min (A ^ 2) (B ^ 2) :=
        lt_min (sq_pos_of_pos hA) (sq_pos_of_pos hB)
      calc
        0 < min (A ^ 2) (B ^ 2) *
            (Real.sin x ^ 2 + Real.cos x ^ 2) := by
          rw [htrig]
          simpa using hmin
        _ ≤ A ^ 2 * Real.sin x ^ 2 +
            B ^ 2 * Real.cos x ^ 2 := by
          calc
            min (A ^ 2) (B ^ 2) *
                (Real.sin x ^ 2 + Real.cos x ^ 2) =
                min (A ^ 2) (B ^ 2) * Real.sin x ^ 2 +
                  min (A ^ 2) (B ^ 2) * Real.cos x ^ 2 := by ring
            _ ≤ A ^ 2 * Real.sin x ^ 2 +
                B ^ 2 * Real.cos x ^ 2 :=
              add_le_add
                (mul_le_mul_of_nonneg_right
                  (min_le_left (A ^ 2) (B ^ 2))
                  (sq_nonneg (Real.sin x)))
                (mul_le_mul_of_nonneg_right
                  (min_le_right (A ^ 2) (B ^ 2))
                  (sq_nonneg (Real.cos x)))
    have hcircle :
        circleMap 0 1 (2 * x) =
          (Real.cos (2 * x) : ℂ) +
            (Real.sin (2 * x) : ℂ) * Complex.I := by
      simpa [circleMap] using Complex.exp_ofReal_mul_I (2 * x)
    have hzre : z.re = Real.cos (2 * x) + r := by
      dsimp only [z]
      rw [hcircle]
      simp only [Complex.sub_re, Complex.add_re, Complex.mul_re,
        Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im]
      ring
    have hzim : z.im = Real.sin (2 * x) := by
      dsimp only [z]
      rw [hcircle]
      simp only [Complex.sub_im, Complex.add_im, Complex.mul_im,
        Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im]
      ring
    have halg :
        A ^ 2 * Real.sin x ^ 2 + B ^ 2 * Real.cos x ^ 2 =
          (s / 2) ^ 2 * ‖z‖ ^ 2 := by
      dsimp only [r, s] at hzre hzim ⊢
      rw [Complex.sq_norm, Complex.normSq_apply, hzre, hzim]
      rw [Real.cos_two_mul', Real.sin_two_mul]
      field_simp [show A + B ≠ 0 by linarith]
      have hcosSq : Real.cos x ^ 2 = 1 - Real.sin x ^ 2 := by
        nlinarith only [htrig]
      rw [hcosSq]
      ring
    have hz : ‖z‖ ≠ 0 := by
      intro hz
      rw [hz] at halg
      norm_num at halg
      linarith
    rw [halg, Real.log_mul
      (pow_ne_zero 2 (by positivity : s / 2 ≠ 0))
      (pow_ne_zero 2 hz), Real.log_pow, Real.log_pow]
    dsimp only [F, z]
    ring
  have hhalf :
      IntervalIntegrable F volume 0 Real.pi := by
    have hcircle :=
      circleIntegrable_log_norm_sub_const
        (a := (-(r : ℂ))) (c := 0) (r := 1)
    have hfull :
        IntervalIntegrable F volume 0 (2 * Real.pi) := by
      simpa only [CircleIntegrable, F] using hcircle
    have hpiMem : Real.pi ∈ Set.uIcc (0 : ℝ) (2 * Real.pi) := by
      rw [Set.uIcc_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
      constructor <;> nlinarith [Real.pi_pos]
    exact ((IntervalIntegrable.trans_iff hpiMem).mp hfull).1
  have hscaled :
      IntervalIntegrable (fun x : ℝ => F (2 * x))
        volume 0 (Real.pi / 2) := by
    have h := hhalf.comp_mul_left (c := (2 : ℝ))
    simpa only [zero_div, mul_zero,
      div_self (by norm_num : (2 : ℝ) ≠ 0)] using h
  have hscaledZero :
      (∫ x in (0 : ℝ)..Real.pi / 2, F (2 * x)) = 0 := by
    rw [intervalIntegral.integral_comp_mul_left
      (f := F) (by norm_num : (2 : ℝ) ≠ 0)]
    rw [show (2 : ℝ) * 0 = 0 by ring,
      show (2 : ℝ) * (Real.pi / 2) = Real.pi by ring]
    have hz := half_circle_log_distance_zero r hr
    change (2 : ℝ)⁻¹ • (∫ x in (0 : ℝ)..Real.pi, F x) = 0
    rw [show (∫ x in (0 : ℝ)..Real.pi, F x) = 0 by
      simpa only [F] using hz]
    simp
  unfold integralValue
  calc
    (∫ x in (0 : ℝ)..Real.pi / 2,
        Real.log (A ^ 2 * Real.sin x ^ 2 + B ^ 2 * Real.cos x ^ 2)) =
        ∫ x in (0 : ℝ)..Real.pi / 2,
          (2 * Real.log (s / 2) + 2 * F (2 * x)) := by
      apply intervalIntegral.integral_congr
      intro x _
      exact hdecomp x
    _ = (∫ x in (0 : ℝ)..Real.pi / 2, 2 * Real.log (s / 2)) +
          ∫ x in (0 : ℝ)..Real.pi / 2, 2 * F (2 * x) := by
      rw [intervalIntegral.integral_add intervalIntegrable_const
        (hscaled.const_mul 2)]
    _ = Real.pi * Real.log (s / 2) +
          2 * (∫ x in (0 : ℝ)..Real.pi / 2, F (2 * x)) := by
      rw [intervalIntegral.integral_const,
        intervalIntegral.integral_const_mul]
      simp only [smul_eq_mul]
      ring
    _ = Real.pi * Real.log ((A + B) / 2) := by
      rw [hscaledZero]
      dsimp only [s]
      ring

private theorem positive_zero_integralValue (A : ℝ) (hA : 0 < A) :
    integralValue A 0 = Real.pi * Real.log (A / 2) := by
  have heq :
      (∫ x in (0 : ℝ)..Real.pi / 2,
          Real.log (A ^ 2 * Real.sin x ^ 2)) =
        ∫ x in (0 : ℝ)..Real.pi / 2,
          (2 * Real.log A + 2 * Real.log (Real.sin x)) := by
    apply intervalIntegral.integral_congr_codiscreteWithin
    apply Filter.codiscreteWithin.mono (by
      intro x _
      exact Set.mem_univ x)
    have hsin :
        Real.sin ⁻¹' ({0} : Set ℝ)ᶜ ∈ Filter.codiscrete ℝ := by
      apply Real.analyticOnNhd_sin.preimage_zero_mem_codiscrete
        (x := Real.pi / 2)
      simp
    filter_upwards [hsin] with x hx
    simp only [Set.preimage_compl, Set.mem_compl_iff, Set.mem_preimage,
      Set.mem_singleton_iff] at hx
    rw [Real.log_mul (pow_ne_zero 2 hA.ne') (pow_ne_zero 2 hx),
      Real.log_pow, Real.log_pow]
    ring
  unfold integralValue
  rw [show (0 : ℝ) ^ 2 = 0 by norm_num]
  simp only [zero_mul, add_zero]
  rw [heq, intervalIntegral.integral_add intervalIntegrable_const
    (by
      simpa only [Function.comp_apply] using
        (intervalIntegrable_log_sin
          (a := (0 : ℝ)) (b := Real.pi / 2)).const_mul 2),
    intervalIntegral.integral_const,
    intervalIntegral.integral_const_mul,
    integral_log_sin_zero_pi_div_two,
    Real.log_div hA.ne' (by norm_num : (2 : ℝ) ≠ 0)]
  simp only [smul_eq_mul]
  ring_nf

private theorem integralValue_swap (a b : ℝ) :
    integralValue a b = integralValue b a := by
  let f : ℝ → ℝ := fun x =>
    Real.log (a ^ 2 * Real.sin x ^ 2 + b ^ 2 * Real.cos x ^ 2)
  unfold integralValue
  change (∫ x in (0 : ℝ)..Real.pi / 2, f x) =
    ∫ x in (0 : ℝ)..Real.pi / 2,
      Real.log (b ^ 2 * Real.sin x ^ 2 + a ^ 2 * Real.cos x ^ 2)
  calc
    (∫ x in (0 : ℝ)..Real.pi / 2, f x) =
        ∫ x in (0 : ℝ)..Real.pi / 2, f (Real.pi / 2 - x) := by
      symm
      rw [intervalIntegral.integral_comp_sub_left]
      ring_nf
    _ = ∫ x in (0 : ℝ)..Real.pi / 2,
        Real.log (b ^ 2 * Real.sin x ^ 2 + a ^ 2 * Real.cos x ^ 2) := by
      apply intervalIntegral.integral_congr
      intro x _
      dsimp only [f]
      rw [Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]
      ring

private theorem absolute_integralValue (a b : ℝ)
    (hab : 0 < |a| + |b|) :
    integralValue a b = Real.pi * Real.log ((|a| + |b|) / 2) := by
  let A := |a|
  let B := |b|
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hsum : 0 < A + B := by simpa only [A, B] using hab
  have hreduce : integralValue a b = integralValue A B := by
    simp [integralValue, A, B]
  rw [hreduce]
  change integralValue A B = Real.pi * Real.log ((A + B) / 2)
  by_cases hA0 : A = 0
  · have hBp : 0 < B := by linarith
    rw [integralValue_swap, hA0]
    simpa only [zero_add] using positive_zero_integralValue B hBp
  · by_cases hB0 : B = 0
    · have hAp : 0 < A := lt_of_le_of_ne hA (Ne.symm hA0)
      rw [hB0]
      simpa only [add_zero] using positive_zero_integralValue A hAp
    · have hAp : 0 < A := lt_of_le_of_ne hA (Ne.symm hA0)
      have hBp : 0 < B := lt_of_le_of_ne hB (Ne.symm hB0)
      simpa only [A, B] using positive_integralValue A B hAp hBp

private def derivativeIntegrand (a b x : ℝ) : ℝ :=
  (2 * a * Real.sin x ^ 2) /
    (a ^ 2 * Real.sin x ^ 2 + b ^ 2 * Real.cos x ^ 2)

private lemma derivativeIntegrand_hasDerivAt
    (a b x : ℝ) (ha : 0 < a) (hb : 0 < b) :
    HasDerivAt
      (fun s =>
        Real.log (s ^ 2 * Real.sin x ^ 2 +
          b ^ 2 * Real.cos x ^ 2))
      (derivativeIntegrand a b x) a := by
  have hden :
      0 < a ^ 2 * Real.sin x ^ 2 + b ^ 2 * Real.cos x ^ 2 := by
    have htrig := Real.sin_sq_add_cos_sq x
    have hmin : 0 < min (a ^ 2) (b ^ 2) :=
      lt_min (sq_pos_of_pos ha) (sq_pos_of_pos hb)
    calc
      0 < min (a ^ 2) (b ^ 2) *
          (Real.sin x ^ 2 + Real.cos x ^ 2) := by
        rw [htrig]
        simpa using hmin
      _ ≤ a ^ 2 * Real.sin x ^ 2 +
          b ^ 2 * Real.cos x ^ 2 := by
        calc
          min (a ^ 2) (b ^ 2) *
              (Real.sin x ^ 2 + Real.cos x ^ 2) =
              min (a ^ 2) (b ^ 2) * Real.sin x ^ 2 +
                min (a ^ 2) (b ^ 2) * Real.cos x ^ 2 := by ring
          _ ≤ a ^ 2 * Real.sin x ^ 2 +
              b ^ 2 * Real.cos x ^ 2 :=
            add_le_add
              (mul_le_mul_of_nonneg_right (min_le_left _ _)
                (sq_nonneg _))
              (mul_le_mul_of_nonneg_right (min_le_right _ _)
                (sq_nonneg _))
  have hinner :
      HasDerivAt
        (fun s => s ^ 2 * Real.sin x ^ 2 +
          b ^ 2 * Real.cos x ^ 2)
        (2 * a * Real.sin x ^ 2) a := by
    convert
      (((hasDerivAt_id a).pow 2).mul_const (Real.sin x ^ 2)).add_const
        (b ^ 2 * Real.cos x ^ 2) using 1 <;>
          simp only [id_eq] <;> ring
  unfold derivativeIntegrand
  convert (Real.hasDerivAt_log hden.ne').comp a hinner using 1 <;> ring

private lemma integralValue_hasDerivAt (a b : ℝ)
    (ha : 0 < a) (hb : 0 < b) :
    HasDerivAt (fun s => integralValue s b)
      (∫ x in (0 : ℝ)..Real.pi / 2,
        derivativeIntegrand a b x) a := by
  let S : Set ℝ := Set.Icc (a / 2) (3 * a / 2)
  let T : Set ℝ := Set.Icc (0 : ℝ) (Real.pi / 2)
  let K : Set (ℝ × ℝ) := S ×ˢ T
  have hS : S ∈ 𝓝 a := by
    dsimp [S]
    apply Icc_mem_nhds <;> linarith
  have hpos (p : ℝ × ℝ) (hp : p ∈ K) :
      0 < p.1 ^ 2 * Real.sin p.2 ^ 2 +
        b ^ 2 * Real.cos p.2 ^ 2 := by
    have hs : 0 < p.1 := by
      have hs' : a / 2 ≤ p.1 := hp.1.1
      linarith
    have htrig := Real.sin_sq_add_cos_sq p.2
    have hm : 0 < min (p.1 ^ 2) (b ^ 2) :=
      lt_min (sq_pos_of_pos hs) (sq_pos_of_pos hb)
    calc
      0 < min (p.1 ^ 2) (b ^ 2) *
          (Real.sin p.2 ^ 2 + Real.cos p.2 ^ 2) := by
        rw [htrig]
        simpa using hm
      _ ≤ p.1 ^ 2 * Real.sin p.2 ^ 2 +
          b ^ 2 * Real.cos p.2 ^ 2 := by
        calc
          min (p.1 ^ 2) (b ^ 2) *
              (Real.sin p.2 ^ 2 + Real.cos p.2 ^ 2) =
              min (p.1 ^ 2) (b ^ 2) * Real.sin p.2 ^ 2 +
                min (p.1 ^ 2) (b ^ 2) * Real.cos p.2 ^ 2 := by ring
          _ ≤ p.1 ^ 2 * Real.sin p.2 ^ 2 +
              b ^ 2 * Real.cos p.2 ^ 2 :=
            add_le_add
              (mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg _))
              (mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg _))
  have hFcont :
      ContinuousOn
        (fun p : ℝ × ℝ =>
          Real.log (p.1 ^ 2 * Real.sin p.2 ^ 2 +
            b ^ 2 * Real.cos p.2 ^ 2)) K := by
    apply ContinuousOn.log
    · fun_prop
    · intro p hp
      exact (hpos p hp).ne'
  have hF'cont :
      ContinuousOn
        (fun p : ℝ × ℝ => derivativeIntegrand p.1 b p.2) K := by
    unfold derivativeIntegrand
    apply ContinuousOn.div
    · fun_prop
    · fun_prop
    · intro p hp
      exact (hpos p hp).ne'
  obtain ⟨C, hC⟩ :=
    (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
      hF'cont
  have hsection
      (H : ℝ × ℝ → ℝ) (hH : ContinuousOn H K)
      (s : ℝ) (hs : s ∈ S) :
      ContinuousOn (fun x => H (s, x)) T := by
    apply hH.comp (continuous_const.prodMk continuous_id).continuousOn
    intro x hx
    exact ⟨hs, hx⟩
  have hF_meas :
      ∀ᶠ s in 𝓝 a,
        AEStronglyMeasurable
          (fun x =>
            Real.log (s ^ 2 * Real.sin x ^ 2 +
              b ^ 2 * Real.cos x ^ 2))
          (volume.restrict (Set.uIoc 0 (Real.pi / 2))) := by
    filter_upwards [hS] with s hs
    have hc := hsection _ hFcont s hs
    have hi :
        IntervalIntegrable
          (fun x =>
            Real.log (s ^ 2 * Real.sin x ^ 2 +
              b ^ 2 * Real.cos x ^ 2))
          volume 0 (Real.pi / 2) := by
      apply ContinuousOn.intervalIntegrable
      simpa only [T, Set.uIcc_of_le (half_pos Real.pi_pos).le] using hc
    simpa [Set.uIoc_of_le (half_pos Real.pi_pos).le] using
      hi.aestronglyMeasurable
  have haS : a ∈ S := by
    dsimp [S]
    constructor <;> linarith
  have hF_int :
      IntervalIntegrable
        (fun x =>
          Real.log (a ^ 2 * Real.sin x ^ 2 +
            b ^ 2 * Real.cos x ^ 2))
        volume 0 (Real.pi / 2) := by
    apply ContinuousOn.intervalIntegrable
    simpa only [T, Set.uIcc_of_le (half_pos Real.pi_pos).le] using
      hsection _ hFcont a haS
  have hF'_int :
      IntervalIntegrable (derivativeIntegrand a b)
        volume 0 (Real.pi / 2) := by
    apply ContinuousOn.intervalIntegrable
    simpa only [T, Set.uIcc_of_le (half_pos Real.pi_pos).le] using
      hsection _ hF'cont a haS
  have hF'_meas :
      AEStronglyMeasurable (derivativeIntegrand a b)
        (volume.restrict (Set.uIoc 0 (Real.pi / 2))) := by
    simpa [Set.uIoc_of_le (half_pos Real.pi_pos).le] using
      hF'_int.aestronglyMeasurable
  have hbound :
      ∀ᵐ x ∂volume, x ∈ Set.uIoc (0 : ℝ) (Real.pi / 2) →
        ∀ s ∈ S, ‖derivativeIntegrand s b x‖ ≤ C := by
    filter_upwards [] with x hx s hs
    rw [Set.uIoc_of_le (half_pos Real.pi_pos).le] at hx
    exact hC (s, x) ⟨hs, ⟨hx.1.le, hx.2⟩⟩
  have hdiff :
      ∀ᵐ x ∂volume, x ∈ Set.uIoc (0 : ℝ) (Real.pi / 2) →
        ∀ s ∈ S,
          HasDerivAt
            (fun q =>
              Real.log (q ^ 2 * Real.sin x ^ 2 +
                b ^ 2 * Real.cos x ^ 2))
            (derivativeIntegrand s b x) s := by
    filter_upwards [] with x hx s hs
    have hspos : 0 < s := by
      have hleft : a / 2 ≤ s := hs.1
      linarith
    exact derivativeIntegrand_hasDerivAt s b x hspos hb
  unfold integralValue
  exact
    (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := fun s x =>
        Real.log (s ^ 2 * Real.sin x ^ 2 +
          b ^ 2 * Real.cos x ^ 2))
      (F' := fun s x => derivativeIntegrand s b x)
      (bound := fun _ => C) (s := S)
      hS hF_meas hF_int hF'_meas
      hbound (continuous_const.intervalIntegrable _ _) hdiff).2

private lemma partialA_value (a b : ℝ)
    (ha : 0 < a) (hb : 0 < b) :
    partialA a b = Real.pi / (a + b) := by
  have heq :
      (fun s => integralValue s b) =ᶠ[𝓝 a]
        fun s => Real.pi * Real.log ((s + b) / 2) := by
    filter_upwards [Ioi_mem_nhds ha] with s hs
    exact positive_integralValue s b hs hb
  have harg : a + b ≠ 0 := by linarith
  have hinner :
      HasDerivAt (fun s : ℝ => (s + b) / 2) (1 / 2) a := by
    convert ((hasDerivAt_id a).add_const b).div_const 2 using 1 <;> ring
  have hlog :=
    (Real.hasDerivAt_log (by positivity : (a + b) / 2 ≠ 0)).comp a hinner
  have hderiv :
      HasDerivAt (fun s => Real.pi * Real.log ((s + b) / 2))
        (Real.pi / (a + b)) a := by
    convert hlog.const_mul Real.pi using 1
    field_simp [harg]
  unfold partialA
  rw [heq.deriv_eq]
  exact hderiv.deriv

private def tangentKernel (a b t : ℝ) : ℝ :=
  t ^ 2 / ((t ^ 2 + 1) * (t ^ 2 + b ^ 2 / a ^ 2))

private lemma tangentKernel_integrable (a b : ℝ)
    (ha : 0 < a) (hb : 0 < b) :
    IntegrableOn (tangentKernel a b) (Set.Ioi (0 : ℝ)) := by
  have hc : 0 < b ^ 2 / a ^ 2 :=
    div_pos (sq_pos_of_pos hb) (sq_pos_of_pos ha)
  have hmeas : AEStronglyMeasurable (tangentKernel a b)
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
    apply Continuous.aestronglyMeasurable
    unfold tangentKernel
    apply Continuous.div
    · fun_prop
    · fun_prop
    · intro t
      positivity
  apply integrable_inv_one_add_sq.integrableOn.mono' hmeas
  filter_upwards [] with t
  have h₁ : 0 < t ^ 2 + 1 := by positivity
  have h₂ : 0 < t ^ 2 + b ^ 2 / a ^ 2 := by positivity
  have hq0 : 0 ≤ tangentKernel a b t := by
    unfold tangentKernel
    positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hq0]
  change tangentKernel a b t ≤ (1 + t ^ 2)⁻¹
  calc
    tangentKernel a b t =
        (t ^ 2 / (t ^ 2 + b ^ 2 / a ^ 2)) *
          (1 / (1 + t ^ 2)) := by
      unfold tangentKernel
      field_simp [h₁.ne', h₂.ne']
      <;> ring
    _ ≤ 1 * (1 / (1 + t ^ 2)) := by
      apply mul_le_mul_of_nonneg_right
      · exact (div_le_one h₂).2 (by linarith)
      · positivity
    _ = (1 + t ^ 2)⁻¹ := by rw [one_mul, inv_eq_one_div]

private lemma arctan_transformed (a b t : ℝ)
    (ha : 0 < a) (hb : 0 < b) :
    derivativeIntegrand a b (Real.arctan t) *
        (1 / (1 + t ^ 2)) =
      (2 / a) * tangentKernel a b t := by
  have hq : 0 < Real.sqrt (1 + t ^ 2) := by positivity
  unfold derivativeIntegrand tangentKernel
  rw [Real.sin_arctan, Real.cos_arctan]
  field_simp [ha.ne', hq.ne']
  ring

private lemma derivativeIntegral_eq_tangent (a b : ℝ)
    (ha : 0 < a) (hb : 0 < b) :
    (∫ x in (0 : ℝ)..Real.pi / 2, derivativeIntegrand a b x) =
      (2 / a) * tangentIntegral a b := by
  let g : ℝ → ℝ := derivativeIntegrand a b
  let h : ℝ → ℝ := fun t =>
    (2 / a) * tangentKernel a b t
  have hg : Continuous g := by
    unfold g derivativeIntegrand
    apply Continuous.div
    · fun_prop
    · fun_prop
    · intro x
      have htrig := Real.sin_sq_add_cos_sq x
      have hm : 0 < min (a ^ 2) (b ^ 2) :=
        lt_min (sq_pos_of_pos ha) (sq_pos_of_pos hb)
      have hp :
          0 < min (a ^ 2) (b ^ 2) *
            (Real.sin x ^ 2 + Real.cos x ^ 2) := by
        rw [htrig]
        simpa using hm
      have hle :
          min (a ^ 2) (b ^ 2) *
              (Real.sin x ^ 2 + Real.cos x ^ 2) ≤
            a ^ 2 * Real.sin x ^ 2 +
              b ^ 2 * Real.cos x ^ 2 := by
        calc
          min (a ^ 2) (b ^ 2) *
              (Real.sin x ^ 2 + Real.cos x ^ 2) =
              min (a ^ 2) (b ^ 2) * Real.sin x ^ 2 +
                min (a ^ 2) (b ^ 2) * Real.cos x ^ 2 := by ring
          _ ≤ _ :=
            add_le_add
              (mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg _))
              (mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg _))
      exact (lt_of_lt_of_le hp hle).ne'
  have hhint : IntegrableOn h (Set.Ioi (0 : ℝ)) := by
    have hi := (tangentKernel_integrable a b ha hb).const_mul (2 / a)
    simpa only [h] using hi
  have hfinite (R : ℝ) :
      (∫ t in (0 : ℝ)..R, h t) =
        ∫ x in (0 : ℝ)..Real.arctan R, g x := by
    have hsub :=
      intervalIntegral.integral_comp_mul_deriv
        (a := (0 : ℝ)) (b := R)
        (f := Real.arctan)
        (f' := fun t : ℝ => 1 / (1 + t ^ 2))
        (g := g)
        (fun t ht => by
          simpa [one_div] using Real.hasDerivAt_arctan t)
        (by
          apply Continuous.continuousOn
          apply Continuous.div
          · fun_prop
          · fun_prop
          · intro t
            positivity)
        hg
    rw [Real.arctan_zero] at hsub
    calc
      (∫ t in (0 : ℝ)..R, h t) =
          ∫ t in (0 : ℝ)..R,
            (g ∘ Real.arctan) t * (1 / (1 + t ^ 2)) := by
        apply intervalIntegral.integral_congr
        intro t ht
        dsimp [g, h, Function.comp_def]
        exact (arctan_transformed a b t ha hb).symm
      _ = ∫ x in (0 : ℝ)..Real.arctan R, g x := hsub
  have hleft :
      Tendsto (fun R => ∫ t in (0 : ℝ)..R, h t) atTop
        (𝓝 (∫ t in Set.Ioi (0 : ℝ), h t)) :=
    intervalIntegral_tendsto_integral_Ioi 0 hhint tendsto_id
  have hprimitive :
      Continuous (fun u => ∫ x in (0 : ℝ)..u, g x) := by
    rw [continuous_iff_continuousAt]
    intro u
    exact (hg.integral_hasStrictDerivAt 0 u).hasDerivAt.continuousAt
  have hright :
      Tendsto (fun R => ∫ x in (0 : ℝ)..Real.arctan R, g x)
        atTop (𝓝 (∫ x in (0 : ℝ)..Real.pi / 2, g x)) :=
    hprimitive.continuousAt.tendsto.comp
      (Real.tendsto_arctan_atTop.mono_right inf_le_left)
  have hevent :
      (fun R => ∫ t in (0 : ℝ)..R, h t) =ᶠ[atTop]
        fun R => ∫ x in (0 : ℝ)..Real.arctan R, g x :=
    Filter.Eventually.of_forall hfinite
  have hlim :
      (∫ t in Set.Ioi (0 : ℝ), h t) =
        ∫ x in (0 : ℝ)..Real.pi / 2, g x :=
    tendsto_nhds_unique hleft (hright.congr' hevent.symm)
  unfold tangentIntegral
  have hpull :
      (∫ t in Set.Ioi (0 : ℝ), h t) =
        (2 / a) * ∫ t in Set.Ioi (0 : ℝ), tangentKernel a b t := by
    unfold h
    exact integral_const_mul _ _
  rw [hpull] at hlim
  simpa only [g, tangentKernel] using hlim.symm

theorem gap1 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    partialA a b =
      ∫ x in (0 : ℝ)..Real.pi / 2,
        (2 * a * Real.sin x ^ 2) /
          (a ^ 2 * Real.sin x ^ 2 + b ^ 2 * Real.cos x ^ 2) := by
  unfold partialA
  rw [(integralValue_hasDerivAt a b ha hb).deriv]
  rfl

theorem gap2 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a = b) :
    partialA b b =
      (2 / b) * ∫ x in (0 : ℝ)..Real.pi / 2, Real.sin x ^ 2 := by
  rw [gap1 b b hb hb]
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro x hx
  have htrig := Real.sin_sq_add_cos_sq x
  field_simp [hb.ne']
  nlinarith

theorem gap3 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a = b) :
    (2 / b) * (∫ x in (0 : ℝ)..Real.pi / 2, Real.sin x ^ 2) =
      Real.pi / (2 * b) := by
  rw [integral_sin_sq]
  simp
  field_simp [hb.ne', Real.pi_ne_zero]

theorem gap4 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a = b) :
    partialA b b = Real.pi / (2 * b) := by
  rw [gap2 a b ha hb hab, gap3 a b ha hb hab]

theorem gap5 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) :
    partialA a b = (2 / a) * tangentIntegral a b := by
  rw [gap1 a b ha hb]
  exact derivativeIntegral_eq_tangent a b ha hb

theorem gap6 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) :
    (2 / a) * tangentIntegral a b = Real.pi / (a + b) := by
  rw [← gap5 a b ha hb hab]
  exact partialA_value a b ha hb

theorem gap7 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) :
    partialA a b = Real.pi / (a + b) := by
  rw [gap5 a b ha hb hab, gap6 a b ha hb hab]

theorem gap8 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    partialA a b = Real.pi / (a + b) :=
  partialA_value a b ha hb

theorem gap9 (b : ℝ) (hb : 0 < b) :
    ∀ a : ℝ, 0 < a →
      integralValue a b =
        Real.pi * Real.log (a + b) + integrationConstant b := by
  intro a ha
  unfold integrationConstant
  rw [positive_integralValue a b ha hb,
    positive_integralValue b b hb hb]
  have hab : a + b ≠ 0 := by linarith
  have h2 : (2 : ℝ) ≠ 0 := by norm_num
  rw [Real.log_div hab h2, Real.log_mul h2 hb.ne']
  norm_num
  ring

theorem gap10 (b : ℝ) (hb : 0 < b) :
    integralValue b b =
      Real.pi * Real.log (2 * b) + integrationConstant b := by
  unfold integrationConstant
  ring

theorem gap11 (b : ℝ) (hb : 0 < b) :
    integralValue b b =
      ∫ x in (0 : ℝ)..Real.pi / 2, Real.log (b ^ 2) := by
  unfold integralValue
  apply intervalIntegral.integral_congr
  intro x hx
  change Real.log
      (b ^ 2 * Real.sin x ^ 2 + b ^ 2 * Real.cos x ^ 2) =
    Real.log (b ^ 2)
  apply congrArg Real.log
  have htrig := Real.sin_sq_add_cos_sq x
  rw [← mul_add, htrig, mul_one]

theorem gap12 (b : ℝ) (hb : 0 < b) :
    (∫ x in (0 : ℝ)..Real.pi / 2, Real.log (b ^ 2)) =
      Real.pi * Real.log b := by
  rw [intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  rw [Real.log_pow]
  ring

theorem gap13 (b : ℝ) (hb : 0 < b) :
    integralValue b b = Real.pi * Real.log b := by
  rw [gap11 b hb, gap12 b hb]

theorem gap14 (b : ℝ) (hb : 0 < b) :
    integrationConstant b = Real.pi * Real.log (1 / 2 : ℝ) := by
  unfold integrationConstant
  rw [gap13 b hb, Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hb.ne',
    Real.log_div (by norm_num : (1 : ℝ) ≠ 0)
      (by norm_num : (2 : ℝ) ≠ 0)]
  norm_num
  ring

theorem gap15 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    integralValue a b =
      Real.pi * Real.log (a + b) + Real.pi * Real.log (1 / 2 : ℝ) := by
  rw [positive_integralValue a b ha hb]
  have hab : a + b ≠ 0 := by linarith
  rw [Real.log_div hab (by norm_num : (2 : ℝ) ≠ 0),
    Real.log_div (by norm_num : (1 : ℝ) ≠ 0)
      (by norm_num : (2 : ℝ) ≠ 0)]
  norm_num
  ring

theorem gap16 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Real.pi * Real.log (a + b) + Real.pi * Real.log (1 / 2 : ℝ) =
      Real.pi * Real.log ((a + b) / 2) := by
  have hab : a + b ≠ 0 := by linarith
  rw [Real.log_div hab (by norm_num : (2 : ℝ) ≠ 0),
    Real.log_div (by norm_num : (1 : ℝ) ≠ 0)
      (by norm_num : (2 : ℝ) ≠ 0)]
  norm_num
  ring

theorem gap17 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    integralValue a b = Real.pi * Real.log ((a + b) / 2) :=
  positive_integralValue a b ha hb

theorem gap18 (a b : ℝ) (hneg : a < 0 ∨ b < 0) :
    integralValue a b =
      ∫ x in (0 : ℝ)..Real.pi / 2,
        Real.log (|a| ^ 2 * Real.sin x ^ 2 + |b| ^ 2 * Real.cos x ^ 2) := by
  unfold integralValue
  apply intervalIntegral.integral_congr
  intro x hx
  rw [sq_abs, sq_abs]

theorem gap19 (a b : ℝ) (hneg : a < 0 ∨ b < 0) :
    (∫ x in (0 : ℝ)..Real.pi / 2,
        Real.log (|a| ^ 2 * Real.sin x ^ 2 + |b| ^ 2 * Real.cos x ^ 2)) =
      Real.pi * Real.log ((|a| + |b|) / 2) := by
  have hsum : 0 < |a| + |b| := by
    rcases hneg with ha | hb
    · have : 0 < |a| := abs_pos.mpr (ne_of_lt ha)
      positivity
    · have : 0 < |b| := abs_pos.mpr (ne_of_lt hb)
      positivity
  have h := absolute_integralValue a b hsum
  rw [gap18 a b hneg] at h
  exact h

theorem gap20 (a b : ℝ) (hneg : a < 0 ∨ b < 0) :
    integralValue a b = Real.pi * Real.log ((|a| + |b|) / 2) := by
  rw [gap18 a b hneg, gap19 a b hneg]

theorem gap21 (a b : ℝ) (hnz : a ≠ 0 ∨ b ≠ 0) :
    integralValue a b = Real.pi * Real.log ((|a| + |b|) / 2) := by
  have hsum : 0 < |a| + |b| := by
    rcases hnz with ha | hb
    · have : 0 < |a| := abs_pos.mpr ha
      positivity
    · have : 0 < |b| := abs_pos.mpr hb
      positivity
  exact absolute_integralValue a b hsum

end

end ProofGap.Exercise3732
