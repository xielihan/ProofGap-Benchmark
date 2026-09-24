import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4034

noncomputable section

open MeasureTheory
open scoped Interval

def nthRoot (n : ℕ) (x : ℝ) : ℝ :=
  Real.rpow x (1 / (n : ℝ))

def betaFn (x y : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1,
    Real.rpow (1 - t) (x - 1) * Real.rpow t (y - 1)

def baseRegion (a b : ℝ) (n : ℕ) : Set (ℝ × ℝ) :=
  {p |
    0 ≤ p.1 ∧ 0 ≤ p.2 ∧
      p.1 ^ n / a ^ n + p.2 ^ n / b ^ n ≤ 1}

def height (a b c : ℝ) (n : ℕ) (x y : ℝ) : ℝ :=
  c * nthRoot n (1 - (x ^ n / a ^ n + y ^ n / b ^ n))

def paramX (a : ℝ) (n : ℕ) (r φ : ℝ) : ℝ :=
  a * r * Real.rpow (Real.cos φ) (2 / (n : ℝ))

def paramY (b : ℝ) (n : ℕ) (r φ : ℝ) : ℝ :=
  b * r * Real.rpow (Real.sin φ) (2 / (n : ℝ))

def radialHeight (c : ℝ) (n : ℕ) (r : ℝ) : ℝ :=
  c * nthRoot n (1 - r ^ n)

def parameterDomain : Set (ℝ × ℝ) :=
  Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) (Real.pi / 2)

def volume (a b c : ℝ) (n : ℕ) : ℝ :=
  ∫ p in baseRegion a b n, height a b c n p.1 p.2

theorem gap1 (a b c : ℝ) (n : ℕ) (hn : 0 < n)
    (ha : 0 < a) (hb : 0 < b) :
    ∀ x y : ℝ,
      height a b c n x y =
        c * nthRoot n (1 - (x ^ n / a ^ n + y ^ n / b ^ n)) := by
  intro x y
  rfl

theorem gap2 (c : ℝ) (n : ℕ) (hn : 0 < n) (r : ℝ) :
    radialHeight c n r = c * nthRoot n (1 - r ^ n) := by
  rfl

theorem gap3 (r φ : ℝ) (hp : (r, φ) ∈ parameterDomain) :
    0 ≤ φ := by
  exact hp.2.1

theorem gap4 (r φ : ℝ) (hp : (r, φ) ∈ parameterDomain) :
    φ ≤ Real.pi / 2 := by
  exact hp.2.2

theorem gap5 (r φ : ℝ) (hp : (r, φ) ∈ parameterDomain) :
    0 ≤ r := by
  exact hp.1.1

theorem gap6 (r φ : ℝ) (hp : (r, φ) ∈ parameterDomain) :
    r ≤ 1 := by
  exact hp.1.2

private theorem ae_real_ne (u : ℝ) :
    ∀ᵐ x : ℝ ∂(MeasureTheory.volume : Measure ℝ), x ≠ u := by
  rw [ae_iff]
  simpa using measure_singleton u

private theorem rpow_pow_mul_pow_deriv
    (n : ℕ) (hn : 0 < n) (r : ℝ) (hr : 0 < r) :
    Real.rpow (r ^ n) (2 / (n : ℝ) - 1) *
        ((n : ℝ) * r ^ (n - 1)) =
      (n : ℝ) * r := by
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hone : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn.ne'
  have hpow :
      Real.rpow (r ^ n) (2 / (n : ℝ) - 1) =
        Real.rpow r
          ((n : ℝ) * (2 / (n : ℝ) - 1)) := by
    calc
      Real.rpow (r ^ n) (2 / (n : ℝ) - 1) =
          Real.rpow (Real.rpow r (n : ℝ))
            (2 / (n : ℝ) - 1) := by
        congr 1
        exact (Real.rpow_natCast r n).symm
      _ = Real.rpow r
            ((n : ℝ) * (2 / (n : ℝ) - 1)) :=
        (Real.rpow_mul hr.le (n : ℝ)
          (2 / (n : ℝ) - 1)).symm
  have hexp :
      (n : ℝ) * (2 / (n : ℝ) - 1) +
          ((n - 1 : ℕ) : ℝ) = 1 := by
    rw [Nat.cast_sub hone]
    field_simp
    ring
  rw [hpow, ← Real.rpow_natCast]
  calc
    Real.rpow r ((n : ℝ) * (2 / (n : ℝ) - 1)) *
          ((n : ℝ) * Real.rpow r ((n - 1 : ℕ) : ℝ)) =
        (n : ℝ) *
          (Real.rpow r ((n : ℝ) * (2 / (n : ℝ) - 1)) *
            Real.rpow r ((n - 1 : ℕ) : ℝ)) := by ring
    _ = (n : ℝ) *
          Real.rpow r
            ((n : ℝ) * (2 / (n : ℝ) - 1) +
              ((n - 1 : ℕ) : ℝ)) := by
      exact congrArg (fun z : ℝ => (n : ℝ) * z)
        (Real.rpow_add hr
          ((n : ℝ) * (2 / (n : ℝ) - 1))
          ((n - 1 : ℕ) : ℝ)).symm
    _ = (n : ℝ) * r := by
      rw [hexp]
      exact congrArg (fun z : ℝ => (n : ℝ) * z)
        (Real.rpow_one r)

private theorem beta_intervalIntegrable (m q : ℝ)
    (hm : -1 < m) (hq : -1 < q) :
    IntervalIntegrable
      (fun t : ℝ =>
        Real.rpow t m * Real.rpow (1 - t) q)
      MeasureTheory.volume 0 1 := by
  have hmLeft :
      IntervalIntegrable (fun t : ℝ => Real.rpow t m)
        MeasureTheory.volume 0 (1 / 2 : ℝ) :=
    intervalIntegral.intervalIntegrable_rpow' hm
  have hqContLeft :
      ContinuousOn (fun t : ℝ => Real.rpow (1 - t) q)
        [[(0 : ℝ), 1 / 2]] := by
    apply continuousOn_of_forall_continuousAt
    intro t ht
    norm_num [Set.uIcc] at ht
    have hbase : 1 - t ≠ 0 := by linarith
    simpa [Function.comp_def] using
      (Real.continuousAt_rpow_const
        (1 - t) q (Or.inl hbase)).comp
        (continuous_const.sub continuous_id).continuousAt
  have hleft :
      IntervalIntegrable
        (fun t : ℝ =>
          Real.rpow t m * Real.rpow (1 - t) q)
        MeasureTheory.volume 0 (1 / 2 : ℝ) :=
    hmLeft.mul_continuousOn hqContLeft
  have hqRight :
      IntervalIntegrable
        (fun t : ℝ => Real.rpow (1 - t) q)
        MeasureTheory.volume (1 / 2 : ℝ) 1 := by
    have h :=
      (intervalIntegral.intervalIntegrable_rpow'
        (a := (0 : ℝ)) (b := 1 / 2) hq).comp_sub_left 1
    convert h.symm using 1 <;> norm_num
  have hmContRight :
      ContinuousOn (fun t : ℝ => Real.rpow t m)
        [[(1 / 2 : ℝ), 1]] := by
    apply continuousOn_of_forall_continuousAt
    intro t ht
    norm_num [Set.uIcc] at ht
    exact Real.continuousAt_rpow_const t m
      (Or.inl (by linarith))
  have hright :
      IntervalIntegrable
        (fun t : ℝ =>
          Real.rpow t m * Real.rpow (1 - t) q)
        MeasureTheory.volume (1 / 2 : ℝ) 1 :=
    hqRight.continuousOn_mul hmContRight
  exact hleft.trans hright

theorem gap8 (n : ℕ) (hn : 0 < n) :
    (∫ r in (0 : ℝ)..1, nthRoot n (1 - r ^ n) * r) =
      1 / (n : ℝ) *
        ∫ t in (0 : ℝ)..1,
          Real.rpow (1 - t) (1 / (n : ℝ)) *
            Real.rpow t (2 / (n : ℝ) - 1) := by
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  let f : ℝ → ℝ := fun r => r ^ n
  let f' : ℝ → ℝ :=
    fun r => (n : ℝ) * r ^ (n - 1)
  let g : ℝ → ℝ :=
    fun t =>
      Real.rpow (1 - t) (1 / (n : ℝ)) *
        Real.rpow t (2 / (n : ℝ) - 1)
  have hf : ContinuousOn f [[(0 : ℝ), 1]] := by
    exact (continuous_id.pow n).continuousOn
  have hder :
      ∀ r ∈ Set.Ioo (min (0 : ℝ) 1) (max (0 : ℝ) 1),
        HasDerivWithinAt f (f' r) (Set.Ioi r) r := by
    intro r hr
    apply HasDerivAt.hasDerivWithinAt
    dsimp [f, f']
    convert (hasDerivAt_id r).pow n using 1 <;>
      simp <;> ring
  have hf' : ContinuousOn f' [[(0 : ℝ), 1]] := by
    exact
      (continuous_const.mul
        (continuous_id.pow (n - 1))).continuousOn
  have hg :
      ContinuousOn g
        (f '' Set.Ioo (min (0 : ℝ) 1) (max (0 : ℝ) 1)) := by
    apply continuousOn_of_forall_continuousAt
    intro t ht
    rcases ht with ⟨r, hr, rfl⟩
    norm_num only [min_eq_left zero_le_one,
      max_eq_right zero_le_one, Set.mem_Ioo] at hr
    have hrpow_pos : 0 < r ^ n := pow_pos hr.1 n
    have hrpow_lt : r ^ n < 1 := by
      simpa using pow_lt_one₀ hr.1.le hr.2 hn.ne'
    have hleft :
        ContinuousAt
          (fun t : ℝ =>
            Real.rpow (1 - t) (1 / (n : ℝ)))
          (r ^ n) := by
      simpa [Function.comp_def] using
        (Real.continuousAt_rpow_const
          (1 - r ^ n) (1 / (n : ℝ))
          (Or.inl (sub_ne_zero.mpr hrpow_lt.ne'))).comp
          (continuous_const.sub continuous_id).continuousAt
    have hright :
        ContinuousAt
          (fun t : ℝ =>
            Real.rpow t (2 / (n : ℝ) - 1))
          (r ^ n) :=
      Real.continuousAt_rpow_const
        (r ^ n) (2 / (n : ℝ) - 1)
        (Or.inl hrpow_pos.ne')
    exact hleft.mul hright
  have hg1 :
      IntegrableOn g (f '' [[(0 : ℝ), 1]]) := by
    have hbeta :
        IntervalIntegrable g MeasureTheory.volume 0 1 := by
      have h :=
        beta_intervalIntegrable
          (2 / (n : ℝ) - 1) (1 / (n : ℝ))
          (by linarith [show 0 < 2 / (n : ℝ) by positivity])
          (by linarith [show 0 < 1 / (n : ℝ) by positivity])
      refine h.congr ?_
      intro t ht
      dsimp [g]
      ring
    have hIcc : IntegrableOn g (Set.Icc (0 : ℝ) 1) :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le
        zero_le_one).mp hbeta
    exact hIcc.mono_set (by
      rintro t ⟨r, hr, rfl⟩
      rw [Set.uIcc_of_le zero_le_one] at hr
      exact ⟨pow_nonneg hr.1 n,
        (pow_le_one₀ hr.1 hr.2)⟩)
  have hg2 :
      IntegrableOn (fun r => (g ∘ f) r * f' r)
        [[(0 : ℝ), 1]] := by
    let k : ℝ → ℝ :=
      fun r =>
        (n : ℝ) *
          (Real.rpow (1 - r ^ n) (1 / (n : ℝ)) * r)
    have hkcont : Continuous k := by
      dsimp [k]
      exact continuous_const.mul
        ((Real.continuous_rpow_const (by positivity)).comp
          (continuous_const.sub (continuous_id.pow n)) |>.mul
            continuous_id)
    have hkint :
        IntervalIntegrable k MeasureTheory.volume 0 1 :=
      hkcont.intervalIntegrable 0 1
    have hcomp :
        IntervalIntegrable
          (fun r => (g ∘ f) r * f' r)
          MeasureTheory.volume 0 1 := by
      apply hkint.congr_ae
      filter_upwards
        [ae_restrict_mem measurableSet_uIoc]
        with r hrmem
      rw [Set.uIoc_of_le zero_le_one] at hrmem
      have hpowder :=
        rpow_pow_mul_pow_deriv n hn r hrmem.1
      dsimp [k, g, f, f']
      calc
        (n : ℝ) *
            (Real.rpow (1 - r ^ n) (1 / (n : ℝ)) * r) =
          Real.rpow (1 - r ^ n) (1 / (n : ℝ)) *
            ((n : ℝ) * r) := by ring
        _ = Real.rpow (1 - r ^ n) (1 / (n : ℝ)) *
            (Real.rpow (r ^ n) (2 / (n : ℝ) - 1) *
              ((n : ℝ) * r ^ (n - 1))) := by
          exact congrArg
            (fun z : ℝ =>
              Real.rpow (1 - r ^ n) (1 / (n : ℝ)) * z)
            hpowder.symm
        _ = _ := by
          simp only [Real.rpow_eq_pow]
          ring
    simpa [Set.uIcc_of_le zero_le_one] using
      (intervalIntegrable_iff_integrableOn_Icc_of_le
        zero_le_one).mp hcomp
  have hsub :=
    intervalIntegral.integral_comp_mul_deriv'''
      (a := (0 : ℝ)) (b := 1)
      (f := f) (f' := f') (g := g)
      hf hder hg hg1 hg2
  have hsub' :
      (∫ r in (0 : ℝ)..1,
          (g ∘ f) r * f' r) =
        ∫ t in (0 : ℝ)..1, g t := by
    simpa [f, hn.ne'] using hsub
  calc
    (∫ r in (0 : ℝ)..1,
        nthRoot n (1 - r ^ n) * r) =
        1 / (n : ℝ) *
          ∫ r in (0 : ℝ)..1,
            (g ∘ f) r * f' r := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr_ae
      filter_upwards [ae_real_ne 0] with r hr0 hrmem
      have hrpos : 0 < r := by
        have hrmem' : r ∈ Set.Ioc (0 : ℝ) 1 := by
          simpa [Set.uIoc_of_le zero_le_one] using hrmem
        exact hrmem'.1
      dsimp [nthRoot, g, f, f']
      have hpowder :=
        rpow_pow_mul_pow_deriv n hn r hrpos
      calc
        Real.rpow (1 - r ^ n) (1 / (n : ℝ)) * r =
            1 / (n : ℝ) *
              (Real.rpow (1 - r ^ n) (1 / (n : ℝ)) *
                ((n : ℝ) * r)) := by
          field_simp
        _ = 1 / (n : ℝ) *
              (Real.rpow (1 - r ^ n) (1 / (n : ℝ)) *
                (Real.rpow (r ^ n) (2 / (n : ℝ) - 1) *
                  ((n : ℝ) * r ^ (n - 1)))) := by
          rw [hpowder]
        _ = _ := by
          simp only [Real.rpow_eq_pow]
          ring
    _ = 1 / (n : ℝ) *
        ∫ t in (0 : ℝ)..1,
          Real.rpow (1 - t) (1 / (n : ℝ)) *
            Real.rpow t (2 / (n : ℝ) - 1) := by
      rw [hsub']

theorem gap9 (n : ℕ) (hn : 0 < n) :
    1 / (n : ℝ) *
        (∫ t in (0 : ℝ)..1,
          Real.rpow (1 - t) (1 / (n : ℝ)) *
            Real.rpow t (2 / (n : ℝ) - 1)) =
      1 / (n : ℝ) * betaFn (1 / (n : ℝ) + 1) (2 / (n : ℝ)) := by
  unfold betaFn
  congr 2
  funext t
  congr 2 <;> ring

private theorem betaFn_eq_Gamma_mul_div
    (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    betaFn x y =
      Real.Gamma x * Real.Gamma y / Real.Gamma (x + y) := by
  unfold betaFn
  apply Complex.ofReal_injective
  rw [← intervalIntegral.integral_ofReal]
  calc
    (∫ t in (0 : ℝ)..1,
        ((Real.rpow (1 - t) (x - 1) *
          Real.rpow t (y - 1) : ℝ) : ℂ)) =
        Complex.betaIntegral (y : ℂ) (x : ℂ) := by
      rw [Complex.betaIntegral]
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le zero_le_one] at ht
      change
        ((Real.rpow (1 - t) (x - 1) *
          Real.rpow t (y - 1) : ℝ) : ℂ) =
          (t : ℂ) ^ ((y : ℂ) - 1) *
            (1 - (t : ℂ)) ^ ((x : ℂ) - 1)
      have hpow1 :=
        Complex.ofReal_cpow (sub_nonneg.mpr ht.2) (x - 1)
      have hpow2 :=
        Complex.ofReal_cpow ht.1 (y - 1)
      rw [Real.rpow_eq_pow, Real.rpow_eq_pow,
        Complex.ofReal_mul, hpow1, hpow2]
      push_cast
      ring
    _ = Complex.Gamma (y : ℂ) * Complex.Gamma (x : ℂ) /
          Complex.Gamma ((y : ℂ) + (x : ℂ)) :=
      Complex.betaIntegral_eq_Gamma_mul_div
        (y : ℂ) (x : ℂ) (by simpa) (by simpa)
    _ = ((Real.Gamma x * Real.Gamma y /
          Real.Gamma (x + y) : ℝ) : ℂ) := by
      rw [Complex.Gamma_ofReal, Complex.Gamma_ofReal,
        ← Complex.ofReal_add, Complex.Gamma_ofReal]
      push_cast
      ring

theorem gap10 (n : ℕ) (hn : 0 < n) :
    betaFn (1 / (n : ℝ) + 1) (2 / (n : ℝ)) =
      Real.Gamma (1 / (n : ℝ) + 1) *
          Real.Gamma (2 / (n : ℝ)) /
        Real.Gamma (1 + 3 / (n : ℝ)) := by
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  rw [betaFn_eq_Gamma_mul_div]
  · congr 1
    ring
  · positivity
  · positivity

theorem gap11 (n : ℕ) (hn : 0 < n) :
    Real.Gamma (1 / (n : ℝ) + 1) *
          Real.Gamma (2 / (n : ℝ)) /
          Real.Gamma (1 + 3 / (n : ℝ)) =
      Real.Gamma (1 / (n : ℝ)) * Real.Gamma (2 / (n : ℝ)) /
        (3 * Real.Gamma (3 / (n : ℝ))) := by
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have h1 : 1 / (n : ℝ) ≠ 0 := by positivity
  have h3 : 3 / (n : ℝ) ≠ 0 := by positivity
  rw [show 1 / (n : ℝ) + 1 =
      (1 / (n : ℝ)) + 1 by ring,
    Real.Gamma_add_one h1]
  rw [show 1 + 3 / (n : ℝ) =
      (3 / (n : ℝ)) + 1 by ring,
    Real.Gamma_add_one h3]
  field_simp

theorem gap12 (n : ℕ) (hn : 0 < n) :
    (∫ r in (0 : ℝ)..1, nthRoot n (1 - r ^ n) * r) =
      Real.Gamma (1 / (n : ℝ)) * Real.Gamma (2 / (n : ℝ)) /
        (3 * (n : ℝ) * Real.Gamma (3 / (n : ℝ))) := by
  rw [gap8 n hn, gap9 n hn, gap10 n hn, gap11 n hn]
  have hnR : (n : ℝ) ≠ 0 := (Nat.cast_ne_zero.mpr hn.ne')
  field_simp

private theorem rpow_sq_mul_self
    (n : ℕ) (hn : 0 < n) (x : ℝ) (hx : 0 < x) :
    Real.rpow (x ^ 2) (1 / (n : ℝ) - 1) * x =
      Real.rpow x ((2 - (n : ℝ)) / (n : ℝ)) := by
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hpow :
      Real.rpow (x ^ 2) (1 / (n : ℝ) - 1) =
        Real.rpow x (2 * (1 / (n : ℝ) - 1)) := by
    calc
      Real.rpow (x ^ 2) (1 / (n : ℝ) - 1) =
          Real.rpow (Real.rpow x (2 : ℝ))
            (1 / (n : ℝ) - 1) := by
        congr 1
        exact (Real.rpow_natCast x 2).symm
      _ = Real.rpow x
            (2 * (1 / (n : ℝ) - 1)) :=
        (Real.rpow_mul hx.le 2
          (1 / (n : ℝ) - 1)).symm
  have hexp :
      2 * (1 / (n : ℝ) - 1) + 1 =
        (2 - (n : ℝ)) / (n : ℝ) := by
    field_simp
    ring
  rw [hpow]
  calc
    Real.rpow x (2 * (1 / (n : ℝ) - 1)) * x =
        Real.rpow x (2 * (1 / (n : ℝ) - 1)) *
          Real.rpow x 1 := by
      exact congrArg
        (fun z : ℝ =>
          Real.rpow x (2 * (1 / (n : ℝ) - 1)) * z)
        (Real.rpow_one x).symm
    _ = Real.rpow x
          (2 * (1 / (n : ℝ) - 1) + 1) :=
      (Real.rpow_add hx
        (2 * (1 / (n : ℝ) - 1)) 1).symm
    _ = Real.rpow x ((2 - (n : ℝ)) / (n : ℝ)) := by
      rw [hexp]

private theorem trig_rpow_product_intervalIntegrable
    (e : ℝ) (he : -1 < e) :
    IntervalIntegrable
      (fun φ : ℝ =>
        Real.rpow (Real.cos φ) e *
          Real.rpow (Real.sin φ) e)
      MeasureTheory.volume 0 (Real.pi / 2) := by
  by_cases he0 : 0 ≤ e
  · exact
      ((Real.continuous_rpow_const he0).comp
        Real.continuous_cos |>.mul
          ((Real.continuous_rpow_const he0).comp
            Real.continuous_sin)).intervalIntegrable
        0 (Real.pi / 2)
  · have heneg : e < 0 := lt_of_not_ge he0
    let k : ℝ := 2 / Real.pi
    let q : ℝ := Real.cos (Real.pi / 4)
    let C : ℝ := Real.rpow k e * Real.rpow q e
    let D : ℝ → ℝ := fun φ => C * Real.rpow φ e
    have hk : 0 < k := by
      dsimp [k]
      positivity
    have hq : 0 < q := by
      dsimp [q]
      exact Real.cos_pos_of_mem_Ioo
        ⟨by linarith [Real.pi_pos],
          by linarith [Real.pi_pos]⟩
    have hD :
        IntervalIntegrable D MeasureTheory.volume
          0 (Real.pi / 4) := by
      exact
        (intervalIntegral.intervalIntegrable_rpow'
          (a := (0 : ℝ)) (b := Real.pi / 4) he).const_mul C
    have hleft :
        IntervalIntegrable
          (fun φ : ℝ =>
            Real.rpow (Real.cos φ) e *
              Real.rpow (Real.sin φ) e)
          MeasureTheory.volume 0 (Real.pi / 4) := by
      rw [intervalIntegrable_iff_integrableOn_Icc_of_le
        (by positivity : (0 : ℝ) ≤ Real.pi / 4)]
      have hDon :
          IntegrableOn D (Set.Icc (0 : ℝ) (Real.pi / 4)) :=
        (intervalIntegrable_iff_integrableOn_Icc_of_le
          (by positivity : (0 : ℝ) ≤ Real.pi / 4)).mp hD
      apply hDon.mono'
      · measurability
      · filter_upwards
          [ae_restrict_mem measurableSet_Icc]
          with φ hφ
        have hφhalf : φ ≤ Real.pi / 2 := by
          linarith [hφ.2, Real.pi_pos]
        have hsin0 : 0 ≤ Real.sin φ :=
          Real.sin_nonneg_of_nonneg_of_le_pi hφ.1
            (by linarith [hφhalf, Real.pi_pos])
        have hcos0 : 0 ≤ Real.cos φ :=
          Real.cos_nonneg_of_mem_Icc
            ⟨by linarith [Real.pi_pos, hφ.1], hφhalf⟩
        have hkφ : 0 ≤ k * φ := mul_nonneg hk.le hφ.1
        have hsinLower : k * φ ≤ Real.sin φ := by
          simpa [k] using Real.mul_le_sin hφ.1 hφhalf
        have hcosLower : q ≤ Real.cos φ := by
          dsimp [q]
          exact Real.cos_le_cos_of_nonneg_of_le_pi
            hφ.1 (by linarith [Real.pi_pos])
            hφ.2
        have hsinPow :
            Real.rpow (Real.sin φ) e ≤
              Real.rpow (k * φ) e := by
          by_cases hφ0 : φ = 0
          · subst φ
            simp [Real.rpow_zero]
          · exact Real.rpow_le_rpow_of_nonpos
              (mul_pos hk (lt_of_le_of_ne hφ.1
                (Ne.symm hφ0))) hsinLower heneg.le
        have hcosPow :
            Real.rpow (Real.cos φ) e ≤
              Real.rpow q e :=
          Real.rpow_le_rpow_of_nonpos
            hq hcosLower heneg.le
        have hkp :
            Real.rpow (k * φ) e =
              Real.rpow k e * Real.rpow φ e :=
          Real.mul_rpow hk.le hφ.1
        have hbound :
            Real.rpow (Real.cos φ) e *
                Real.rpow (Real.sin φ) e ≤
              D φ := by
          change
            Real.rpow (Real.cos φ) e *
                Real.rpow (Real.sin φ) e ≤
              Real.rpow k e * Real.rpow q e *
                Real.rpow φ e
          calc
            _ ≤ Real.rpow q e *
                Real.rpow (k * φ) e :=
              mul_le_mul hcosPow hsinPow
                (Real.rpow_nonneg hsin0 e)
                (Real.rpow_nonneg hq.le e)
            _ = _ := by rw [hkp]; ring
        rw [Real.norm_eq_abs]
        calc
          |Real.rpow (Real.cos φ) e *
              Real.rpow (Real.sin φ) e| =
              Real.rpow (Real.cos φ) e *
                Real.rpow (Real.sin φ) e :=
            abs_of_nonneg
              (mul_nonneg
                (Real.rpow_nonneg hcos0 e)
                (Real.rpow_nonneg hsin0 e))
          _ ≤ D φ := hbound
    have hright :
        IntervalIntegrable
          (fun φ : ℝ =>
            Real.rpow (Real.cos φ) e *
              Real.rpow (Real.sin φ) e)
          MeasureTheory.volume (Real.pi / 4)
            (Real.pi / 2) := by
      have hcomp := hleft.comp_sub_left (Real.pi / 2)
      convert hcomp.symm using 1
      · funext φ
        rw [Real.cos_pi_div_two_sub,
          Real.sin_pi_div_two_sub]
        ring
      · ring
      · ring
    exact hleft.trans hright

theorem gap13 (n : ℕ) (hn : 0 < n) :
    (∫ φ in (0 : ℝ)..Real.pi / 2,
        Real.rpow (Real.cos φ) ((2 - (n : ℝ)) / (n : ℝ)) *
          Real.rpow (Real.sin φ) ((2 - (n : ℝ)) / (n : ℝ))) =
      1 / 2 *
        ∫ t in (0 : ℝ)..1,
          Real.rpow (1 - t) (1 / (n : ℝ) - 1) *
            Real.rpow t (1 / (n : ℝ) - 1) := by
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  let e : ℝ := (2 - (n : ℝ)) / (n : ℝ)
  let q : ℝ := 1 / (n : ℝ) - 1
  let f : ℝ → ℝ := fun φ => Real.sin φ ^ 2
  let f' : ℝ → ℝ :=
    fun φ => 2 * Real.sin φ * Real.cos φ
  let g : ℝ → ℝ :=
    fun t =>
      Real.rpow (1 - t) q * Real.rpow t q
  let T : ℝ → ℝ :=
    fun φ =>
      Real.rpow (Real.cos φ) e *
        Real.rpow (Real.sin φ) e
  have he : -1 < e := by
    dsimp [e]
    have hpos : 0 < 2 / (n : ℝ) := by positivity
    have heq :
        (2 - (n : ℝ)) / (n : ℝ) + 1 =
          2 / (n : ℝ) := by
      field_simp
      ring
    linarith
  have hq : -1 < q := by
    dsimp [q]
    have hpos : 0 < 1 / (n : ℝ) := by positivity
    linarith
  have hf :
      ContinuousOn f [[(0 : ℝ), Real.pi / 2]] := by
    exact (Real.continuous_sin.pow 2).continuousOn
  have hder :
      ∀ φ ∈ Set.Ioo (min (0 : ℝ) (Real.pi / 2))
          (max (0 : ℝ) (Real.pi / 2)),
        HasDerivWithinAt f (f' φ) (Set.Ioi φ) φ := by
    intro φ hφ
    apply HasDerivAt.hasDerivWithinAt
    dsimp [f, f']
    convert (Real.hasDerivAt_sin φ).pow 2 using 1 <;>
      simp <;> ring
  have hf' :
      ContinuousOn f' [[(0 : ℝ), Real.pi / 2]] := by
    exact
      ((continuous_const.mul Real.continuous_sin).mul
        Real.continuous_cos).continuousOn
  have hg :
      ContinuousOn g
        (f '' Set.Ioo (min (0 : ℝ) (Real.pi / 2))
          (max (0 : ℝ) (Real.pi / 2))) := by
    apply continuousOn_of_forall_continuousAt
    intro t ht
    rcases ht with ⟨φ, hφ, rfl⟩
    rw [min_eq_left (by positivity :
        (0 : ℝ) ≤ Real.pi / 2),
      max_eq_right (by positivity :
        (0 : ℝ) ≤ Real.pi / 2)] at hφ
    have hsin :
        0 < Real.sin φ :=
      Real.sin_pos_of_pos_of_lt_pi hφ.1
        (by linarith [hφ.2, Real.pi_pos])
    have hcos :
        0 < Real.cos φ :=
      Real.cos_pos_of_mem_Ioo
        ⟨by linarith [hφ.1, Real.pi_pos], hφ.2⟩
    have hsqpos : 0 < Real.sin φ ^ 2 := sq_pos_of_pos hsin
    have hsquared :
        Real.sin φ ^ 2 < 1 := by
      nlinarith [Real.sin_sq_add_cos_sq φ,
        sq_pos_of_pos hcos]
    have hleft :
        ContinuousAt
          (fun t : ℝ => Real.rpow (1 - t) q)
          (Real.sin φ ^ 2) := by
      simpa [Function.comp_def] using
        (Real.continuousAt_rpow_const
          (1 - Real.sin φ ^ 2) q
          (Or.inl (sub_ne_zero.mpr hsquared.ne'))).comp
          (continuous_const.sub continuous_id).continuousAt
    have hright :
        ContinuousAt
          (fun t : ℝ => Real.rpow t q)
          (Real.sin φ ^ 2) :=
      Real.continuousAt_rpow_const
        (Real.sin φ ^ 2) q (Or.inl hsqpos.ne')
    exact hleft.mul hright
  have hg1 :
      IntegrableOn g
        (f '' [[(0 : ℝ), Real.pi / 2]]) := by
    have hbeta :
        IntervalIntegrable g MeasureTheory.volume 0 1 := by
      have h := beta_intervalIntegrable q q hq hq
      refine h.congr ?_
      intro t ht
      dsimp [g]
      ring
    have hIcc : IntegrableOn g (Set.Icc (0 : ℝ) 1) :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le
        zero_le_one).mp hbeta
    exact hIcc.mono_set (by
      rintro t ⟨φ, hφ, rfl⟩
      exact ⟨sq_nonneg _, Real.sin_sq_le_one φ⟩)
  have hpoint (φ : ℝ) (hφ0 : 0 < φ)
      (hφ1 : φ < Real.pi / 2) :
      (g ∘ f) φ * f' φ = 2 * T φ := by
    have hsin :
        0 < Real.sin φ :=
      Real.sin_pos_of_pos_of_lt_pi hφ0
        (by linarith [hφ1, Real.pi_pos])
    have hcos :
        0 < Real.cos φ :=
      Real.cos_pos_of_mem_Ioo
        ⟨by linarith [hφ0, Real.pi_pos], hφ1⟩
    have hsinPow :=
      rpow_sq_mul_self n hn (Real.sin φ) hsin
    have hcosPow :=
      rpow_sq_mul_self n hn (Real.cos φ) hcos
    have htrig :
        1 - Real.sin φ ^ 2 =
          Real.cos φ ^ 2 := by
      nlinarith [Real.sin_sq_add_cos_sq φ]
    dsimp [g, f, f', T, q, e]
    rw [htrig]
    calc
      (Real.rpow (Real.cos φ ^ 2)
            (1 / (n : ℝ) - 1) *
          Real.rpow (Real.sin φ ^ 2)
            (1 / (n : ℝ) - 1)) *
            (2 * Real.sin φ * Real.cos φ) =
          2 *
            (Real.rpow (Real.cos φ ^ 2)
                (1 / (n : ℝ) - 1) * Real.cos φ) *
            (Real.rpow (Real.sin φ ^ 2)
                (1 / (n : ℝ) - 1) * Real.sin φ) := by
        ring
      _ = 2 *
          (Real.rpow (Real.cos φ)
              ((2 - (n : ℝ)) / (n : ℝ))) *
          (Real.rpow (Real.sin φ)
              ((2 - (n : ℝ)) / (n : ℝ))) := by
        rw [hcosPow, hsinPow]
      _ = 2 *
          (Real.cos φ ^ ((2 - (n : ℝ)) / (n : ℝ)) *
            Real.sin φ ^ ((2 - (n : ℝ)) / (n : ℝ))) := by
        simp only [Real.rpow_eq_pow]
        ring
  have hg2 :
      IntegrableOn
        (fun φ => (g ∘ f) φ * f' φ)
        [[(0 : ℝ), Real.pi / 2]] := by
    have hTint :
        IntervalIntegrable T MeasureTheory.volume
          0 (Real.pi / 2) := by
      exact trig_rpow_product_intervalIntegrable e he
    have h2Tint :
        IntervalIntegrable (fun φ => 2 * T φ)
          MeasureTheory.volume 0 (Real.pi / 2) :=
      hTint.const_mul 2
    have hcomp :
        IntervalIntegrable
          (fun φ => (g ∘ f) φ * f' φ)
          MeasureTheory.volume 0 (Real.pi / 2) := by
      apply h2Tint.congr_ae
      filter_upwards
        [ae_restrict_mem measurableSet_uIoc,
          ae_restrict_of_ae (ae_real_ne (Real.pi / 2))]
        with φ hφ hne
      rw [Set.uIoc_of_le (by positivity :
        (0 : ℝ) ≤ Real.pi / 2)] at hφ
      exact (hpoint φ hφ.1
        (lt_of_le_of_ne hφ.2 hne)).symm
    simpa [Set.uIcc_of_le (by positivity :
        (0 : ℝ) ≤ Real.pi / 2)] using
      (intervalIntegrable_iff_integrableOn_Icc_of_le
        (by positivity : (0 : ℝ) ≤ Real.pi / 2)).mp hcomp
  have hsub :=
    intervalIntegral.integral_comp_mul_deriv'''
      (a := (0 : ℝ)) (b := Real.pi / 2)
      (f := f) (f' := f') (g := g)
      hf hder hg hg1 hg2
  have hsub' :
      (∫ φ in (0 : ℝ)..Real.pi / 2,
          (g ∘ f) φ * f' φ) =
        ∫ t in (0 : ℝ)..1, g t := by
    simpa [f] using hsub
  change
    (∫ φ in (0 : ℝ)..Real.pi / 2, T φ) =
      1 / 2 * ∫ t in (0 : ℝ)..1, g t
  calc
    (∫ φ in (0 : ℝ)..Real.pi / 2, T φ) =
        1 / 2 *
          ∫ φ in (0 : ℝ)..Real.pi / 2,
            (g ∘ f) φ * f' φ := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr_ae
      filter_upwards
        [ae_real_ne 0, ae_real_ne (Real.pi / 2)]
        with φ hzero hhalf hmem
      have hmem' :
          φ ∈ Set.Ioc (0 : ℝ) (Real.pi / 2) := by
        simpa [Set.uIoc_of_le (by positivity :
          (0 : ℝ) ≤ Real.pi / 2)] using hmem
      have hφlt : φ < Real.pi / 2 :=
        lt_of_le_of_ne hmem'.2 hhalf
      rw [hpoint φ hmem'.1 hφlt]
      ring
    _ = 1 / 2 *
        ∫ t in (0 : ℝ)..1,
          Real.rpow (1 - t) (1 / (n : ℝ) - 1) *
            Real.rpow t (1 / (n : ℝ) - 1) := by
      rw [hsub']

theorem gap14 (n : ℕ) (hn : 0 < n) :
    1 / 2 *
        (∫ t in (0 : ℝ)..1,
          Real.rpow (1 - t) (1 / (n : ℝ) - 1) *
            Real.rpow t (1 / (n : ℝ) - 1)) =
      1 / 2 * betaFn (1 / (n : ℝ)) (1 / (n : ℝ)) := by
  unfold betaFn
  rfl

theorem gap15 (n : ℕ) (hn : 0 < n) :
    1 / 2 * betaFn (1 / (n : ℝ)) (1 / (n : ℝ)) =
      1 / 2 *
        (Real.Gamma (1 / (n : ℝ)) ^ 2 /
          Real.Gamma (2 / (n : ℝ))) := by
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  rw [betaFn_eq_Gamma_mul_div]
  · congr 2 <;> ring
  · positivity
  · positivity

theorem gap16 (n : ℕ) (hn : 0 < n) :
    (∫ φ in (0 : ℝ)..Real.pi / 2,
        Real.rpow (Real.cos φ) ((2 - (n : ℝ)) / (n : ℝ)) *
          Real.rpow (Real.sin φ) ((2 - (n : ℝ)) / (n : ℝ))) =
      1 / 2 *
        (Real.Gamma (1 / (n : ℝ)) ^ 2 /
          Real.Gamma (2 / (n : ℝ))) := by
  rw [gap13 n hn, gap14 n hn, gap15 n hn]

private def activeParameterDomain : Set (ℝ × ℝ) :=
  Set.Ioc (0 : ℝ) 1 ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)

private def positiveBaseRegion (a b : ℝ) (n : ℕ) :
    Set (ℝ × ℝ) :=
  {p |
    0 < p.1 ∧ 0 < p.2 ∧
      p.1 ^ n / a ^ n + p.2 ^ n / b ^ n ≤ 1}

private def parameterMap (a b : ℝ) (n : ℕ)
    (p : ℝ × ℝ) : ℝ × ℝ :=
  (paramX a n p.1 p.2, paramY b n p.1 p.2)

private theorem rpow_two_div_pow (n : ℕ) (hn : 0 < n)
    (z : ℝ) (hz : 0 ≤ z) :
    (Real.rpow z (2 / (n : ℝ))) ^ n = z ^ 2 := by
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  calc
    (Real.rpow z (2 / (n : ℝ))) ^ n =
        Real.rpow (Real.rpow z (2 / (n : ℝ))) (n : ℝ) := by
      exact
        (Real.rpow_natCast
          (Real.rpow z (2 / (n : ℝ))) n).symm
    _ = Real.rpow z ((2 / (n : ℝ)) * (n : ℝ)) :=
      (Real.rpow_mul hz (2 / (n : ℝ)) (n : ℝ)).symm
    _ = Real.rpow z (2 : ℝ) := by
      congr 1
      field_simp
    _ = z ^ 2 := Real.rpow_natCast z 2

private theorem parameterMap_image (a b : ℝ) (n : ℕ)
    (hn : 0 < n) (ha : 0 < a) (hb : 0 < b) :
    parameterMap a b n '' activeParameterDomain =
      positiveBaseRegion a b n := by
  ext q
  constructor
  · rintro ⟨⟨r, φ⟩, hp, rfl⟩
    have hr : 0 < r := hp.1.1
    have hr1 : r ≤ 1 := hp.1.2
    have hφ0 : 0 < φ := hp.2.1
    have hφ1 : φ < Real.pi / 2 := hp.2.2
    have hsin : 0 < Real.sin φ :=
      Real.sin_pos_of_pos_of_lt_pi hφ0
        (by linarith [hφ1, Real.pi_pos])
    have hcos : 0 < Real.cos φ :=
      Real.cos_pos_of_mem_Ioo
        ⟨by linarith [hφ0, Real.pi_pos], hφ1⟩
    have hxpow :
        (paramX a n r φ) ^ n / a ^ n =
          r ^ n * Real.cos φ ^ 2 := by
      dsimp [paramX]
      calc
        (a * r * Real.rpow (Real.cos φ) (2 / (n : ℝ))) ^ n /
              a ^ n =
            r ^ n *
              (Real.rpow (Real.cos φ) (2 / (n : ℝ))) ^ n := by
          field_simp [ha.ne']
          ring
        _ = r ^ n * Real.cos φ ^ 2 := by
          rw [rpow_two_div_pow n hn (Real.cos φ) hcos.le]
    have hypow :
        (paramY b n r φ) ^ n / b ^ n =
          r ^ n * Real.sin φ ^ 2 := by
      dsimp [paramY]
      calc
        (b * r * Real.rpow (Real.sin φ) (2 / (n : ℝ))) ^ n /
              b ^ n =
            r ^ n *
              (Real.rpow (Real.sin φ) (2 / (n : ℝ))) ^ n := by
          field_simp [hb.ne']
          ring
        _ = r ^ n * Real.sin φ ^ 2 := by
          rw [rpow_two_div_pow n hn (Real.sin φ) hsin.le]
    refine ⟨?_, ?_, ?_⟩
    · exact mul_pos (mul_pos ha hr)
        (Real.rpow_pos_of_pos hcos _)
    · exact mul_pos (mul_pos hb hr)
        (Real.rpow_pos_of_pos hsin _)
    · change
        (paramX a n r φ) ^ n / a ^ n +
            (paramY b n r φ) ^ n / b ^ n ≤ 1
      rw [hxpow, hypow, ← mul_add,
        Real.cos_sq_add_sin_sq, mul_one]
      exact pow_le_one₀ hr.le hr1
  · intro hq
    let U : ℝ := q.1 ^ n / a ^ n
    let V : ℝ := q.2 ^ n / b ^ n
    let R : ℝ := U + V
    have hU : 0 < U := by
      dsimp [U]
      exact div_pos (pow_pos hq.1 n) (pow_pos ha n)
    have hV : 0 < V := by
      dsimp [V]
      exact div_pos (pow_pos hq.2.1 n) (pow_pos hb n)
    have hR : 0 < R := by
      dsimp [R]
      positivity
    have hR1 : R ≤ 1 := by
      simpa [R, U, V] using hq.2.2
    let r : ℝ := Real.rpow R (1 / (n : ℝ))
    let z : ℝ := Real.sqrt (U / R)
    let φ : ℝ := Real.arccos z
    have hratio : 0 < U / R := div_pos hU hR
    have hratio_lt : U / R < 1 :=
      (div_lt_one hR).2 (by dsimp [R]; linarith)
    have hz : 0 < z := by
      dsimp [z]
      exact Real.sqrt_pos.2 hratio
    have hz1 : z < 1 := by
      dsimp [z]
      rw [Real.sqrt_lt' zero_lt_one]
      simpa using hratio_lt
    have hφ0 : 0 < φ := by
      dsimp [φ]
      exact Real.arccos_pos.mpr hz1
    have hφ1 : φ < Real.pi / 2 := by
      dsimp [φ]
      exact Real.arccos_lt_pi_div_two.mpr hz
    have hr : 0 < r := by
      dsimp [r]
      exact Real.rpow_pos_of_pos hR _
    have hr1 : r ≤ 1 := by
      dsimp [r]
      exact Real.rpow_le_one hR.le hR1 (by positivity)
    have hrpow : r ^ n = R := by
      dsimp [r]
      simpa [one_div] using
        Real.rpow_inv_natCast_pow hR.le hn.ne'
    have hcos : Real.cos φ = z := by
      dsimp [φ]
      exact Real.cos_arccos (by linarith) hz1.le
    have hcosSq : Real.cos φ ^ 2 = U / R := by
      rw [hcos]
      dsimp [z]
      exact Real.sq_sqrt hratio.le
    have hsinSq : Real.sin φ ^ 2 = V / R := by
      have hnonneg : 0 ≤ 1 - z ^ 2 := by
        nlinarith [sq_nonneg z]
      rw [show φ = Real.arccos z by rfl,
        Real.sin_arccos, Real.sq_sqrt hnonneg]
      rw [show z ^ 2 = U / R by
        dsimp [z]
        exact Real.sq_sqrt hratio.le]
      dsimp [R]
      field_simp [hR.ne']
      ring
    have hxpos : 0 < paramX a n r φ := by
      exact mul_pos (mul_pos ha hr)
        (Real.rpow_pos_of_pos (hcos.trans_gt hz) _)
    have hypos : 0 < paramY b n r φ := by
      have hsin : 0 < Real.sin φ :=
        Real.sin_pos_of_pos_of_lt_pi hφ0
          (by linarith [hφ1, Real.pi_pos])
      exact mul_pos (mul_pos hb hr)
        (Real.rpow_pos_of_pos hsin _)
    have hxpow :
        (paramX a n r φ) ^ n = q.1 ^ n := by
      dsimp [paramX]
      calc
        (a * r * Real.rpow (Real.cos φ) (2 / (n : ℝ))) ^ n =
            a ^ n * r ^ n *
              (Real.rpow (Real.cos φ) (2 / (n : ℝ))) ^ n := by
          ring
        _ = a ^ n * R * (U / R) := by
          rw [hrpow,
            rpow_two_div_pow n hn (Real.cos φ)
              (hcos.trans_gt hz).le,
            hcosSq]
        _ = q.1 ^ n := by
          dsimp [U]
          field_simp [ha.ne', hR.ne']
    have hypow :
        (paramY b n r φ) ^ n = q.2 ^ n := by
      have hsin : 0 < Real.sin φ :=
        Real.sin_pos_of_pos_of_lt_pi hφ0
          (by linarith [hφ1, Real.pi_pos])
      dsimp [paramY]
      calc
        (b * r * Real.rpow (Real.sin φ) (2 / (n : ℝ))) ^ n =
            b ^ n * r ^ n *
              (Real.rpow (Real.sin φ) (2 / (n : ℝ))) ^ n := by
          ring
        _ = b ^ n * R * (V / R) := by
          rw [hrpow,
            rpow_two_div_pow n hn (Real.sin φ) hsin.le,
            hsinSq]
        _ = q.2 ^ n := by
          dsimp [V]
          field_simp [hb.ne', hR.ne']
    have hx : paramX a n r φ = q.1 :=
      (pow_left_strictMonoOn₀ hn.ne').injOn
        hxpos.le hq.1.le hxpow
    have hy : paramY b n r φ = q.2 :=
      (pow_left_strictMonoOn₀ hn.ne').injOn
        hypos.le hq.2.1.le hypow
    refine ⟨(r, φ), ⟨⟨hr, hr1⟩, ⟨hφ0, hφ1⟩⟩, ?_⟩
    exact Prod.ext hx hy

private theorem paramX_pow_div (a : ℝ) (n : ℕ)
    (hn : 0 < n) (ha : 0 < a) (r φ : ℝ)
    (hcos : 0 ≤ Real.cos φ) :
    (paramX a n r φ) ^ n / a ^ n =
      r ^ n * Real.cos φ ^ 2 := by
  dsimp [paramX]
  calc
    (a * r * Real.rpow (Real.cos φ) (2 / (n : ℝ))) ^ n /
          a ^ n =
        r ^ n *
          (Real.rpow (Real.cos φ) (2 / (n : ℝ))) ^ n := by
      field_simp [ha.ne']
      ring
    _ = r ^ n * Real.cos φ ^ 2 := by
      rw [rpow_two_div_pow n hn (Real.cos φ) hcos]

private theorem paramY_pow_div (b : ℝ) (n : ℕ)
    (hn : 0 < n) (hb : 0 < b) (r φ : ℝ)
    (hsin : 0 ≤ Real.sin φ) :
    (paramY b n r φ) ^ n / b ^ n =
      r ^ n * Real.sin φ ^ 2 := by
  dsimp [paramY]
  calc
    (b * r * Real.rpow (Real.sin φ) (2 / (n : ℝ))) ^ n /
          b ^ n =
        r ^ n *
          (Real.rpow (Real.sin φ) (2 / (n : ℝ))) ^ n := by
      field_simp [hb.ne']
      ring
    _ = r ^ n * Real.sin φ ^ 2 := by
      rw [rpow_two_div_pow n hn (Real.sin φ) hsin]

private theorem parameterMap_injOn (a b : ℝ) (n : ℕ)
    (hn : 0 < n) (ha : 0 < a) (hb : 0 < b) :
    Set.InjOn (parameterMap a b n) activeParameterDomain := by
  rintro ⟨r, φ⟩ hp ⟨s, ψ⟩ hq heq
  have hr : 0 < r := hp.1.1
  have hs : 0 < s := hq.1.1
  have hφ0 : 0 < φ := hp.2.1
  have hφ1 : φ < Real.pi / 2 := hp.2.2
  have hψ0 : 0 < ψ := hq.2.1
  have hψ1 : ψ < Real.pi / 2 := hq.2.2
  have hcosφ : 0 < Real.cos φ :=
    Real.cos_pos_of_mem_Ioo
      ⟨by linarith [hφ0, Real.pi_pos], hφ1⟩
  have hsinφ : 0 < Real.sin φ :=
    Real.sin_pos_of_pos_of_lt_pi hφ0
      (by linarith [hφ1, Real.pi_pos])
  have hcosψ : 0 < Real.cos ψ :=
    Real.cos_pos_of_mem_Ioo
      ⟨by linarith [hψ0, Real.pi_pos], hψ1⟩
  have hsinψ : 0 < Real.sin ψ :=
    Real.sin_pos_of_pos_of_lt_pi hψ0
      (by linarith [hψ1, Real.pi_pos])
  have hxraw : paramX a n r φ = paramX a n s ψ :=
    congrArg Prod.fst heq
  have hyraw : paramY b n r φ = paramY b n s ψ :=
    congrArg Prod.snd heq
  have hx :
      r ^ n * Real.cos φ ^ 2 =
        s ^ n * Real.cos ψ ^ 2 := by
    calc
      r ^ n * Real.cos φ ^ 2 =
          (paramX a n r φ) ^ n / a ^ n :=
        (paramX_pow_div a n hn ha r φ hcosφ.le).symm
      _ = (paramX a n s ψ) ^ n / a ^ n := by
        rw [hxraw]
      _ = s ^ n * Real.cos ψ ^ 2 :=
        paramX_pow_div a n hn ha s ψ hcosψ.le
  have hy :
      r ^ n * Real.sin φ ^ 2 =
        s ^ n * Real.sin ψ ^ 2 := by
    calc
      r ^ n * Real.sin φ ^ 2 =
          (paramY b n r φ) ^ n / b ^ n :=
        (paramY_pow_div b n hn hb r φ hsinφ.le).symm
      _ = (paramY b n s ψ) ^ n / b ^ n := by
        rw [hyraw]
      _ = s ^ n * Real.sin ψ ^ 2 :=
        paramY_pow_div b n hn hb s ψ hsinψ.le
  have hrsPow : r ^ n = s ^ n := by
    calc
      r ^ n = r ^ n *
          (Real.cos φ ^ 2 + Real.sin φ ^ 2) := by
        rw [Real.cos_sq_add_sin_sq, mul_one]
      _ = r ^ n * Real.cos φ ^ 2 +
          r ^ n * Real.sin φ ^ 2 := by ring
      _ = s ^ n * Real.cos ψ ^ 2 +
          s ^ n * Real.sin ψ ^ 2 := by rw [hx, hy]
      _ = s ^ n *
          (Real.cos ψ ^ 2 + Real.sin ψ ^ 2) := by ring
      _ = s ^ n := by
        rw [Real.cos_sq_add_sin_sq, mul_one]
  have hrs : r = s :=
    (pow_left_strictMonoOn₀ hn.ne').injOn hr.le hs.le hrsPow
  have hcosSq :
      Real.cos φ ^ 2 = Real.cos ψ ^ 2 := by
    rw [hrs] at hx
    exact mul_left_cancel₀ (pow_ne_zero n hs.ne') hx
  have hcos : Real.cos φ = Real.cos ψ :=
    (pow_left_strictMonoOn₀ two_ne_zero).injOn
      hcosφ.le hcosψ.le hcosSq
  have hφψ : φ = ψ := by
    apply Real.strictAntiOn_cos.injOn
    · exact
        ⟨hφ0.le,
          le_trans hφ1.le (by linarith [Real.pi_pos])⟩
    · exact
        ⟨hψ0.le,
          le_trans hψ1.le (by linarith [Real.pi_pos])⟩
    · exact hcos
  exact Prod.ext hrs hφψ

private def parameterDeriv (a b : ℝ) (n : ℕ)
    (p : ℝ × ℝ) : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  (Matrix.toLin (.finTwoProd ℝ) (.finTwoProd ℝ)
    !![
      a * Real.rpow (Real.cos p.2) (2 / (n : ℝ)),
      a * p.1 *
        ((2 / (n : ℝ)) *
          Real.rpow (Real.cos p.2) (2 / (n : ℝ) - 1) *
            (-Real.sin p.2));
      b * Real.rpow (Real.sin p.2) (2 / (n : ℝ)),
      b * p.1 * (2 / (n : ℝ)) *
        Real.rpow (Real.sin p.2) (2 / (n : ℝ) - 1) *
          Real.cos p.2
    ]).toContinuousLinearMap

private theorem parameterMap_hasFDerivAt (a b : ℝ) (n : ℕ)
    (p : ℝ × ℝ) (hcos : Real.cos p.2 ≠ 0)
    (hsin : Real.sin p.2 ≠ 0) :
    HasFDerivAt (parameterMap a b n)
      (parameterDeriv a b n p) p := by
  have hxpow :
      HasDerivAt
        (fun φ : ℝ =>
          Real.rpow (Real.cos φ) (2 / (n : ℝ)))
        ((2 / (n : ℝ)) *
          Real.rpow (Real.cos p.2) (2 / (n : ℝ) - 1) *
            (-Real.sin p.2)) p.2 := by
    exact
      (Real.hasDerivAt_rpow_const (Or.inl hcos)).comp
        p.2 (Real.hasDerivAt_cos p.2)
  have hypow :
      HasDerivAt
        (fun φ : ℝ =>
          Real.rpow (Real.sin φ) (2 / (n : ℝ)))
        ((2 / (n : ℝ)) *
          Real.rpow (Real.sin p.2) (2 / (n : ℝ) - 1) *
            Real.cos p.2) p.2 := by
    exact
      (Real.hasDerivAt_rpow_const (Or.inl hsin)).comp
        p.2 (Real.hasDerivAt_sin p.2)
  unfold parameterDeriv
  rw [Matrix.toLin_finTwoProd_toContinuousLinearMap]
  convert HasFDerivAt.prodMk (𝕜 := ℝ)
    ((hasFDerivAt_fst.mul
      (hxpow.comp_hasFDerivAt p hasFDerivAt_snd)).const_mul a)
    ((hasFDerivAt_fst.mul
      (hypow.comp_hasFDerivAt p hasFDerivAt_snd)).const_mul b)
      using 2
  all_goals
    simp [parameterMap, paramX, paramY, smul_smul,
      add_comm, add_left_comm, mul_assoc, neg_smul]
    try ring
  all_goals
    apply ContinuousLinearMap.ext
    intro v
    simp

private theorem det_parameterDeriv (a b : ℝ) (n : ℕ)
    (hn : 0 < n) (p : ℝ × ℝ)
    (hcos : Real.cos p.2 ≠ 0)
    (hsin : Real.sin p.2 ≠ 0) :
    (parameterDeriv a b n p).det =
      2 * a * b / (n : ℝ) * p.1 *
        Real.rpow (Real.cos p.2)
          ((2 - (n : ℝ)) / (n : ℝ)) *
        Real.rpow (Real.sin p.2)
          ((2 - (n : ℝ)) / (n : ℝ)) := by
  have hnR : (n : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr hn.ne'
  have hexp :
      2 / (n : ℝ) - 1 =
        (2 - (n : ℝ)) / (n : ℝ) := by
    field_simp
  have hcosPow :
      Real.rpow (Real.cos p.2) (2 / (n : ℝ)) =
        Real.rpow (Real.cos p.2) (2 / (n : ℝ) - 1) *
          Real.cos p.2 := by
    calc
      Real.rpow (Real.cos p.2) (2 / (n : ℝ)) =
          Real.rpow (Real.cos p.2)
            ((2 / (n : ℝ) - 1) + 1) := by
        congr 1
        ring
      _ = Real.rpow (Real.cos p.2) (2 / (n : ℝ) - 1) *
          Real.cos p.2 :=
        Real.rpow_add_one hcos (2 / (n : ℝ) - 1)
  have hsinPow :
      Real.rpow (Real.sin p.2) (2 / (n : ℝ)) =
        Real.rpow (Real.sin p.2) (2 / (n : ℝ) - 1) *
          Real.sin p.2 := by
    calc
      Real.rpow (Real.sin p.2) (2 / (n : ℝ)) =
          Real.rpow (Real.sin p.2)
            ((2 / (n : ℝ) - 1) + 1) := by
        congr 1
        ring
      _ = Real.rpow (Real.sin p.2) (2 / (n : ℝ) - 1) *
          Real.sin p.2 :=
        Real.rpow_add_one hsin (2 / (n : ℝ) - 1)
  unfold parameterDeriv
  simp only [LinearMap.det_toContinuousLinearMap,
    LinearMap.det_toLin, Matrix.det_fin_two_of]
  rw [hcosPow, hsinPow]
  calc
        a *
          (Real.rpow (Real.cos p.2)
            (2 / (n : ℝ) - 1) * Real.cos p.2) *
          (b * p.1 * (2 / (n : ℝ)) *
            Real.rpow (Real.sin p.2)
              (2 / (n : ℝ) - 1) * Real.cos p.2) -
        (a * p.1 *
          ((2 / (n : ℝ)) *
            Real.rpow (Real.cos p.2)
              (2 / (n : ℝ) - 1) * (-Real.sin p.2))) *
          (b * (Real.rpow (Real.sin p.2)
            (2 / (n : ℝ) - 1) * Real.sin p.2)) =
        a * b * p.1 * (2 / (n : ℝ)) *
          Real.rpow (Real.cos p.2)
            (2 / (n : ℝ) - 1) *
          Real.rpow (Real.sin p.2)
            (2 / (n : ℝ) - 1) *
          (Real.cos p.2 ^ 2 + Real.sin p.2 ^ 2) := by
          ring
    _ = a * b * p.1 * (2 / (n : ℝ)) *
          Real.rpow (Real.cos p.2)
            (2 / (n : ℝ) - 1) *
          Real.rpow (Real.sin p.2)
            (2 / (n : ℝ) - 1) := by
      rw [Real.cos_sq_add_sin_sq, mul_one]
    _ = 2 * a * b / (n : ℝ) * p.1 *
          Real.rpow (Real.cos p.2)
            ((2 - (n : ℝ)) / (n : ℝ)) *
          Real.rpow (Real.sin p.2)
            ((2 - (n : ℝ)) / (n : ℝ)) := by
      rw [hexp]
      ring

private theorem positiveBaseRegion_ae_eq (a b : ℝ) (n : ℕ) :
    positiveBaseRegion a b n =ᵐ[
      (MeasureTheory.volume : Measure (ℝ × ℝ))]
        baseRegion a b n := by
  have hfst :
      ∀ᵐ p : ℝ × ℝ
        ∂(MeasureTheory.volume : Measure (ℝ × ℝ)),
          p.1 ≠ 0 := by
    rw [Measure.volume_eq_prod]
    apply (Measure.ae_prod_iff_ae_ae
      (μ := (MeasureTheory.volume : Measure ℝ))
      (ν := (MeasureTheory.volume : Measure ℝ))
      (p := fun p : ℝ × ℝ => p.1 ≠ 0) (by
        exact
        (measurableSet_singleton (0 : ℝ)).compl.preimage
          measurable_fst)).2
    filter_upwards [ae_real_ne 0] with x hx
    exact Filter.Eventually.of_forall (fun _ => hx)
  have hsnd :
      ∀ᵐ p : ℝ × ℝ
        ∂(MeasureTheory.volume : Measure (ℝ × ℝ)),
          p.2 ≠ 0 := by
    rw [Measure.volume_eq_prod]
    apply (Measure.ae_prod_iff_ae_ae
      (μ := (MeasureTheory.volume : Measure ℝ))
      (ν := (MeasureTheory.volume : Measure ℝ))
      (p := fun p : ℝ × ℝ => p.2 ≠ 0) (by
        exact
        (measurableSet_singleton (0 : ℝ)).compl.preimage
          measurable_snd)).2
    filter_upwards with x
    exact ae_real_ne 0
  filter_upwards [hfst, hsnd] with p hpx hpy
  apply propext
  change
    (0 < p.1 ∧ 0 < p.2 ∧
        p.1 ^ n / a ^ n + p.2 ^ n / b ^ n ≤ 1) ↔
      (0 ≤ p.1 ∧ 0 ≤ p.2 ∧
        p.1 ^ n / a ^ n + p.2 ^ n / b ^ n ≤ 1)
  constructor
  · rintro ⟨hx, hy, hsum⟩
    exact ⟨hx.le, hy.le, hsum⟩
  · rintro ⟨hx, hy, hsum⟩
    exact
      ⟨lt_of_le_of_ne hx hpx.symm,
        lt_of_le_of_ne hy hpy.symm, hsum⟩

private theorem parameter_change_variables
    (a b : ℝ) (n : ℕ) (hn : 0 < n)
    (ha : 0 < a) (hb : 0 < b)
    (g : ℝ × ℝ → ℝ) :
    (∫ q in baseRegion a b n, g q) =
      ∫ p in activeParameterDomain,
        (2 * a * b / (n : ℝ) * p.1 *
          Real.rpow (Real.cos p.2)
            ((2 - (n : ℝ)) / (n : ℝ)) *
          Real.rpow (Real.sin p.2)
            ((2 - (n : ℝ)) / (n : ℝ))) *
          g (parameterMap a b n p) := by
  letI : Measure.IsAddHaarMeasure
      (MeasureTheory.volume : Measure (ℝ × ℝ)) := by
    rw [Measure.volume_eq_prod]
    infer_instance
  have hmeas : MeasurableSet activeParameterDomain :=
    measurableSet_Ioc.prod measurableSet_Ioo
  have hchange :=
    integral_image_eq_integral_abs_det_fderiv_smul
      (μ := MeasureTheory.volume) hmeas
      (f := parameterMap a b n)
      (f' := parameterDeriv a b n)
      (fun p hp => by
        have hcos : 0 < Real.cos p.2 :=
          Real.cos_pos_of_mem_Ioo
            ⟨by linarith [hp.2.1, Real.pi_pos], hp.2.2⟩
        have hsin : 0 < Real.sin p.2 :=
          Real.sin_pos_of_pos_of_lt_pi hp.2.1
            (by linarith [hp.2.2, Real.pi_pos])
        exact
          (parameterMap_hasFDerivAt a b n p
            hcos.ne' hsin.ne').hasFDerivWithinAt)
      (parameterMap_injOn a b n hn ha hb) g
  rw [parameterMap_image a b n hn ha hb] at hchange
  calc
    (∫ q in baseRegion a b n, g q) =
        ∫ q in positiveBaseRegion a b n, g q :=
      setIntegral_congr_set (positiveBaseRegion_ae_eq a b n).symm
    _ = ∫ p in activeParameterDomain,
          |(parameterDeriv a b n p).det| •
            g (parameterMap a b n p) := hchange
    _ = ∫ p in activeParameterDomain,
        (2 * a * b / (n : ℝ) * p.1 *
          Real.rpow (Real.cos p.2)
            ((2 - (n : ℝ)) / (n : ℝ)) *
          Real.rpow (Real.sin p.2)
            ((2 - (n : ℝ)) / (n : ℝ))) *
          g (parameterMap a b n p) := by
      apply setIntegral_congr_fun hmeas
      intro p hp
      have hcos : 0 < Real.cos p.2 :=
        Real.cos_pos_of_mem_Ioo
          ⟨by linarith [hp.2.1, Real.pi_pos], hp.2.2⟩
      have hsin : 0 < Real.sin p.2 :=
        Real.sin_pos_of_pos_of_lt_pi hp.2.1
          (by linarith [hp.2.2, Real.pi_pos])
      change
        |(parameterDeriv a b n p).det| *
            g (parameterMap a b n p) =
          (2 * a * b / (n : ℝ) * p.1 *
            Real.rpow (Real.cos p.2)
              ((2 - (n : ℝ)) / (n : ℝ)) *
            Real.rpow (Real.sin p.2)
              ((2 - (n : ℝ)) / (n : ℝ))) *
            g (parameterMap a b n p)
      rw [det_parameterDeriv a b n hn p hcos.ne' hsin.ne',
        abs_of_pos]
      have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
      have hp1 : 0 < p.1 := hp.1.1
      have hcosPow :
          0 < Real.rpow (Real.cos p.2)
            ((2 - (n : ℝ)) / (n : ℝ)) :=
        Real.rpow_pos_of_pos hcos _
      have hsinPow :
          0 < Real.rpow (Real.sin p.2)
            ((2 - (n : ℝ)) / (n : ℝ)) :=
        Real.rpow_pos_of_pos hsin _
      positivity

private theorem height_parameterMap
    (a b c : ℝ) (n : ℕ) (hn : 0 < n)
    (ha : 0 < a) (hb : 0 < b)
    (p : ℝ × ℝ) (hp : p ∈ activeParameterDomain) :
    height a b c n
        (parameterMap a b n p).1
        (parameterMap a b n p).2 =
      c * nthRoot n (1 - p.1 ^ n) := by
  have hcos : 0 < Real.cos p.2 :=
    Real.cos_pos_of_mem_Ioo
      ⟨by linarith [hp.2.1, Real.pi_pos], hp.2.2⟩
  have hsin : 0 < Real.sin p.2 :=
    Real.sin_pos_of_pos_of_lt_pi hp.2.1
      (by linarith [hp.2.2, Real.pi_pos])
  change
    c * nthRoot n
        (1 -
          ((paramX a n p.1 p.2) ^ n / a ^ n +
            (paramY b n p.1 p.2) ^ n / b ^ n)) =
      c * nthRoot n (1 - p.1 ^ n)
  rw [paramX_pow_div a n hn ha p.1 p.2 hcos.le,
    paramY_pow_div b n hn hb p.1 p.2 hsin.le,
    ← mul_add, Real.cos_sq_add_sin_sq, mul_one]

theorem gap7 (a b c : ℝ) (n : ℕ) (hn : 0 < n)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    volume a b c n =
      2 * a * b * c / (n : ℝ) *
        (∫ r in (0 : ℝ)..1, nthRoot n (1 - r ^ n) * r) *
          ∫ φ in (0 : ℝ)..Real.pi / 2,
            Real.rpow (Real.cos φ) ((2 - (n : ℝ)) / (n : ℝ)) *
              Real.rpow (Real.sin φ) ((2 - (n : ℝ)) / (n : ℝ)) := by
  let R : ℝ → ℝ :=
    fun r => nthRoot n (1 - r ^ n) * r
  let A : ℝ → ℝ :=
    fun φ =>
      Real.rpow (Real.cos φ)
          ((2 - (n : ℝ)) / (n : ℝ)) *
        Real.rpow (Real.sin φ)
          ((2 - (n : ℝ)) / (n : ℝ))
  let K : ℝ := 2 * a * b * c / (n : ℝ)
  have hchange :=
    parameter_change_variables a b n hn ha hb
      (fun q => height a b c n q.1 q.2)
  have hpull :
      volume a b c n =
        ∫ p in activeParameterDomain,
          K * (R p.1 * A p.2) := by
    rw [volume]
    calc
      (∫ q in baseRegion a b n,
          height a b c n q.1 q.2) =
          ∫ p in activeParameterDomain,
            (2 * a * b / (n : ℝ) * p.1 *
              Real.rpow (Real.cos p.2)
                ((2 - (n : ℝ)) / (n : ℝ)) *
              Real.rpow (Real.sin p.2)
                ((2 - (n : ℝ)) / (n : ℝ))) *
              height a b c n
                (parameterMap a b n p).1
                (parameterMap a b n p).2 := hchange
      _ = ∫ p in activeParameterDomain,
            K * (R p.1 * A p.2) := by
        apply setIntegral_congr_fun
          (measurableSet_Ioc.prod measurableSet_Ioo)
        intro p hp
        change
          (2 * a * b / (n : ℝ) * p.1 *
            Real.rpow (Real.cos p.2)
              ((2 - (n : ℝ)) / (n : ℝ)) *
            Real.rpow (Real.sin p.2)
              ((2 - (n : ℝ)) / (n : ℝ))) *
              height a b c n
                (parameterMap a b n p).1
                (parameterMap a b n p).2 =
            K * (R p.1 * A p.2)
        rw [height_parameterMap a b c n hn ha hb p hp]
        dsimp [K, R, A]
        ring
  have hprod :
      (∫ p in activeParameterDomain, R p.1 * A p.2) =
        (∫ r in Set.Ioc (0 : ℝ) 1, R r) *
          ∫ φ in Set.Ioo (0 : ℝ) (Real.pi / 2), A φ := by
    rw [Measure.volume_eq_prod]
    exact
      setIntegral_prod_mul R A
        (Set.Ioc (0 : ℝ) 1)
        (Set.Ioo (0 : ℝ) (Real.pi / 2))
  have hradial :
      (∫ r in Set.Ioc (0 : ℝ) 1, R r) =
        ∫ r in (0 : ℝ)..1, R r := by
    rw [intervalIntegral.integral_of_le zero_le_one]
  have angularBounds : (0 : ℝ) ≤ Real.pi / 2 := by
    positivity
  have hangular :
      (∫ φ in Set.Ioo (0 : ℝ) (Real.pi / 2), A φ) =
        ∫ φ in (0 : ℝ)..Real.pi / 2, A φ := by
    calc
      (∫ φ in Set.Ioo (0 : ℝ) (Real.pi / 2), A φ) =
          ∫ φ in Set.Ioc (0 : ℝ) (Real.pi / 2), A φ :=
        (integral_Ioc_eq_integral_Ioo (f := A)).symm
      _ = ∫ φ in (0 : ℝ)..Real.pi / 2, A φ := by
        rw [intervalIntegral.integral_of_le angularBounds]
  calc
    volume a b c n =
        ∫ p in activeParameterDomain,
          K * (R p.1 * A p.2) := hpull
    _ = K *
        ∫ p in activeParameterDomain,
          R p.1 * A p.2 := by
      rw [integral_const_mul]
    _ = K *
        ((∫ r in Set.Ioc (0 : ℝ) 1, R r) *
          ∫ φ in Set.Ioo (0 : ℝ) (Real.pi / 2), A φ) := by
      rw [hprod]
    _ = K *
        ((∫ r in (0 : ℝ)..1, R r) *
          ∫ φ in (0 : ℝ)..Real.pi / 2, A φ) := by
      rw [hradial, hangular]
    _ = 2 * a * b * c / (n : ℝ) *
        (∫ r in (0 : ℝ)..1, nthRoot n (1 - r ^ n) * r) *
          ∫ φ in (0 : ℝ)..Real.pi / 2,
            Real.rpow (Real.cos φ)
                ((2 - (n : ℝ)) / (n : ℝ)) *
              Real.rpow (Real.sin φ)
                ((2 - (n : ℝ)) / (n : ℝ)) := by
      dsimp [K, R, A]
      ring

theorem gap17 (a b c : ℝ) (n : ℕ) (hn : 0 < n)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    volume a b c n =
      a * b * c / (n : ℝ) ^ 2 *
        (Real.Gamma (1 / (n : ℝ)) * Real.Gamma (2 / (n : ℝ)) /
          (3 * Real.Gamma (3 / (n : ℝ)))) *
        (Real.Gamma (1 / (n : ℝ)) ^ 2 /
          Real.Gamma (2 / (n : ℝ))) := by
  rw [gap7 a b c n hn ha hb hc, gap12 n hn, gap16 n hn]
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  field_simp

theorem gap18 (a b c : ℝ) (n : ℕ) (hn : 0 < n) :
    a * b * c / (n : ℝ) ^ 2 *
          (Real.Gamma (1 / (n : ℝ)) * Real.Gamma (2 / (n : ℝ)) /
            (3 * Real.Gamma (3 / (n : ℝ)))) *
          (Real.Gamma (1 / (n : ℝ)) ^ 2 /
            Real.Gamma (2 / (n : ℝ))) =
      a * b * c / (3 * (n : ℝ) ^ 2) *
        (Real.Gamma (1 / (n : ℝ)) ^ 3 /
          Real.Gamma (3 / (n : ℝ))) := by
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hgamma2 :
      Real.Gamma (2 / (n : ℝ)) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by positivity)).ne'
  field_simp

theorem gap19 (a b c : ℝ) (n : ℕ) (hn : 0 < n)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    volume a b c n =
      a * b * c / (3 * (n : ℝ) ^ 2) *
        (Real.Gamma (1 / (n : ℝ)) ^ 3 /
          Real.Gamma (3 / (n : ℝ))) := by
  rw [gap17 a b c n hn ha hb hc, gap18 a b c n hn]

end

end ProofGap.Exercise4034
