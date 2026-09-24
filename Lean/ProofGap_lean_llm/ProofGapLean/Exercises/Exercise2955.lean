import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Analysis.Complex.AbelLimit
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Typeclasses.NoAtoms
import Mathlib.Topology.Algebra.InfiniteSum.Basic

namespace ProofGap.Exercise2955

noncomputable section

open scoped Interval
open scoped Topology

open Filter Finset

def fracPart (x : ℝ) : ℝ :=
  x - (Int.floor x : ℝ)

def integers : Set ℝ :=
  Set.range (fun z : ℤ => (z : ℝ))

def cosineIntegral (n : ℕ) : ℝ :=
  2 * ∫ x in 0..1,
    fracPart x * Real.cos (2 * (n : ℝ) * Real.pi * x)

def linearCosineIntegral (n : ℕ) : ℝ :=
  2 * ∫ x in 0..1,
    x * Real.cos (2 * (n : ℝ) * Real.pi * x)

def cosineAntiderivative (n : ℕ) (x : ℝ) : ℝ :=
  2 *
    (x / (2 * (n : ℝ) * Real.pi) *
        Real.sin (2 * (n : ℝ) * Real.pi * x) +
      1 / (4 * ((n : ℝ) * Real.pi) ^ 2) *
        Real.cos (2 * (n : ℝ) * Real.pi * x))

def cosineEval (n : ℕ) : ℝ :=
  cosineAntiderivative n 1 - cosineAntiderivative n 0

def sineIntegral (n : ℕ) : ℝ :=
  2 * ∫ x in 0..1,
    fracPart x * Real.sin (2 * (n : ℝ) * Real.pi * x)

def linearSineIntegral (n : ℕ) : ℝ :=
  2 * ∫ x in 0..1,
    x * Real.sin (2 * (n : ℝ) * Real.pi * x)

def sineAntiderivative (n : ℕ) (x : ℝ) : ℝ :=
  2 *
    (-x / (2 * (n : ℝ) * Real.pi) *
        Real.cos (2 * (n : ℝ) * Real.pi * x) +
      1 / (4 * ((n : ℝ) * Real.pi) ^ 2) *
        Real.sin (2 * (n : ℝ) * Real.pi * x))

def sineEval (n : ℕ) : ℝ :=
  sineAntiderivative n 1 - sineAntiderivative n 0

def fourierSeries (x : ℝ) : ℝ :=
  1 / 2 -
    1 / Real.pi *
      ∑'[SummationFilter.conditional ℕ] k : ℕ,
        Real.sin (2 * (k + 1 : ℝ) * Real.pi * x) / (k + 1 : ℝ)

theorem gap1 (f : ℝ → ℝ) (hf : ∀ x, f x = fracPart x) :
    ∀ x, f (x + 1) =
      x + 1 - (Int.floor (x + 1) : ℝ) := by
  intro x
  exact hf (x + 1)

theorem gap2 :
    ∀ x : ℝ,
      x + 1 - (Int.floor (x + 1) : ℝ) =
        x + 1 - (Int.floor x : ℝ) - 1 := by
  intro x
  rw [Int.floor_add_one]
  rw [Int.cast_add, Int.cast_one]
  ring

theorem gap3 :
    ∀ x : ℝ,
      x + 1 - (Int.floor x : ℝ) - 1 =
        x - (Int.floor x : ℝ) := by
  intro x
  ring

theorem gap4 (f : ℝ → ℝ) (hf : ∀ x, f x = fracPart x) :
    ∀ x, x - (Int.floor x : ℝ) = f x := by
  intro x
  rw [hf]
  rfl

theorem gap5 (f : ℝ → ℝ) (hf : ∀ x, f x = fracPart x) :
    ∀ x, f (x + 1) = f x := by
  intro x
  rw [hf, hf]
  simp [fracPart]

theorem gap6 (f : ℝ → ℝ) (hf : ∀ x, f x = fracPart x) :
    Function.Periodic f 1 := by
  exact gap5 f hf

theorem gap7 (f : ℝ → ℝ) (hf : ∀ x, f x = fracPart x) :
    ∀ x, x ∉ integers → ContinuousAt f x := by
  intro x hx
  have hne : x ≠ (Int.floor x : ℝ) := by
    intro h
    apply hx
    exact ⟨Int.floor x, h.symm⟩
  have hfract : ContinuousAt (Int.fract : ℝ → ℝ) x :=
    continuousAt_fract hne
  convert hfract using 1
  funext y
  rw [hf]
  rfl

theorem gap8 (c : ℕ → ℝ)
    (hc : c 0 = 2 * ∫ x in 0..1, fracPart x) :
    c 0 = 1 / (1 / 2 : ℝ) * ∫ x in 0..1, fracPart x := by
  convert hc using 1 <;> norm_num

theorem gap9 :
    1 / (1 / 2 : ℝ) * (∫ x in 0..1, fracPart x) =
      2 * ∫ x in 0..1, x := by
  have hInt :
      (∫ x in 0..1, fracPart x) = ∫ x in 0..1, x := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [MeasureTheory.Measure.ae_ne MeasureTheory.volume (1 : ℝ)] with x hx hI
    rw [Set.uIoc_of_le (by norm_num)] at hI
    have hfloor : Int.floor x = 0 :=
      Int.floor_eq_zero_iff.mpr
        ⟨hI.1.le, lt_of_le_of_ne hI.2 hx⟩
    simp [fracPart, hfloor]
  rw [hInt]
  norm_num

theorem gap10 :
    2 * (∫ x in 0..1, x) = 1 := by
  norm_num

theorem gap11 (c : ℕ → ℝ)
    (hc : c 0 = 2 * ∫ x in 0..1, fracPart x) :
    c 0 = 1 := by
  calc
    c 0 = 1 / (1 / 2 : ℝ) * ∫ x in 0..1, fracPart x := gap8 c hc
    _ = 2 * ∫ x in 0..1, x := gap9
    _ = 1 := gap10

theorem gap12 (c : ℕ → ℝ)
    (hc : ∀ n : ℕ, 1 ≤ n → c n = cosineIntegral n) :
    ∀ n : ℕ, 1 ≤ n → c n = cosineIntegral n := by
  exact hc

theorem gap13 :
    ∀ n : ℕ, 1 ≤ n →
      cosineIntegral n = linearCosineIntegral n := by
  intro n hn
  unfold cosineIntegral linearCosineIntegral
  congr 1
  apply intervalIntegral.integral_congr_ae
  filter_upwards [MeasureTheory.Measure.ae_ne MeasureTheory.volume (1 : ℝ)] with x hx hI
  rw [Set.uIoc_of_le (by norm_num)] at hI
  have hfloor : Int.floor x = 0 :=
    Int.floor_eq_zero_iff.mpr
      ⟨hI.1.le, lt_of_le_of_ne hI.2 hx⟩
  simp [fracPart, hfloor]

theorem gap14 (c : ℕ → ℝ)
    (hc : ∀ n : ℕ, 1 ≤ n → c n = cosineIntegral n) :
    ∀ n : ℕ, 1 ≤ n → c n = linearCosineIntegral n := by
  intro n hn
  rw [hc n hn, gap13 n hn]

theorem gap15 (c : ℕ → ℝ)
    (hc : ∀ n : ℕ, 1 ≤ n → c n = linearCosineIntegral n) :
    ∀ n : ℕ, 1 ≤ n → c n = cosineEval n := by
  intro n hn
  rw [hc n hn]
  unfold linearCosineIntegral cosineEval
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x hx
    have hn0 : (n : ℝ) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt hn
    have hq : (n : ℝ) * Real.pi ≠ 0 :=
      mul_ne_zero hn0 Real.pi_ne_zero
    have hA : 2 * (n : ℝ) * Real.pi ≠ 0 := by
      positivity
    have harg :
        HasDerivAt (fun y : ℝ => 2 * (n : ℝ) * Real.pi * y)
          (2 * (n : ℝ) * Real.pi) x := by
      convert (hasDerivAt_id x).const_mul
        (2 * (n : ℝ) * Real.pi) using 1 <;> ring
    have hsin :=
      (Real.hasDerivAt_sin (2 * (n : ℝ) * Real.pi * x)).comp x harg
    have hcos :=
      (Real.hasDerivAt_cos (2 * (n : ℝ) * Real.pi * x)).comp x harg
    have hfirst :=
      ((hasDerivAt_id x).div_const (2 * (n : ℝ) * Real.pi)).mul hsin
    have hsecond :=
      hcos.const_mul (1 / (4 * ((n : ℝ) * Real.pi) ^ 2))
    have htotal := (hfirst.add hsecond).const_mul 2
    convert htotal using 1 <;>
      simp only [Function.comp_apply, id_eq] <;>
      field_simp [hA, hq] <;>
      ring
  · apply Continuous.intervalIntegrable
    fun_prop

theorem gap16 :
    ∀ n : ℕ, 1 ≤ n → cosineEval n = 0 := by
  intro n hn
  have hs :
      Real.sin (2 * (n : ℝ) * Real.pi * 1) = 0 := by
    rw [show 2 * (n : ℝ) * Real.pi * 1 =
      ((2 * n : ℕ) : ℝ) * Real.pi by push_cast; ring]
    exact Real.sin_nat_mul_pi _
  have hc :
      Real.cos (2 * (n : ℝ) * Real.pi * 1) = 1 := by
    rw [show 2 * (n : ℝ) * Real.pi * 1 =
      (n : ℝ) * (2 * Real.pi) by ring]
    exact Real.cos_nat_mul_two_pi n
  unfold cosineEval cosineAntiderivative
  rw [hs, hc]
  norm_num

theorem gap17 (c : ℕ → ℝ)
    (hc : ∀ n : ℕ, 1 ≤ n → c n = cosineIntegral n) :
    ∀ n : ℕ, 1 ≤ n → c n = 0 := by
  intro n hn
  have heval :
      c n = cosineEval n :=
    gap15 c (gap14 c hc) n hn
  rw [heval, gap16 n hn]

theorem gap18 (s : ℕ → ℝ)
    (hs : ∀ n : ℕ, 1 ≤ n → s n = sineIntegral n) :
    ∀ n : ℕ, 1 ≤ n → s n = sineIntegral n := by
  exact hs

theorem gap19 :
    ∀ n : ℕ, 1 ≤ n →
      sineIntegral n = linearSineIntegral n := by
  intro n hn
  unfold sineIntegral linearSineIntegral
  congr 1
  apply intervalIntegral.integral_congr_ae
  filter_upwards [MeasureTheory.Measure.ae_ne MeasureTheory.volume (1 : ℝ)] with x hx hI
  rw [Set.uIoc_of_le (by norm_num)] at hI
  have hfloor : Int.floor x = 0 :=
    Int.floor_eq_zero_iff.mpr
      ⟨hI.1.le, lt_of_le_of_ne hI.2 hx⟩
  simp [fracPart, hfloor]

theorem gap20 (s : ℕ → ℝ)
    (hs : ∀ n : ℕ, 1 ≤ n → s n = sineIntegral n) :
    ∀ n : ℕ, 1 ≤ n → s n = linearSineIntegral n := by
  intro n hn
  rw [hs n hn, gap19 n hn]

theorem gap21 (s : ℕ → ℝ)
    (hs : ∀ n : ℕ, 1 ≤ n → s n = linearSineIntegral n) :
    ∀ n : ℕ, 1 ≤ n → s n = sineEval n := by
  intro n hn
  rw [hs n hn]
  unfold linearSineIntegral sineEval
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x hx
    have hn0 : (n : ℝ) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt hn
    have hq : (n : ℝ) * Real.pi ≠ 0 :=
      mul_ne_zero hn0 Real.pi_ne_zero
    have hA : 2 * (n : ℝ) * Real.pi ≠ 0 := by
      positivity
    have harg :
        HasDerivAt (fun y : ℝ => 2 * (n : ℝ) * Real.pi * y)
          (2 * (n : ℝ) * Real.pi) x := by
      convert (hasDerivAt_id x).const_mul
        (2 * (n : ℝ) * Real.pi) using 1 <;> ring
    have hsin :=
      (Real.hasDerivAt_sin (2 * (n : ℝ) * Real.pi * x)).comp x harg
    have hcos :=
      (Real.hasDerivAt_cos (2 * (n : ℝ) * Real.pi * x)).comp x harg
    have hfirst :=
      ((hasDerivAt_id x).neg.div_const
        (2 * (n : ℝ) * Real.pi)).mul hcos
    have hsecond :=
      hsin.const_mul (1 / (4 * ((n : ℝ) * Real.pi) ^ 2))
    have htotal := (hfirst.add hsecond).const_mul 2
    convert htotal using 1 <;>
      simp only [Function.comp_apply, Pi.neg_apply, id_eq] <;>
      field_simp [hA, hq] <;>
      ring
  · apply Continuous.intervalIntegrable
    fun_prop

theorem gap22 :
    ∀ n : ℕ, 1 ≤ n →
      sineEval n = -(1 / ((n : ℝ) * Real.pi)) := by
  intro n hn
  have hn0 : (n : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hn
  have hq : (n : ℝ) * Real.pi ≠ 0 :=
    mul_ne_zero hn0 Real.pi_ne_zero
  have hs :
      Real.sin (2 * (n : ℝ) * Real.pi * 1) = 0 := by
    rw [show 2 * (n : ℝ) * Real.pi * 1 =
      ((2 * n : ℕ) : ℝ) * Real.pi by push_cast; ring]
    exact Real.sin_nat_mul_pi _
  have hc :
      Real.cos (2 * (n : ℝ) * Real.pi * 1) = 1 := by
    rw [show 2 * (n : ℝ) * Real.pi * 1 =
      (n : ℝ) * (2 * Real.pi) by ring]
    exact Real.cos_nat_mul_two_pi n
  unfold sineEval sineAntiderivative
  rw [hs, hc]
  norm_num
  field_simp [hq]

theorem gap23 (s : ℕ → ℝ)
    (hs : ∀ n : ℕ, 1 ≤ n → s n = sineIntegral n) :
    ∀ n : ℕ, 1 ≤ n →
      s n = -(1 / ((n : ℝ) * Real.pi)) := by
  intro n hn
  have heval : s n = sineEval n :=
    gap21 s (gap20 s hs) n hn
  rw [heval, gap22 n hn]

private lemma sine_harmonic_series_hasSum
    (x : ℝ) (hx : ∀ z : ℤ, x ≠ (z : ℝ)) :
    HasSum
      (fun k : ℕ =>
        Real.sin (2 * (k + 1 : ℝ) * Real.pi * x) / (k + 1 : ℝ))
      (Real.pi * (1 / 2 - Int.fract x))
      (SummationFilter.conditional ℕ) := by
  let y : ℝ := Int.fract x
  let a : ℝ := Real.pi * y
  let θ : ℝ := a - Real.pi / 2
  let r : ℝ := 2 * Real.sin a
  let ζ : ℂ := Complex.exp ((x : ℂ) * (2 * Real.pi * Complex.I))
  have hyne : y ≠ 0 := by
    apply Int.fract_ne_zero_iff.mpr
    rintro ⟨z, hz⟩
    exact hx z hz.symm
  have hypos : 0 < y := (Int.fract_nonneg x).lt_of_ne hyne.symm
  have hylt : y < 1 := Int.fract_lt_one x
  have ha0 : 0 < a := mul_pos Real.pi_pos hypos
  have hapi : a < Real.pi := by
    dsimp [a]
    nlinarith [Real.pi_pos]
  have hsina : 0 < Real.sin a :=
    Real.sin_pos_of_pos_of_lt_pi ha0 hapi
  have hrpos : 0 < r := by
    dsimp [r]
    positivity
  have hθ : θ ∈ Set.Ioc (-Real.pi) Real.pi := by
    dsimp [θ]
    constructor <;> linarith [ha0, hapi, Real.pi_pos]
  have hζy :
      ζ = Complex.exp ((y : ℂ) * (2 * Real.pi * Complex.I)) := by
    dsimp [ζ]
    rw [Complex.exp_eq_exp_iff_exists_int]
    refine ⟨Int.floor x, ?_⟩
    have hsplit := Int.fract_add_floor x
    have hsplitC :
        (y : ℂ) + (Int.floor x : ℂ) = (x : ℂ) := by
      exact_mod_cast hsplit
    rw [← hsplitC]
    ring
  have hζexp :
      ζ = Complex.exp ((2 * a : ℂ) * Complex.I) := by
    rw [hζy]
    congr 1
    dsimp [a]
    push_cast
    ring
  have hpolar :
      1 - ζ = (r : ℂ) *
        ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I) := by
    rw [hζexp, Complex.exp_mul_I]
    have hcast : (2 * a : ℂ) = ((2 * a : ℝ) : ℂ) := by norm_num
    rw [hcast, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    dsimp [r, θ]
    rw [Real.cos_sub, Real.sin_sub]
    simp only [Real.cos_pi_div_two, Real.sin_pi_div_two, mul_zero,
      mul_one, add_zero, zero_mul, sub_zero]
    rw [Real.sin_two_mul, Real.cos_two_mul]
    apply Complex.ext
    · simp only [Complex.sub_re, Complex.sub_im, Complex.one_re,
        Complex.one_im, Complex.mul_re, Complex.mul_im, Complex.add_re,
        Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, zero_mul, add_zero,
        zero_add, sub_zero, mul_one]
      nlinarith [Real.sin_sq_add_cos_sq a]
    · simp only [Complex.sub_re, Complex.sub_im, Complex.one_re,
        Complex.one_im, Complex.mul_re, Complex.mul_im, Complex.add_re,
        Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, zero_mul, add_zero,
        zero_add, sub_zero, mul_one]
      ring
  have hunit :
      (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I ≠ 0 := by
    rw [Complex.ofReal_cos, Complex.ofReal_sin, ← Complex.exp_mul_I]
    exact Complex.exp_ne_zero _
  have honeζ : 1 - ζ ≠ 0 := by
    rw [hpolar]
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hrpos.ne') hunit
  have hζne : ζ ≠ 1 := by
    intro hz
    apply honeζ
    rw [hz, sub_self]
  have harg : (1 - ζ).arg = θ := by
    rw [hpolar, Complex.ofReal_cos, Complex.ofReal_sin]
    exact Complex.arg_mul_cos_add_sin_mul_I hrpos hθ
  have hslit : 1 - ζ ∈ Complex.slitPlane := by
    apply Complex.mem_slitPlane_iff_arg.mpr
    exact ⟨by rw [harg]; dsimp [θ]; linarith [hapi, Real.pi_pos], honeζ⟩
  have hζnorm : ‖ζ‖ = 1 := by
    dsimp [ζ]
    rw [Complex.norm_exp]
    simp [Complex.mul_re]
  have hpartial_bound :
      ∀ n : ℕ, ‖∑ i ∈ range n, ζ ^ (i + 1)‖ ≤
        2 / ‖ζ - 1‖ := by
    intro n
    have hsum :
        (∑ i ∈ range n, ζ ^ (i + 1)) =
          ζ * ∑ i ∈ range n, ζ ^ i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [pow_succ']
    rw [hsum, geom_sum_eq hζne, norm_mul, hζnorm, one_mul, norm_div]
    apply div_le_div_of_nonneg_right _ (norm_nonneg _)
    calc
      ‖ζ ^ n - 1‖ ≤ ‖ζ ^ n‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, hζnorm]; norm_num
  have hanti : Antitone (fun n : ℕ => 1 / (n + 1 : ℝ)) := by
    intro m n hmn
    apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast Nat.add_le_add_right hmn 1
  have hzero :
      Tendsto (fun n : ℕ => 1 / (n + 1 : ℝ)) atTop (𝓝 0) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hcauchy0 :=
    hanti.cauchySeq_series_mul_of_tendsto_zero_of_bounded
      hzero hpartial_bound
  have hcauchy :
      CauchySeq
        (fun n => ∑ i ∈ range n, ζ ^ (i + 1) / (i + 1 : ℂ)) := by
    convert hcauchy0 using 1
    funext n
    apply Finset.sum_congr rfl
    intro i hi
    calc
      ζ ^ (i + 1) / (i + 1 : ℂ) =
          ((1 / (i + 1 : ℝ) : ℝ) : ℂ) * ζ ^ (i + 1) := by
        push_cast
        ring
      _ = (1 / (i + 1 : ℝ)) • ζ ^ (i + 1) :=
        Complex.real_smul.symm
  obtain ⟨l, hlim⟩ := cauchySeq_tendsto_of_complete hcauchy
  have habel := Complex.tendsto_tsum_powerSeries_nhdsWithin_lt hlim
  rw [tendsto_map'_iff] at habel
  have hcoe :
      Tendsto (fun u : ℝ => (u : ℂ)) (𝓝[<] (1 : ℝ)) (𝓝 (1 : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.mono_left inf_le_left
  have habelmul :
      Tendsto
        (fun u : ℝ =>
          (u : ℂ) *
            ∑' n : ℕ, (ζ ^ (n + 1) / (n + 1 : ℂ)) * (u : ℂ) ^ n)
        (𝓝[<] (1 : ℝ)) (𝓝 l) := by
    simpa using hcoe.mul habel
  have hpower_log :
      (fun u : ℝ =>
        (u : ℂ) *
          ∑' n : ℕ, (ζ ^ (n + 1) / (n + 1 : ℂ)) * (u : ℂ) ^ n) =ᶠ[
        𝓝[<] (1 : ℝ)]
      (fun u : ℝ => -Complex.log (1 - (u : ℂ) * ζ)) := by
    filter_upwards [Ioo_mem_nhdsLT one_pos] with u hu
    have huz : ‖(u : ℂ) * ζ‖ < 1 := by
      rw [norm_mul, Complex.norm_real, hζnorm, mul_one,
        Real.norm_eq_abs, abs_of_pos hu.1]
      exact hu.2
    have hlog0 := Complex.hasSum_taylorSeries_neg_log huz
    have hlog :
        HasSum
          (fun n : ℕ => ((u : ℂ) * ζ) ^ (n + 1) / (n + 1 : ℂ))
          (-Complex.log (1 - (u : ℂ) * ζ)) := by
      have hshift := (hasSum_nat_add_iff' 1).2 hlog0
      convert hshift using 1 with n <;> simp
    calc
      (u : ℂ) *
          ∑' n : ℕ, (ζ ^ (n + 1) / (n + 1 : ℂ)) * (u : ℂ) ^ n =
          ∑' n : ℕ,
            (u : ℂ) *
              ((ζ ^ (n + 1) / (n + 1 : ℂ)) * (u : ℂ) ^ n) := by
        rw [tsum_mul_left]
      _ = ∑' n : ℕ, ((u : ℂ) * ζ) ^ (n + 1) / (n + 1 : ℂ) := by
        apply tsum_congr
        intro n
        rw [mul_pow]
        ring
      _ = -Complex.log (1 - (u : ℂ) * ζ) := hlog.tsum_eq
  have habellog :
      Tendsto (fun u : ℝ => -Complex.log (1 - (u : ℂ) * ζ))
        (𝓝[<] (1 : ℝ)) (𝓝 l) :=
    habelmul.congr' hpower_log
  have hinner :
      Tendsto (fun u : ℝ => 1 - (u : ℂ) * ζ)
        (𝓝[<] (1 : ℝ)) (𝓝 (1 - ζ)) := by
    simpa using tendsto_const_nhds.sub (hcoe.mul_const ζ)
  have hloglim :
      Tendsto (fun u : ℝ => -Complex.log (1 - (u : ℂ) * ζ))
        (𝓝[<] (1 : ℝ)) (𝓝 (-Complex.log (1 - ζ))) :=
    ((continuousAt_clog hslit).tendsto.comp hinner).neg
  have hl : l = -Complex.log (1 - ζ) :=
    tendsto_nhds_unique habellog hloglim
  have himlim := (Complex.imCLM.continuous.tendsto l).comp hlim
  rw [hl] at himlim
  have himlim' :
      Tendsto
        (fun n => (∑ i ∈ range n, ζ ^ (i + 1) / (i + 1 : ℂ)).im)
        atTop (𝓝 (-Complex.log (1 - ζ)).im) := by
    simpa [Function.comp_def, Complex.imCLM_apply] using himlim
  have hvalue :
      (-Complex.log (1 - ζ)).im = Real.pi * (1 / 2 - y) := by
    rw [Complex.neg_im, Complex.log_im, harg]
    dsimp [θ, a]
    ring
  rw [hvalue] at himlim'
  have hpowim : ∀ i : ℕ,
      (ζ ^ (i + 1)).im =
        Real.sin (2 * (i + 1 : ℝ) * Real.pi * x) := by
    intro i
    dsimp [ζ]
    rw [← Complex.exp_nat_mul]
    have hexp :
        ((i + 1 : ℕ) : ℂ) * ((x : ℂ) * (2 * Real.pi * Complex.I)) =
          ((2 * (i + 1 : ℝ) * Real.pi * x : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [hexp, Complex.exp_mul_I]
    rw [← Complex.ofReal_cos, ← Complex.ofReal_sin]
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_im,
      Complex.ofReal_re, Complex.I_re, Complex.I_im, zero_add, mul_one,
      zero_mul, add_zero]
  have hreal :
      Tendsto
        (fun n => ∑ i ∈ range n,
          Real.sin (2 * (i + 1 : ℝ) * Real.pi * x) / (i + 1 : ℝ))
        atTop (𝓝 (Real.pi * (1 / 2 - y))) := by
    convert himlim' using 1
    funext n
    rw [Complex.im_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have hcastden :
        (i + 1 : ℂ) = ((i + 1 : ℝ) : ℂ) := by norm_num
    rw [hcastden, Complex.div_ofReal_im, hpowim]
  unfold HasSum
  rw [SummationFilter.conditional_filter_eq_map_range, tendsto_map'_iff]
  simpa [Function.comp_def] using hreal

theorem gap24 (f : ℝ → ℝ) (hf : ∀ x, f x = fracPart x) :
    ∀ x, x ∉ integers → f x = fourierSeries x := by
  intro x hx
  have hx' : ∀ z : ℤ, x ≠ (z : ℝ) := by
    intro z hz
    apply hx
    exact ⟨z, hz.symm⟩
  have hs := sine_harmonic_series_hasSum x hx'
  rw [hf x]
  unfold fourierSeries
  rw [hs.tsum_eq]
  change Int.fract x =
    1 / 2 - 1 / Real.pi * (Real.pi * (1 / 2 - Int.fract x))
  field_simp [Real.pi_ne_zero]
  ring

theorem gap25 :
    ∀ x, x ∉ integers → fourierSeries x = fracPart x := by
  intro x hx
  exact (gap24 fracPart (fun _ => rfl) x hx).symm

theorem gap26 (f : ℝ → ℝ) (hf : ∀ x, f x = fracPart x) :
    ∀ x, f x = fracPart x := by
  exact hf

end

end ProofGap.Exercise2955
