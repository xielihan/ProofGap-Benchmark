import ProofGapLean.Prelude.Sequences
import Mathlib.Analysis.Complex.AbelLimit
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Algebra.InfiniteSum.Basic

namespace ProofGap.Exercise2949

noncomputable section

open scoped Interval
open scoped Topology
open Filter Finset

def cosineIntegral (a l : ℝ) (n : ℕ) : ℝ :=
  1 / l *
    ∫ x in a..a + 2 * l,
      x * Real.cos ((n : ℝ) * Real.pi * x / l)

def sineIntegral (a l : ℝ) (n : ℕ) : ℝ :=
  1 / l *
    ∫ x in a..a + 2 * l,
      x * Real.sin ((n : ℝ) * Real.pi * x / l)

def cosineParts (a l : ℝ) (n : ℕ) : ℝ :=
  ((1 / ((n : ℝ) * Real.pi) * (a + 2 * l) *
        Real.sin ((n : ℝ) * Real.pi * (a + 2 * l) / l)) -
      (1 / ((n : ℝ) * Real.pi) * a *
        Real.sin ((n : ℝ) * Real.pi * a / l))) -
    1 / ((n : ℝ) * Real.pi) *
      ∫ x in a..a + 2 * l,
        Real.sin ((n : ℝ) * Real.pi * x / l)

def sineParts (a l : ℝ) (n : ℕ) : ℝ :=
  ((-1 / ((n : ℝ) * Real.pi) * (a + 2 * l) *
        Real.cos ((n : ℝ) * Real.pi * (a + 2 * l) / l)) -
      (-1 / ((n : ℝ) * Real.pi) * a *
        Real.cos ((n : ℝ) * Real.pi * a / l))) +
    1 / ((n : ℝ) * Real.pi) *
      ∫ x in a..a + 2 * l,
        Real.cos ((n : ℝ) * Real.pi * x / l)

def fourierSeries (a l x : ℝ) : ℝ :=
  a + l +
    2 * l / Real.pi *
      ∑'[SummationFilter.conditional ℕ] k : ℕ,
        1 / (k + 1 : ℝ) *
          (Real.sin ((k + 1 : ℝ) * Real.pi * a / l) *
              Real.cos ((k + 1 : ℝ) * Real.pi * x / l) -
            Real.cos ((k + 1 : ℝ) * Real.pi * a / l) *
              Real.sin ((k + 1 : ℝ) * Real.pi * x / l))

private def mulCosAntiderivative (c x : ℝ) : ℝ :=
  x * Real.sin (c * x) / c + Real.cos (c * x) / c ^ 2

private theorem hasDerivAt_mulCosAntiderivative
    (c : ℝ) (hc : c ≠ 0) (x : ℝ) :
    HasDerivAt (mulCosAntiderivative c) (x * Real.cos (c * x)) x := by
  have hinner : HasDerivAt (fun y : ℝ => c * y) c x := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id x).const_mul c
  have hsin :
      HasDerivAt (fun y : ℝ => Real.sin (c * y))
        (Real.cos (c * x) * c) x :=
    (Real.hasDerivAt_sin (c * x)).comp x hinner
  have hcos :
      HasDerivAt (fun y : ℝ => Real.cos (c * y))
        (-Real.sin (c * x) * c) x :=
    (Real.hasDerivAt_cos (c * x)).comp x hinner
  convert
    (((hasDerivAt_id x).mul hsin).div_const c).add
      (hcos.div_const (c ^ 2)) using 1
  field_simp [hc]
  simp only [id_eq]
  ring

private theorem integral_mul_cos_eq_sub
    (c : ℝ) (hc : c ≠ 0) (u v : ℝ) :
    (∫ x in u..v, x * Real.cos (c * x)) =
      mulCosAntiderivative c v - mulCosAntiderivative c u := by
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hasDerivAt_mulCosAntiderivative c hc x)
    ((continuous_id.mul
      (Real.continuous_cos.comp
        (continuous_const.mul continuous_id))).intervalIntegrable u v)

private def mulSinAntiderivative (c x : ℝ) : ℝ :=
  -(x * Real.cos (c * x)) / c + Real.sin (c * x) / c ^ 2

private theorem hasDerivAt_mulSinAntiderivative
    (c : ℝ) (hc : c ≠ 0) (x : ℝ) :
    HasDerivAt (mulSinAntiderivative c) (x * Real.sin (c * x)) x := by
  have hinner : HasDerivAt (fun y : ℝ => c * y) c x := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id x).const_mul c
  have hcos :
      HasDerivAt (fun y : ℝ => Real.cos (c * y))
        (-Real.sin (c * x) * c) x :=
    (Real.hasDerivAt_cos (c * x)).comp x hinner
  have hsin :
      HasDerivAt (fun y : ℝ => Real.sin (c * y))
        (Real.cos (c * x) * c) x :=
    (Real.hasDerivAt_sin (c * x)).comp x hinner
  convert
    ((((hasDerivAt_id x).mul hcos).neg).div_const c).add
      (hsin.div_const (c ^ 2)) using 1
  field_simp [hc]
  simp only [id_eq]
  ring

private theorem integral_mul_sin_eq_sub
    (c : ℝ) (hc : c ≠ 0) (u v : ℝ) :
    (∫ x in u..v, x * Real.sin (c * x)) =
      mulSinAntiderivative c v - mulSinAntiderivative c u := by
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hasDerivAt_mulSinAntiderivative c hc x)
    ((continuous_id.mul
      (Real.continuous_sin.comp
        (continuous_const.mul continuous_id))).intervalIntegrable u v)

private def sinAntiderivative (c x : ℝ) : ℝ :=
  -Real.cos (c * x) / c

private theorem hasDerivAt_sinAntiderivative
    (c : ℝ) (hc : c ≠ 0) (x : ℝ) :
    HasDerivAt (sinAntiderivative c) (Real.sin (c * x)) x := by
  have hinner : HasDerivAt (fun y : ℝ => c * y) c x := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id x).const_mul c
  have hcos :
      HasDerivAt (fun y : ℝ => Real.cos (c * y))
        (-Real.sin (c * x) * c) x :=
    (Real.hasDerivAt_cos (c * x)).comp x hinner
  convert hcos.neg.div_const c using 1
  field_simp [hc]

private theorem integral_sin_linear_eq_sub
    (c : ℝ) (hc : c ≠ 0) (u v : ℝ) :
    (∫ x in u..v, Real.sin (c * x)) =
      sinAntiderivative c v - sinAntiderivative c u := by
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hasDerivAt_sinAntiderivative c hc x)
    ((Real.continuous_sin.comp
      (continuous_const.mul continuous_id)).intervalIntegrable u v)

private def cosAntiderivative (c x : ℝ) : ℝ :=
  Real.sin (c * x) / c

private theorem hasDerivAt_cosAntiderivative
    (c : ℝ) (hc : c ≠ 0) (x : ℝ) :
    HasDerivAt (cosAntiderivative c) (Real.cos (c * x)) x := by
  have hinner : HasDerivAt (fun y : ℝ => c * y) c x := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id x).const_mul c
  have hsin :
      HasDerivAt (fun y : ℝ => Real.sin (c * y))
        (Real.cos (c * x) * c) x :=
    (Real.hasDerivAt_sin (c * x)).comp x hinner
  convert hsin.div_const c using 1
  field_simp [hc]

private theorem integral_cos_linear_eq_sub
    (c : ℝ) (hc : c ≠ 0) (u v : ℝ) :
    (∫ x in u..v, Real.cos (c * x)) =
      cosAntiderivative c v - cosAntiderivative c u := by
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hasDerivAt_cosAntiderivative c hc x)
    ((Real.continuous_cos.comp
      (continuous_const.mul continuous_id)).intervalIntegrable u v)

private theorem seriesHasSum_sin_nat_div
    (t : ℝ) (ht₀ : 0 < t) (ht₂ : t < 2 * Real.pi) :
    ProofGap.SeriesHasSum
      (fun k : ℕ =>
        Real.sin ((k + 1 : ℝ) * t) / (k + 1 : ℝ))
      ((Real.pi - t) / 2) := by
  let e : ℂ := Complex.exp ((t : ℂ) * Complex.I)
  have heNorm : ‖e‖ = 1 := by
    simpa [e] using Complex.norm_exp_ofReal_mul_I t
  have hhalf : 0 < Real.sin (t / 2) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · linarith
    · linarith
  have hcosHalf :
      1 - Real.cos t = 2 * Real.sin (t / 2) * Real.sin (t / 2) := by
    nth_rw 1 [show t = 2 * (t / 2) by ring]
    rw [Real.cos_two_mul]
    nlinarith [Real.sin_sq_add_cos_sq (t / 2)]
  have hsinHalf :
      -Real.sin t =
        2 * Real.sin (t / 2) * (-Real.cos (t / 2)) := by
    nth_rw 1 [show t = 2 * (t / 2) by ring]
    rw [Real.sin_two_mul]
    ring
  have hcosTheta :
      Real.cos ((t - Real.pi) / 2) = Real.sin (t / 2) := by
    rw [show (t - Real.pi) / 2 = t / 2 - Real.pi / 2 by ring,
      Real.cos_sub_pi_div_two]
  have hsinTheta :
      Real.sin ((t - Real.pi) / 2) = -Real.cos (t / 2) := by
    rw [show (t - Real.pi) / 2 = t / 2 - Real.pi / 2 by ring,
      Real.sin_sub_pi_div_two]
  have hfactor :
      (1 : ℂ) - e =
        (2 * Real.sin (t / 2) : ℝ) *
          (Real.cos ((t - Real.pi) / 2) +
            Real.sin ((t - Real.pi) / 2) * Complex.I) := by
    dsimp [e]
    apply Complex.ext
    · simp only [Complex.sub_re, Complex.one_re,
        Complex.exp_ofReal_mul_I_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, Complex.add_re, Complex.I_re, Complex.I_im,
        mul_zero, zero_mul, sub_zero, add_zero]
      rw [hcosTheta, hcosHalf]
    · simp only [Complex.sub_im, Complex.one_im,
        Complex.exp_ofReal_mul_I_im, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.add_im, Complex.I_re, Complex.I_im,
        mul_zero, zero_mul, sub_zero, add_zero, zero_sub, mul_one]
      rw [hsinTheta, hsinHalf]
      ring
  have heNe : e ≠ 1 := by
    apply sub_ne_zero.mp
    rw [← norm_pos_iff]
    rw [show e - 1 = -((1 : ℂ) - e) by ring, norm_neg, hfactor,
      norm_mul, Complex.norm_real, Complex.ofReal_cos,
      Complex.ofReal_sin, Complex.norm_cos_add_sin_mul_I,
      mul_one, Real.norm_eq_abs,
      abs_of_pos (mul_pos zero_lt_two hhalf)]
    positivity
  have hePowIm (n : ℕ) :
      (e ^ n).im = Real.sin ((n : ℝ) * t) := by
    dsimp [e]
    rw [← Complex.exp_nat_mul]
    convert Complex.exp_ofReal_mul_I_im ((n : ℝ) * t) using 2 <;>
      push_cast <;> ring
  have hBound (n : ℕ) :
      ‖∑ i ∈ Finset.range n, Real.sin ((i + 1 : ℝ) * t)‖ ≤
        2 / ‖e - 1‖ := by
    let S : ℂ := ∑ i ∈ Finset.range n, e ^ (i + 1)
    have hSim :
        S.im = ∑ i ∈ Finset.range n,
          Real.sin ((i + 1 : ℝ) * t) := by
      dsimp [S]
      rw [Complex.im_sum]
      exact Finset.sum_congr rfl fun i _ => by
        simpa only [Nat.cast_add, Nat.cast_one] using hePowIm (i + 1)
    have hS : S = e * ((e ^ n - 1) / (e - 1)) := by
      calc
        S = e * ∑ i ∈ Finset.range n, e ^ i := by
          dsimp [S]
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => pow_succ' e i
        _ = e * ((e ^ n - 1) / (e - 1)) := by
          rw [geom_sum_eq heNe]
    calc
      ‖∑ i ∈ Finset.range n, Real.sin ((i + 1 : ℝ) * t)‖ =
          ‖S.im‖ := by rw [hSim]
      _ ≤ ‖S‖ := by
        simpa [Real.norm_eq_abs] using Complex.abs_im_le_norm S
      _ = ‖e ^ n - 1‖ / ‖e - 1‖ := by
        rw [hS, norm_mul, norm_div, heNorm, one_mul]
      _ ≤ (‖e ^ n‖ + ‖(1 : ℂ)‖) / ‖e - 1‖ := by
        exact div_le_div_of_nonneg_right (norm_sub_le _ _) (norm_nonneg _)
      _ = 2 / ‖e - 1‖ := by norm_num [norm_pow, heNorm]
  have hAnti : Antitone (fun n : ℕ => (1 : ℝ) / (n + 1 : ℝ)) := by
    intro m n hmn
    exact one_div_le_one_div_of_le (by positivity)
      (by exact_mod_cast Nat.add_le_add_right hmn 1)
  have hZero :
      Filter.Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1 : ℝ))
        Filter.atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨s, hs⟩ :
      ∃ s : ℝ,
        Filter.Tendsto
          (fun n => ∑ i ∈ Finset.range n,
            Real.sin ((i + 1 : ℝ) * t) / (i + 1 : ℝ))
          Filter.atTop (𝓝 s) := by
    have hc :=
      hAnti.cauchySeq_series_mul_of_tendsto_zero_of_bounded hZero hBound
    obtain ⟨s, hs⟩ := cauchySeq_tendsto_of_complete hc
    refine ⟨s, ?_⟩
    simpa [smul_eq_mul, div_eq_mul_inv, mul_comm] using hs
  let g : ℕ → ℝ := fun n => Real.sin ((n : ℝ) * t) / (n : ℝ)
  have hg :
      Filter.Tendsto (fun n => ∑ i ∈ Finset.range n, g i)
        Filter.atTop (𝓝 s) := by
    rw [← (tendsto_add_atTop_iff_nat 1)]
    simpa [g, Finset.sum_range_succ'] using hs
  have hArg : Complex.arg ((1 : ℂ) - e) = (t - Real.pi) / 2 := by
    rw [hfactor, Complex.ofReal_cos, Complex.ofReal_sin,
      Complex.arg_mul_cos_add_sin_mul_I_eq_toIocMod (by positivity)]
    apply (toIocMod_eq_self Real.two_pi_pos).2
    constructor <;> dsimp <;> linarith [Real.pi_pos]
  have hSlit : (1 : ℂ) - e ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    left
    dsimp [e]
    simp only [Complex.sub_re, Complex.one_re,
      Complex.exp_ofReal_mul_I_re]
    rw [hcosHalf]
    positivity
  have hValue :
      (-Complex.log ((1 : ℂ) - e)).im = (Real.pi - t) / 2 := by
    rw [Complex.neg_im, Complex.log_im, hArg]
    ring
  have hLogLimit :
      Filter.Tendsto
        (fun r : ℝ =>
          (-Complex.log ((1 : ℂ) - (r : ℂ) * e)).im)
        (𝓝[<] (1 : ℝ)) (𝓝 ((Real.pi - t) / 2)) := by
    have hp :
        ContinuousAt (fun r : ℝ => (1 : ℂ) - (r : ℂ) * e) 1 := by
      fun_prop
    have hc :
        ContinuousAt
          (fun r : ℝ =>
            (-Complex.log ((1 : ℂ) - (r : ℂ) * e)).im) 1 :=
      Complex.continuous_im.continuousAt.comp
        ((hp.clog (by simpa using hSlit)).neg)
    convert hc.tendsto.mono_left
      (tendsto_nhdsWithin_of_tendsto_nhds fun _ h => h) using 1
    simpa using hValue.symm
  have hAbel := Real.tendsto_tsum_powerSeries_nhdsWithin_lt hg
  have hEq :
      (fun r : ℝ => ∑' n : ℕ, g n * r ^ n) =ᶠ[𝓝[<] (1 : ℝ)]
        (fun r : ℝ =>
          (-Complex.log ((1 : ℂ) - (r : ℂ) * e)).im) := by
    change ∀ᶠ r : ℝ in 𝓝[<] (1 : ℝ),
      (∑' n : ℕ, g n * r ^ n) =
        (-Complex.log ((1 : ℂ) - (r : ℂ) * e)).im
    rw [Filter.eventually_iff_exists_mem]
    refine ⟨Set.Ioo 0 1, Ioo_mem_nhdsLT (by norm_num), ?_⟩
    intro r hr
    have hz : ‖(r : ℂ) * e‖ < 1 := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hr.1, heNorm, mul_one]
      exact hr.2
    have hlog :=
      Complex.hasSum_im
        (Complex.hasSum_taylorSeries_neg_log (z := (r : ℂ) * e) hz)
    rw [← hlog.tsum_eq]
    apply tsum_congr
    intro n
    calc
      g n * r ^ n =
          ((((r ^ n / (n : ℝ) : ℝ) : ℂ) * e ^ n).im) := by
            rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
              zero_mul, add_zero, hePowIm]
            dsimp [g]
            ring
      _ = ((((r : ℂ) * e) ^ n / (n : ℂ)).im) := by
            congr 1
            rw [mul_pow]
            push_cast
            ring
  have hAbel' :
      Filter.Tendsto
        (fun r : ℝ =>
          (-Complex.log ((1 : ℂ) - (r : ℂ) * e)).im)
        (𝓝[<] (1 : ℝ)) (𝓝 s) :=
    hAbel.congr' hEq
  have hsValue : s = (Real.pi - t) / 2 :=
    tendsto_nhds_unique hAbel' hLogLimit
  rw [ProofGap.SeriesHasSum, HasSum,
    SummationFilter.conditional_filter_eq_map_range]
  simpa [Function.comp_def, hsValue] using hs

private theorem fourierSeries_eq_self
    (a l x : ℝ) (hl : 0 < l)
    (hx₀ : a < x) (hx₁ : x < a + 2 * l) :
    fourierSeries a l x = x := by
  let t : ℝ := Real.pi * (x - a) / l
  have ht₀ : 0 < t := by
    dsimp [t]
    exact div_pos (mul_pos Real.pi_pos (sub_pos.mpr hx₀)) hl
  have ht₂ : t < 2 * Real.pi := by
    dsimp [t]
    apply (div_lt_iff₀ hl).2
    nlinarith [Real.pi_pos]
  have hs := (seriesHasSum_sin_nat_div t ht₀ ht₂).neg
  have hterms :
      HasSum
        (fun k : ℕ =>
          1 / (k + 1 : ℝ) *
            (Real.sin ((k + 1 : ℝ) * Real.pi * a / l) *
                Real.cos ((k + 1 : ℝ) * Real.pi * x / l) -
              Real.cos ((k + 1 : ℝ) * Real.pi * a / l) *
                Real.sin ((k + 1 : ℝ) * Real.pi * x / l)))
        ((t - Real.pi) / 2) (SummationFilter.conditional ℕ) := by
    convert hs using 1
    · ext k
      rw [← Real.sin_sub]
      have harg :
          (k + 1 : ℝ) * Real.pi * a / l -
              (k + 1 : ℝ) * Real.pi * x / l =
            -((k + 1 : ℝ) * t) := by
        dsimp [t]
        ring
      rw [harg, Real.sin_neg]
      ring
    · ring
  unfold fourierSeries
  rw [hterms.tsum_eq]
  dsimp [t]
  field_simp [ne_of_gt hl, Real.pi_ne_zero]
  ring

theorem gap1 (a l : ℝ) (c : ℕ → ℝ) (hl : 0 < l)
    (hc : c 0 = 1 / l * ∫ x in a..a + 2 * l, x) :
    c 0 = 1 / l * ∫ x in a..a + 2 * l, x := by
  exact hc

theorem gap2 (a l : ℝ) (hl : 0 < l) :
    1 / l * (∫ x in a..a + 2 * l, x) = 2 * (a + l) := by
  rw [integral_id]
  field_simp [ne_of_gt hl]
  ring

theorem gap3 (a l : ℝ) (c : ℕ → ℝ) (hl : 0 < l)
    (hc : c 0 = 1 / l * ∫ x in a..a + 2 * l, x) :
    c 0 = 2 * (a + l) := by
  rw [hc]
  exact gap2 a l hl

theorem gap4 (a l : ℝ) (c : ℕ → ℝ) (hl : 0 < l)
    (hc : ∀ n : ℕ, 1 ≤ n → c n = cosineIntegral a l n) :
    ∀ n : ℕ, 1 ≤ n → c n = cosineIntegral a l n := by
  exact hc

theorem gap5 (a l : ℝ) (hl : 0 < l) :
    ∀ n : ℕ, 1 ≤ n →
      cosineIntegral a l n = cosineParts a l n := by
  intro n hn
  have hnpos : 0 < n := hn
  have hn0 : (n : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt hnpos)
  let q : ℝ := (n : ℝ) * Real.pi / l
  have hq0 : q ≠ 0 := by
    dsimp [q]
    exact div_ne_zero (mul_ne_zero hn0 Real.pi_ne_zero) (ne_of_gt hl)
  have harg (x : ℝ) : q * x = (n : ℝ) * Real.pi * x / l := by
    dsimp [q]
    ring
  have hmul :
      (∫ x in a..a + 2 * l,
        x * Real.cos ((n : ℝ) * Real.pi * x / l)) =
        mulCosAntiderivative q (a + 2 * l) -
          mulCosAntiderivative q a := by
    simpa only [harg] using
      integral_mul_cos_eq_sub q hq0 a (a + 2 * l)
  have hsin :
      (∫ x in a..a + 2 * l,
        Real.sin ((n : ℝ) * Real.pi * x / l)) =
        sinAntiderivative q (a + 2 * l) -
          sinAntiderivative q a := by
    simpa only [harg] using
      integral_sin_linear_eq_sub q hq0 a (a + 2 * l)
  unfold cosineIntegral cosineParts
  rw [hmul, hsin]
  simp only [mulCosAntiderivative, sinAntiderivative]
  dsimp [q]
  field_simp [hn0, Real.pi_ne_zero, ne_of_gt hl]
  ring

theorem gap6 (a l : ℝ) (hl : 0 < l) :
    ∀ n : ℕ, 1 ≤ n →
      cosineParts a l n =
        2 * l / ((n : ℝ) * Real.pi) *
          Real.sin ((n : ℝ) * Real.pi * a / l) := by
  intro n hn
  have hnpos : 0 < n := hn
  have hn0 : (n : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt hnpos)
  let q : ℝ := (n : ℝ) * Real.pi / l
  have hq0 : q ≠ 0 := by
    dsimp [q]
    exact div_ne_zero (mul_ne_zero hn0 Real.pi_ne_zero) (ne_of_gt hl)
  have harg (x : ℝ) : q * x = (n : ℝ) * Real.pi * x / l := by
    dsimp [q]
    ring
  have hend :
      (n : ℝ) * Real.pi * (a + 2 * l) / l =
        (n : ℝ) * Real.pi * a / l + (n : ℝ) * (2 * Real.pi) := by
    field_simp [ne_of_gt hl]
  have hsinend :
      Real.sin ((n : ℝ) * Real.pi * (a + 2 * l) / l) =
        Real.sin ((n : ℝ) * Real.pi * a / l) := by
    rw [hend]
    exact Real.sin_add_nat_mul_two_pi _ n
  have hcosend :
      Real.cos ((n : ℝ) * Real.pi * (a + 2 * l) / l) =
        Real.cos ((n : ℝ) * Real.pi * a / l) := by
    rw [hend]
    exact Real.cos_add_nat_mul_two_pi _ n
  have hsinInt :
      (∫ x in a..a + 2 * l,
        Real.sin ((n : ℝ) * Real.pi * x / l)) = 0 := by
    rw [show (∫ x in a..a + 2 * l,
        Real.sin ((n : ℝ) * Real.pi * x / l)) =
          sinAntiderivative q (a + 2 * l) -
            sinAntiderivative q a by
      simpa only [harg] using
        integral_sin_linear_eq_sub q hq0 a (a + 2 * l)]
    simp only [sinAntiderivative]
    rw [harg, harg, hcosend]
    ring
  unfold cosineParts
  rw [hsinInt, hsinend]
  ring

theorem gap7 (a l : ℝ) (c : ℕ → ℝ) (hl : 0 < l)
    (hc : ∀ n : ℕ, 1 ≤ n → c n = cosineIntegral a l n) :
    ∀ n : ℕ, 1 ≤ n →
      c n =
        2 * l / ((n : ℝ) * Real.pi) *
          Real.sin ((n : ℝ) * Real.pi * a / l) := by
  intro n hn
  rw [hc n hn, gap5 a l hl n hn, gap6 a l hl n hn]

theorem gap8 (a l : ℝ) (s : ℕ → ℝ) (hl : 0 < l)
    (hs : ∀ n : ℕ, 1 ≤ n → s n = sineIntegral a l n) :
    ∀ n : ℕ, 1 ≤ n → s n = sineIntegral a l n := by
  exact hs

theorem gap9 (a l : ℝ) (hl : 0 < l) :
    ∀ n : ℕ, 1 ≤ n →
      sineIntegral a l n = sineParts a l n := by
  intro n hn
  have hnpos : 0 < n := hn
  have hn0 : (n : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt hnpos)
  let q : ℝ := (n : ℝ) * Real.pi / l
  have hq0 : q ≠ 0 := by
    dsimp [q]
    exact div_ne_zero (mul_ne_zero hn0 Real.pi_ne_zero) (ne_of_gt hl)
  have harg (x : ℝ) : q * x = (n : ℝ) * Real.pi * x / l := by
    dsimp [q]
    ring
  have hmul :
      (∫ x in a..a + 2 * l,
        x * Real.sin ((n : ℝ) * Real.pi * x / l)) =
        mulSinAntiderivative q (a + 2 * l) -
          mulSinAntiderivative q a := by
    simpa only [harg] using
      integral_mul_sin_eq_sub q hq0 a (a + 2 * l)
  have hcos :
      (∫ x in a..a + 2 * l,
        Real.cos ((n : ℝ) * Real.pi * x / l)) =
        cosAntiderivative q (a + 2 * l) -
          cosAntiderivative q a := by
    simpa only [harg] using
      integral_cos_linear_eq_sub q hq0 a (a + 2 * l)
  unfold sineIntegral sineParts
  rw [hmul, hcos]
  simp only [mulSinAntiderivative, cosAntiderivative]
  dsimp [q]
  field_simp [hn0, Real.pi_ne_zero, ne_of_gt hl]
  ring

theorem gap10 (a l : ℝ) (hl : 0 < l) :
    ∀ n : ℕ, 1 ≤ n →
      sineParts a l n =
        -(2 * l / ((n : ℝ) * Real.pi)) *
          Real.cos ((n : ℝ) * Real.pi * a / l) := by
  intro n hn
  have hnpos : 0 < n := hn
  have hn0 : (n : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt hnpos)
  let q : ℝ := (n : ℝ) * Real.pi / l
  have hq0 : q ≠ 0 := by
    dsimp [q]
    exact div_ne_zero (mul_ne_zero hn0 Real.pi_ne_zero) (ne_of_gt hl)
  have harg (x : ℝ) : q * x = (n : ℝ) * Real.pi * x / l := by
    dsimp [q]
    ring
  have hend :
      (n : ℝ) * Real.pi * (a + 2 * l) / l =
        (n : ℝ) * Real.pi * a / l + (n : ℝ) * (2 * Real.pi) := by
    field_simp [ne_of_gt hl]
  have hsinend :
      Real.sin ((n : ℝ) * Real.pi * (a + 2 * l) / l) =
        Real.sin ((n : ℝ) * Real.pi * a / l) := by
    rw [hend]
    exact Real.sin_add_nat_mul_two_pi _ n
  have hcosend :
      Real.cos ((n : ℝ) * Real.pi * (a + 2 * l) / l) =
        Real.cos ((n : ℝ) * Real.pi * a / l) := by
    rw [hend]
    exact Real.cos_add_nat_mul_two_pi _ n
  have hcosInt :
      (∫ x in a..a + 2 * l,
        Real.cos ((n : ℝ) * Real.pi * x / l)) = 0 := by
    rw [show (∫ x in a..a + 2 * l,
        Real.cos ((n : ℝ) * Real.pi * x / l)) =
          cosAntiderivative q (a + 2 * l) -
            cosAntiderivative q a by
      simpa only [harg] using
        integral_cos_linear_eq_sub q hq0 a (a + 2 * l)]
    simp only [cosAntiderivative]
    rw [harg, harg, hsinend]
    ring
  unfold sineParts
  rw [hcosInt, hcosend]
  ring

theorem gap11 (a l : ℝ) (s : ℕ → ℝ) (hl : 0 < l)
    (hs : ∀ n : ℕ, 1 ≤ n → s n = sineIntegral a l n) :
    ∀ n : ℕ, 1 ≤ n →
      s n =
        -(2 * l / ((n : ℝ) * Real.pi)) *
          Real.cos ((n : ℝ) * Real.pi * a / l) := by
  intro n hn
  rw [hs n hn, gap9 a l hl n hn, gap10 a l hl n hn]

theorem gap12 (a l : ℝ) (f : ℝ → ℝ) (hl : 0 < l)
    (hf : ∀ x, f x = x) :
    ∀ x, a < x → x < a + 2 * l →
      f x = fourierSeries a l x := by
  intro x hx₀ hx₁
  rw [hf x]
  exact (fourierSeries_eq_self a l x hl hx₀ hx₁).symm

theorem gap13 (a l x : ℝ) (hl : 0 < l)
    (hx₀ : a < x) (hx₁ : x < a + 2 * l) :
    fourierSeries a l x = x := by
  exact fourierSeries_eq_self a l x hl hx₀ hx₁

theorem gap14 (f : ℝ → ℝ) (hf : ∀ x, f x = x) :
    ∀ x, f x = x := by
  exact hf

end

end ProofGap.Exercise2949
