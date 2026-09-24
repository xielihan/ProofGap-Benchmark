import ProofGapLean.Prelude.Sequences
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Analysis.Complex.AbelLimit
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Data.Real.Sign
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Algebra.InfiniteSum.Basic

namespace ProofGap.Exercise2952

noncomputable section

open Filter
open scoped Interval
open scoped Topology

def squareWave (x : ℝ) : ℝ :=
  Real.sign (Real.cos x)

def cosineIntegral (n : ℕ) : ℝ :=
  2 / Real.pi *
    ∫ x in 0..Real.pi,
      squareWave x * Real.cos ((n : ℝ) * x)

def splitCosineIntegral (n : ℕ) : ℝ :=
  2 / Real.pi *
    ((∫ x in 0..Real.pi / 2, Real.cos ((n : ℝ) * x)) -
      ∫ x in Real.pi / 2..Real.pi, Real.cos ((n : ℝ) * x))

def squareWaveSeries (x : ℝ) : ℝ :=
  4 / Real.pi *
    ∑'[SummationFilter.conditional ℕ] k : ℕ,
      (-1 : ℝ) ^ k *
        (Real.cos (((2 * k + 1 : ℕ) : ℝ) * x) /
          ((2 * k + 1 : ℕ) : ℝ))

def HasMidpointValue (f : ℝ → ℝ) (x : ℝ) : Prop :=
  ∃ left right : ℝ,
    Tendsto f (nhdsWithin x (Set.Iio x)) (nhds left) ∧
      Tendsto f (nhdsWithin x (Set.Ioi x)) (nhds right) ∧
      f x = (left + right) / 2

private theorem squareWave_eq_one_of_mem
    {x : ℝ} (hx0 : 0 < x) (hx1 : x < Real.pi / 2) :
    squareWave x = 1 := by
  unfold squareWave
  exact Real.sign_of_pos (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hx1⟩)

private theorem squareWave_eq_neg_one_of_mem
    {x : ℝ} (hx0 : Real.pi / 2 < x) (hx1 : x ≤ Real.pi) :
    squareWave x = -1 := by
  unfold squareWave
  exact Real.sign_of_neg
    (Real.cos_neg_of_pi_div_two_lt_of_lt hx0 (by linarith [Real.pi_pos]))

private theorem squareWave_eq_one_ae :
    (fun x : ℝ => squareWave x) =ᵐ[
      MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) (Real.pi / 2))]
      (fun _ => (1 : ℝ)) := by
  rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff'
    measurableSet_uIoc]
  filter_upwards [MeasureTheory.Measure.ae_ne MeasureTheory.volume
    (Real.pi / 2)] with x hxne hxmem
  rw [Set.uIoc_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 2)] at hxmem
  exact squareWave_eq_one_of_mem hxmem.1 (lt_of_le_of_ne hxmem.2 hxne)

private theorem squareWave_eq_neg_one_ae :
    (fun x : ℝ => squareWave x) =ᵐ[
      MeasureTheory.volume.restrict (Set.uIoc (Real.pi / 2) Real.pi)]
      (fun _ => (-1 : ℝ)) := by
  rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff'
    measurableSet_uIoc]
  filter_upwards with x hxmem
  rw [Set.uIoc_of_le (by linarith [Real.pi_pos] : Real.pi / 2 ≤ Real.pi)] at hxmem
  exact squareWave_eq_neg_one_of_mem hxmem.1 hxmem.2

private theorem integral_cos_nat_mul (n : ℕ) (hn : 1 ≤ n)
    (u v : ℝ) :
    (∫ x in u..v, Real.cos ((n : ℝ) * x)) =
      Real.sin ((n : ℝ) * v) / (n : ℝ) -
        Real.sin ((n : ℝ) * u) / (n : ℝ) := by
  have hn0 : (n : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x hx
    have hinner : HasDerivAt (fun y : ℝ => (n : ℝ) * y) (n : ℝ) x := by
      simpa only [id_eq, mul_one] using (hasDerivAt_id x).const_mul (n : ℝ)
    convert ((Real.hasDerivAt_sin ((n : ℝ) * x)).comp x hinner).div_const
      (n : ℝ) using 1
    field_simp [hn0]
  · exact (Real.continuous_cos.comp
      (continuous_const.mul continuous_id)).intervalIntegrable u v

private theorem seriesHasSum_squareWaveCore (x : ℝ) :
    ProofGap.SeriesHasSum
      (fun k : ℕ =>
        (-1 : ℝ) ^ k *
          (Real.cos (((2 * k + 1 : ℕ) : ℝ) * x) /
            ((2 * k + 1 : ℕ) : ℝ)))
      (Real.pi / 4 * Real.sign (Real.cos x)) := by
  by_cases hc : Real.cos x = 0
  · obtain ⟨j, hx⟩ := Real.cos_eq_zero_iff.mp hc
    have hodd (k : ℕ) :
        Real.cos (((2 * k + 1 : ℕ) : ℝ) * x) = 0 := by
      apply Real.cos_eq_zero_iff.mpr
      refine ⟨(2 * (k : ℤ) + 1) * j + k, ?_⟩
      rw [hx]
      push_cast
      ring
    unfold ProofGap.SeriesHasSum
    convert (hasSum_zero (α := ℝ)
      (L := SummationFilter.conditional ℕ)) using 1
    · ext k
      rw [hodd k, zero_div, mul_zero]
    · simp [hc]
  · let e : ℂ := Complex.exp ((x : ℂ) * Complex.I)
    let q : ℂ := -(e ^ 2)
    have heNorm : ‖e‖ = 1 := by
      simpa [e] using Complex.norm_exp_ofReal_mul_I x
    have hePowRe (n : ℕ) :
        (e ^ n).re = Real.cos ((n : ℝ) * x) := by
      dsimp [e]
      rw [← Complex.exp_nat_mul]
      convert Complex.exp_ofReal_mul_I_re ((n : ℝ) * x) using 2 <;>
        push_cast <;> ring
    have hqNorm : ‖q‖ = 1 := by
      dsimp [q]
      rw [norm_neg, norm_pow, heNorm, one_pow]
    have hqNe : q ≠ 1 := by
      intro hq
      have hre := congrArg Complex.re hq
      dsimp [q] at hre
      change -(e ^ 2).re = 1 at hre
      rw [hePowRe 2] at hre
      norm_num at hre
      rw [Real.cos_two_mul] at hre
      apply hc
      nlinarith
    have hOsc (k : ℕ) :
        (e * q ^ k).re =
          (-1 : ℝ) ^ k *
            Real.cos (((2 * k + 1 : ℕ) : ℝ) * x) := by
      have heq :
          e * q ^ k = ((-1 : ℝ) ^ k : ℝ) * e ^ (2 * k + 1) := by
        dsimp [q]
        calc
          e * (-(e ^ 2)) ^ k =
              e * ((-1 : ℂ) ^ k * e ^ (2 * k)) := by
                rw [neg_eq_neg_one_mul, mul_pow, ← pow_mul]
          _ = ((-1 : ℂ) ^ k) * e ^ (2 * k + 1) := by
                rw [pow_succ']
                ring
          _ = ((-1 : ℝ) ^ k : ℝ) * e ^ (2 * k + 1) := by
                norm_cast
      rw [heq, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero, hePowRe]
    have hBound (n : ℕ) :
        ‖∑ i ∈ Finset.range n,
          (-1 : ℝ) ^ i *
            Real.cos (((2 * i + 1 : ℕ) : ℝ) * x)‖ ≤
          2 / ‖q - 1‖ := by
      let S : ℂ := ∑ i ∈ Finset.range n, e * q ^ i
      have hSre :
          S.re = ∑ i ∈ Finset.range n,
            (-1 : ℝ) ^ i *
              Real.cos (((2 * i + 1 : ℕ) : ℝ) * x) := by
        dsimp [S]
        rw [Complex.re_sum]
        exact Finset.sum_congr rfl fun i _ => hOsc i
      have hS : S = e * ((q ^ n - 1) / (q - 1)) := by
        calc
          S = e * ∑ i ∈ Finset.range n, q ^ i := by
            dsimp [S]
            rw [Finset.mul_sum]
          _ = e * ((q ^ n - 1) / (q - 1)) := by
            rw [geom_sum_eq hqNe]
      calc
        ‖∑ i ∈ Finset.range n,
            (-1 : ℝ) ^ i *
              Real.cos (((2 * i + 1 : ℕ) : ℝ) * x)‖ =
            ‖S.re‖ := by rw [hSre]
        _ ≤ ‖S‖ := by
          simpa [Real.norm_eq_abs] using Complex.abs_re_le_norm S
        _ = ‖q ^ n - 1‖ / ‖q - 1‖ := by
          rw [hS, norm_mul, norm_div, heNorm, one_mul]
        _ ≤ (‖q ^ n‖ + ‖(1 : ℂ)‖) / ‖q - 1‖ := by
          exact div_le_div_of_nonneg_right (norm_sub_le _ _) (norm_nonneg _)
        _ = 2 / ‖q - 1‖ := by norm_num [norm_pow, hqNorm]
    have hAnti :
        Antitone (fun n : ℕ => (1 : ℝ) / ((2 * n + 1 : ℕ) : ℝ)) := by
      intro m n hmn
      exact one_div_le_one_div_of_le (by positivity) (by
        exact_mod_cast Nat.add_le_add_right (Nat.mul_le_mul_left 2 hmn) 1)
    have hZero :
        Tendsto (fun n : ℕ => (1 : ℝ) / ((2 * n + 1 : ℕ) : ℝ))
          atTop (𝓝 0) := by
      have hden :
          Tendsto (fun n : ℕ => 2 * (n : ℝ) + 1)
            atTop atTop := by
        apply tendsto_atTop_add_const_right
        simpa [mul_comm] using
          tendsto_natCast_atTop_atTop.const_mul_atTop
            (show (0 : ℝ) < 2 by norm_num)
      simpa only [one_div, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
        Nat.cast_one] using hden.inv_tendsto_atTop
    obtain ⟨v, hv⟩ :
        ∃ v : ℝ,
          Tendsto
            (fun n => ∑ i ∈ Finset.range n,
              (-1 : ℝ) ^ i *
                (Real.cos (((2 * i + 1 : ℕ) : ℝ) * x) /
                  ((2 * i + 1 : ℕ) : ℝ)))
            atTop (𝓝 v) := by
      have hCauchy :=
        hAnti.cauchySeq_series_mul_of_tendsto_zero_of_bounded hZero hBound
      obtain ⟨v, hv⟩ := cauchySeq_tendsto_of_complete hCauchy
      refine ⟨v, ?_⟩
      simpa [smul_eq_mul, div_eq_mul_inv, mul_assoc, mul_left_comm,
        mul_comm] using hv
    have hsinSq := Real.sin_sq_add_cos_sq x
    have hcSq : 0 < Real.cos x ^ 2 := sq_pos_of_ne_zero hc
    have hdenPos : 0 < 1 + Real.sin x := by
      nlinarith [Real.neg_one_le_sin x]
    have heForm :
        e = (Real.cos x : ℝ) + (Real.sin x : ℝ) * Complex.I := by
      simpa [e] using Complex.exp_ofReal_mul_I x
    have heRe : e.re = Real.cos x := by
      simpa using hePowRe 1
    have hdenNe : (1 : ℂ) - e * Complex.I ≠ 0 := by
      intro h
      have him := congrArg Complex.im h
      simp only [Complex.sub_im, Complex.one_im, Complex.mul_im,
        Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero,
        zero_sub, heRe, Complex.zero_im] at him
      exact hc (neg_eq_zero.mp him)
    let R : ℂ := ((1 : ℂ) + e * Complex.I) / (1 - e * Complex.I)
    let ρ : ℝ := Real.cos x / (1 + Real.sin x)
    have hRatio : R = (ρ : ℂ) * Complex.I := by
      dsimp [R]
      rw [div_eq_iff hdenNe, heForm]
      apply Complex.ext
      · dsimp [ρ]
        norm_num [Complex.mul_re, Complex.mul_im]
        field_simp [ne_of_gt hdenPos]
        nlinarith
      · dsimp [ρ]
        norm_num [Complex.mul_re, Complex.mul_im]
        field_simp [ne_of_gt hdenPos]
    have hRSlit : R ∈ Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff]
      right
      rw [hRatio]
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, zero_mul, mul_one, zero_add]
      dsimp [ρ]
      simpa only [add_zero] using div_ne_zero hc (ne_of_gt hdenPos)
    have hArcCont : ContinuousAt Complex.arctan e := by
      have hzi : ContinuousAt (fun z : ℂ => z * Complex.I) e :=
        continuousAt_id.mul continuousAt_const
      have hrat :
          ContinuousAt
            (fun z : ℂ => ((1 : ℂ) + z * Complex.I) /
              (1 - z * Complex.I)) e :=
        (continuousAt_const.add hzi).div
          (continuousAt_const.sub hzi) hdenNe
      have hlog := hrat.clog (by simpa [R] using hRSlit)
      unfold Complex.arctan
      exact continuousAt_const.mul hlog
    have hArcRe :
        (Complex.arctan e).re =
          Real.pi / 4 * Real.sign (Real.cos x) := by
      rcases lt_or_gt_of_ne hc with hcNeg | hcPos
      · have hρNeg : ρ < 0 := div_neg_of_neg_of_pos hcNeg hdenPos
        have hArg : Complex.arg R = -(Real.pi / 2) := by
          apply Complex.arg_eq_neg_pi_div_two_iff.mpr
          rw [hRatio]
          simp [hρNeg]
        calc
          (Complex.arctan e).re = (Complex.log R).im / 2 := by
            unfold Complex.arctan
            dsimp [R]
            simp [Complex.mul_re, Complex.div_re]
            ring
          _ = Complex.arg R / 2 := by rw [Complex.log_im]
          _ = Real.pi / 4 * Real.sign (Real.cos x) := by
            rw [hArg, Real.sign_of_neg hcNeg]
            ring
      · have hρPos : 0 < ρ := div_pos hcPos hdenPos
        have hArg : Complex.arg R = Real.pi / 2 := by
          apply Complex.arg_eq_pi_div_two_iff.mpr
          rw [hRatio]
          simp [hρPos]
        calc
          (Complex.arctan e).re = (Complex.log R).im / 2 := by
            unfold Complex.arctan
            dsimp [R]
            simp [Complex.mul_re, Complex.div_re]
            ring
          _ = Complex.arg R / 2 := by rw [Complex.log_im]
          _ = Real.pi / 4 * Real.sign (Real.cos x) := by
            rw [hArg, Real.sign_of_pos hcPos]
            ring
    let a : ℕ → ℝ := fun k =>
      (-1 : ℝ) ^ k *
        (Real.cos (((2 * k + 1 : ℕ) : ℝ) * x) /
          ((2 * k + 1 : ℕ) : ℝ))
    have hv' : Tendsto (fun n => ∑ i ∈ Finset.range n, a i)
        atTop (𝓝 v) := by simpa [a] using hv
    have hAbel := Real.tendsto_tsum_powerSeries_nhdsWithin_lt hv'
    have hm : 𝓝[<] (1 : ℝ) ≤ 𝓝 1 :=
      tendsto_nhdsWithin_of_tendsto_nhds fun _ h => h
    have hsq : Tendsto (fun y : ℝ => y ^ 2) (𝓝[<] 1) (𝓝[<] 1) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · nth_rw 3 [← one_pow 2]
        exact Tendsto.pow ‹_› 2
      · rw [eventually_iff_exists_mem]
        refine ⟨Set.Ioo (-1) 1, Ioo_mem_nhdsLT (by norm_num), ?_⟩
        intro y hy
        rw [Set.mem_Iio, sq_lt_one_iff_abs_lt_one, abs_lt]
        exact hy
    have hRadial := (hAbel.comp hsq).mul hm
    rw [mul_one] at hRadial
    have hEq :
        (fun y : ℝ => (∑' k : ℕ, a k * (y ^ 2) ^ k) * y) =ᶠ[
          𝓝[<] (1 : ℝ)]
          (fun y : ℝ => (Complex.arctan ((y : ℂ) * e)).re) := by
      change ∀ᶠ y : ℝ in 𝓝[<] (1 : ℝ),
        (∑' k : ℕ, a k * (y ^ 2) ^ k) * y =
          (Complex.arctan ((y : ℂ) * e)).re
      rw [eventually_iff_exists_mem]
      refine ⟨Set.Ioo 0 1, Ioo_mem_nhdsLT (by norm_num), ?_⟩
      intro y hy
      have hz : ‖(y : ℂ) * e‖ < 1 := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hy.1, heNorm, mul_one]
        exact hy.2
      have har := Complex.hasSum_re (Complex.hasSum_arctan hz)
      rw [← har.tsum_eq, ← tsum_mul_right]
      apply tsum_congr
      intro k
      have hpowRe (n : ℕ) :
          (((y : ℂ) * e) ^ n).re =
            y ^ n * Real.cos ((n : ℝ) * x) := by
        rw [mul_pow, show (y : ℂ) ^ n = ((y ^ n : ℝ) : ℂ) by
          norm_cast, Complex.mul_re, Complex.ofReal_re,
          Complex.ofReal_im, zero_mul, sub_zero, hePowRe]
      have hsign :
          ((-1 : ℂ) ^ k) = (((-1 : ℝ) ^ k : ℝ) : ℂ) := by
        norm_cast
      rw [hsign]
      rw [Complex.div_re]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, add_zero, hpowRe, Complex.natCast_re,
        Complex.natCast_im, mul_zero, sub_zero, Complex.normSq_natCast]
      dsimp [a]
      push_cast
      field_simp
      ring
    have hArcLimit :
        Tendsto (fun y : ℝ => (Complex.arctan ((y : ℂ) * e)).re)
          (𝓝[<] (1 : ℝ))
          (𝓝 (Real.pi / 4 * Real.sign (Real.cos x))) := by
      have hp : ContinuousAt (fun y : ℝ => (y : ℂ) * e) 1 := by
        fun_prop
      have hpT :
          Tendsto (fun y : ℝ => (y : ℂ) * e) (𝓝 1) (𝓝 e) := by
        simpa using hp.tendsto
      have hArcT :
          Tendsto (fun y : ℝ => Complex.arctan ((y : ℂ) * e))
            (𝓝 1) (𝓝 (Complex.arctan e)) :=
        hArcCont.tendsto.comp hpT
      have hReT :
          Tendsto (fun y : ℝ => (Complex.arctan ((y : ℂ) * e)).re)
            (𝓝 1) (𝓝 (Complex.arctan e).re) :=
        (Complex.continuous_re.tendsto _).comp hArcT
      convert hReT.mono_left hm using 1
      simpa using hArcRe.symm
    have hRadial' :
        Tendsto (fun y : ℝ => (Complex.arctan ((y : ℂ) * e)).re)
          (𝓝[<] (1 : ℝ)) (𝓝 v) :=
      hRadial.congr' hEq
    have hvValue : v = Real.pi / 4 * Real.sign (Real.cos x) :=
      tendsto_nhds_unique hRadial' hArcLimit
    rw [ProofGap.SeriesHasSum, HasSum,
      SummationFilter.conditional_filter_eq_map_range]
    simpa [Function.comp_def, hvValue] using hv

private theorem squareWaveSeries_eq_squareWave (x : ℝ) :
    squareWaveSeries x = squareWave x := by
  unfold squareWaveSeries squareWave
  rw [(seriesHasSum_squareWaveCore x).tsum_eq]
  field_simp [Real.pi_ne_zero]

theorem gap1 (f : ℝ → ℝ) (hf : ∀ x, f x = squareWave x) :
    ∀ x, f (x + 2 * Real.pi) =
      Real.sign (Real.cos (x + 2 * Real.pi)) := by
  intro x
  rw [hf]
  rfl

theorem gap2 :
    ∀ x, Real.sign (Real.cos (x + 2 * Real.pi)) =
      Real.sign (Real.cos x) := by
  intro x
  rw [Real.cos_add_two_pi]

theorem gap3 (f : ℝ → ℝ) (hf : ∀ x, f x = squareWave x) :
    ∀ x, Real.sign (Real.cos x) = f x := by
  intro x
  rw [hf]
  rfl

theorem gap4 (f : ℝ → ℝ) (hf : ∀ x, f x = squareWave x) :
    ∀ x, f (x + 2 * Real.pi) = f x := by
  intro x
  rw [gap1 f hf x, gap2 x, gap3 f hf x]

theorem gap5 (f : ℝ → ℝ) (hf : ∀ x, f x = squareWave x) :
    Function.Periodic f (2 * Real.pi) := by
  exact gap4 f hf

theorem gap6 (f : ℝ → ℝ) (hf : ∀ x, f x = squareWave x) :
    Function.Even f := by
  intro x
  rw [hf, hf]
  simp [squareWave]

theorem gap7 (s : ℕ → ℝ)
    (hs : ∀ n : ℕ, 1 ≤ n → s n = 0) :
    ∀ n : ℕ, 1 ≤ n → s n = 0 := by
  exact hs

theorem gap8 (c : ℕ → ℝ)
    (hc : c 0 =
      2 / Real.pi * ∫ x in 0..Real.pi, squareWave x) :
    c 0 = 2 / Real.pi * ∫ x in 0..Real.pi, squareWave x := by
  exact hc

theorem gap9 :
    2 / Real.pi * (∫ x in 0..Real.pi, squareWave x) =
      2 / Real.pi *
        ((∫ _x in 0..Real.pi / 2, (1 : ℝ)) +
          ∫ _x in Real.pi / 2..Real.pi, (-1 : ℝ)) := by
  have hleftConst : IntervalIntegrable (fun _ : ℝ => (1 : ℝ))
      MeasureTheory.volume 0 (Real.pi / 2) :=
    continuous_const.intervalIntegrable _ _
  have hrightConst : IntervalIntegrable (fun _ : ℝ => (-1 : ℝ))
      MeasureTheory.volume (Real.pi / 2) Real.pi :=
    continuous_const.intervalIntegrable _ _
  have hleft : IntervalIntegrable squareWave MeasureTheory.volume
      0 (Real.pi / 2) :=
    hleftConst.congr_ae squareWave_eq_one_ae.symm
  have hright : IntervalIntegrable squareWave MeasureTheory.volume
      (Real.pi / 2) Real.pi :=
    hrightConst.congr_ae squareWave_eq_neg_one_ae.symm
  have hleftEq :
      (∫ x in (0 : ℝ)..Real.pi / 2, squareWave x) =
        ∫ _x in (0 : ℝ)..Real.pi / 2, (1 : ℝ) :=
    intervalIntegral.integral_congr_ae_restrict squareWave_eq_one_ae
  have hrightEq :
      (∫ x in Real.pi / 2..Real.pi, squareWave x) =
        ∫ _x in Real.pi / 2..Real.pi, (-1 : ℝ) :=
    intervalIntegral.integral_congr_ae_restrict squareWave_eq_neg_one_ae
  rw [← intervalIntegral.integral_add_adjacent_intervals hleft hright,
    hleftEq, hrightEq]

theorem gap10 :
    2 / Real.pi *
        ((∫ _x in 0..Real.pi / 2, (1 : ℝ)) +
          ∫ _x in Real.pi / 2..Real.pi, (-1 : ℝ)) =
      0 := by
  simp
  ring

theorem gap11 (c : ℕ → ℝ)
    (hc : c 0 =
      2 / Real.pi * ∫ x in 0..Real.pi, squareWave x) :
    c 0 = 0 := by
  rw [hc, gap9, gap10]

theorem gap12 (c : ℕ → ℝ)
    (hc : ∀ n : ℕ, 1 ≤ n → c n = cosineIntegral n) :
    ∀ n : ℕ, 1 ≤ n → c n = cosineIntegral n := by
  exact hc

theorem gap13 :
    ∀ n : ℕ, 1 ≤ n →
      cosineIntegral n = splitCosineIntegral n := by
  intro n hn
  let g : ℝ → ℝ := fun x => squareWave x * Real.cos ((n : ℝ) * x)
  have hcosLeft : IntervalIntegrable
      (fun x : ℝ => Real.cos ((n : ℝ) * x)) MeasureTheory.volume
      0 (Real.pi / 2) :=
    (Real.continuous_cos.comp
      (continuous_const.mul continuous_id)).intervalIntegrable _ _
  have hcosRight : IntervalIntegrable
      (fun x : ℝ => -Real.cos ((n : ℝ) * x)) MeasureTheory.volume
      (Real.pi / 2) Real.pi :=
    ((Real.continuous_cos.comp
      (continuous_const.mul continuous_id)).neg).intervalIntegrable _ _
  have hgLeftAE : g =ᵐ[
      MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) (Real.pi / 2))]
      (fun x => Real.cos ((n : ℝ) * x)) := by
    filter_upwards [squareWave_eq_one_ae] with x hx
    dsimp [g]
    rw [hx, one_mul]
  have hgRightAE : g =ᵐ[
      MeasureTheory.volume.restrict (Set.uIoc (Real.pi / 2) Real.pi)]
      (fun x => -Real.cos ((n : ℝ) * x)) := by
    filter_upwards [squareWave_eq_neg_one_ae] with x hx
    dsimp [g]
    rw [hx, neg_one_mul]
  have hgLeft : IntervalIntegrable g MeasureTheory.volume
      0 (Real.pi / 2) := hcosLeft.congr_ae hgLeftAE.symm
  have hgRight : IntervalIntegrable g MeasureTheory.volume
      (Real.pi / 2) Real.pi := hcosRight.congr_ae hgRightAE.symm
  have hleftEq :
      (∫ x in (0 : ℝ)..Real.pi / 2, g x) =
        ∫ x in (0 : ℝ)..Real.pi / 2, Real.cos ((n : ℝ) * x) :=
    intervalIntegral.integral_congr_ae_restrict hgLeftAE
  have hrightEq :
      (∫ x in Real.pi / 2..Real.pi, g x) =
        ∫ x in Real.pi / 2..Real.pi, -Real.cos ((n : ℝ) * x) :=
    intervalIntegral.integral_congr_ae_restrict hgRightAE
  unfold cosineIntegral splitCosineIntegral
  change 2 / Real.pi * (∫ x in (0 : ℝ)..Real.pi, g x) = _
  rw [← intervalIntegral.integral_add_adjacent_intervals hgLeft hgRight,
    hleftEq, hrightEq, intervalIntegral.integral_neg]
  simp only [sub_eq_add_neg]

theorem gap14 (c : ℕ → ℝ)
    (hc : ∀ n : ℕ, 1 ≤ n → c n = cosineIntegral n) :
    ∀ n : ℕ, 1 ≤ n → c n = splitCosineIntegral n := by
  intro n hn
  rw [hc n hn, gap13 n hn]

theorem gap15 (c : ℕ → ℝ)
    (hc : ∀ n : ℕ, 1 ≤ n → c n = splitCosineIntegral n) :
    ∀ n : ℕ, 1 ≤ n →
      c n =
        2 / Real.pi *
          (1 / (n : ℝ) * Real.sin ((n : ℝ) * Real.pi / 2) +
            1 / (n : ℝ) * Real.sin ((n : ℝ) * Real.pi / 2)) := by
  intro n hn
  rw [hc n hn]
  unfold splitCosineIntegral
  rw [integral_cos_nat_mul n hn 0 (Real.pi / 2),
    integral_cos_nat_mul n hn (Real.pi / 2) Real.pi]
  simp only [mul_zero, Real.sin_zero, zero_div, Real.sin_nat_mul_pi]
  ring

theorem gap16 :
    ∀ n : ℕ, 1 ≤ n →
      2 / Real.pi *
          (1 / (n : ℝ) * Real.sin ((n : ℝ) * Real.pi / 2) +
            1 / (n : ℝ) * Real.sin ((n : ℝ) * Real.pi / 2)) =
        4 / ((n : ℝ) * Real.pi) *
          Real.sin ((n : ℝ) * Real.pi / 2) := by
  intro n hn
  have hn0 : (n : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  field_simp [hn0, Real.pi_ne_zero]
  ring

theorem gap17 (c : ℕ → ℝ)
    (hc : ∀ n : ℕ, 1 ≤ n → c n = cosineIntegral n) :
    ∀ n : ℕ, 1 ≤ n →
      c n =
        4 / ((n : ℝ) * Real.pi) *
          Real.sin ((n : ℝ) * Real.pi / 2) := by
  intro n hn
  calc
    c n = splitCosineIntegral n := gap14 c hc n hn
    _ = 2 / Real.pi *
          (1 / (n : ℝ) * Real.sin ((n : ℝ) * Real.pi / 2) +
            1 / (n : ℝ) * Real.sin ((n : ℝ) * Real.pi / 2)) :=
      gap15 (fun m => splitCosineIntegral m) (fun m hm => rfl) n hn
    _ = 4 / ((n : ℝ) * Real.pi) *
          Real.sin ((n : ℝ) * Real.pi / 2) := gap16 n hn

theorem gap18 (c : ℕ → ℝ)
    (hc : ∀ n : ℕ, 1 ≤ n →
      c n =
        4 / ((n : ℝ) * Real.pi) *
          Real.sin ((n : ℝ) * Real.pi / 2)) :
    (∀ k : ℕ, 1 ≤ k → c (2 * k) = 0) ∧
      (∀ k : ℕ,
        c (2 * k + 1) =
          (-1 : ℝ) ^ k *
            (4 / (((2 * k + 1 : ℕ) : ℝ) * Real.pi))) := by
  constructor
  · intro k hk
    rw [hc (2 * k) (by omega)]
    have harg : ((2 * k : ℕ) : ℝ) * Real.pi / 2 =
        (k : ℝ) * Real.pi := by
      push_cast
      ring
    rw [harg, Real.sin_nat_mul_pi, mul_zero]
  · intro k
    rw [hc (2 * k + 1) (by omega)]
    have harg : (((2 * k + 1 : ℕ) : ℝ) * Real.pi / 2) =
        (k : ℝ) * Real.pi + Real.pi / 2 := by
      push_cast
      ring
    rw [harg, Real.sin_add, Real.sin_nat_mul_pi,
      Real.cos_nat_mul_pi, Real.sin_pi_div_two, Real.cos_pi_div_two]
    ring

theorem gap19 (f : ℝ → ℝ) (hf : ∀ x, f x = squareWave x) :
    ∀ x, -Real.pi < x → x < Real.pi →
      f x = squareWaveSeries x := by
  intro x _ _
  rw [hf x, squareWaveSeries_eq_squareWave x]

theorem gap20 :
    ∀ x, squareWaveSeries x = squareWave x := by
  exact squareWaveSeries_eq_squareWave

theorem gap21 (f : ℝ → ℝ) (hf : ∀ x, f x = squareWave x) :
    ∀ x, f x = squareWave x := by
  exact hf

theorem gap22 (f : ℝ → ℝ) (hf : ∀ x, f x = squareWave x) :
    ∀ x, Real.cos x = 0 → HasMidpointValue f x := by
  intro x hx
  rcases Real.cos_eq_zero_iff_sin_eq.mp hx with hs | hs
  · refine ⟨1, -1, ?_, ?_, ?_⟩
    · refine (tendsto_const_nhds :
        Tendsto (fun _ : ℝ => (1 : ℝ))
          (nhdsWithin x (Set.Iio x)) (nhds 1)).congr' ?_
      filter_upwards [
        mem_nhdsWithin_of_mem_nhds
          (Ioi_mem_nhds (sub_lt_self x Real.pi_pos)),
        self_mem_nhdsWithin] with y hyclose hyleft
      have hyclose' : x - Real.pi < y := hyclose
      have hdeltaNeg : y - x < 0 := sub_neg.mpr hyleft
      have hdeltaLower : -Real.pi < y - x := by linarith
      have hsinNeg : Real.sin (y - x) < 0 :=
        Real.sin_neg_of_neg_of_neg_pi_lt hdeltaNeg hdeltaLower
      have hcos : Real.cos y = -Real.sin (y - x) := by
        calc
          Real.cos y = Real.cos (x + (y - x)) := by ring_nf
          _ = Real.cos x * Real.cos (y - x) -
              Real.sin x * Real.sin (y - x) := Real.cos_add _ _
          _ = -Real.sin (y - x) := by rw [hx, hs]; ring
      symm
      rw [hf, squareWave, Real.sign_of_pos (hcos.symm ▸ neg_pos.mpr hsinNeg)]
    · refine (tendsto_const_nhds :
        Tendsto (fun _ : ℝ => (-1 : ℝ))
          (nhdsWithin x (Set.Ioi x)) (nhds (-1))).congr' ?_
      filter_upwards [
        mem_nhdsWithin_of_mem_nhds
          (Iio_mem_nhds (lt_add_of_pos_right x Real.pi_pos)),
        self_mem_nhdsWithin] with y hyclose hyright
      have hyclose' : y < x + Real.pi := hyclose
      have hdeltaPos : 0 < y - x := sub_pos.mpr hyright
      have hdeltaUpper : y - x < Real.pi := by linarith
      have hsinPos : 0 < Real.sin (y - x) :=
        Real.sin_pos_of_pos_of_lt_pi hdeltaPos hdeltaUpper
      have hcos : Real.cos y = -Real.sin (y - x) := by
        calc
          Real.cos y = Real.cos (x + (y - x)) := by ring_nf
          _ = Real.cos x * Real.cos (y - x) -
              Real.sin x * Real.sin (y - x) := Real.cos_add _ _
          _ = -Real.sin (y - x) := by rw [hx, hs]; ring
      symm
      rw [hf, squareWave, Real.sign_of_neg (hcos.symm ▸ neg_neg_of_pos hsinPos)]
    · rw [hf, squareWave, hx, Real.sign_zero]
      norm_num
  · refine ⟨-1, 1, ?_, ?_, ?_⟩
    · refine (tendsto_const_nhds :
        Tendsto (fun _ : ℝ => (-1 : ℝ))
          (nhdsWithin x (Set.Iio x)) (nhds (-1))).congr' ?_
      filter_upwards [
        mem_nhdsWithin_of_mem_nhds
          (Ioi_mem_nhds (sub_lt_self x Real.pi_pos)),
        self_mem_nhdsWithin] with y hyclose hyleft
      have hyclose' : x - Real.pi < y := hyclose
      have hdeltaNeg : y - x < 0 := sub_neg.mpr hyleft
      have hdeltaLower : -Real.pi < y - x := by linarith
      have hsinNeg : Real.sin (y - x) < 0 :=
        Real.sin_neg_of_neg_of_neg_pi_lt hdeltaNeg hdeltaLower
      have hcos : Real.cos y = Real.sin (y - x) := by
        calc
          Real.cos y = Real.cos (x + (y - x)) := by ring_nf
          _ = Real.cos x * Real.cos (y - x) -
              Real.sin x * Real.sin (y - x) := Real.cos_add _ _
          _ = Real.sin (y - x) := by rw [hx, hs]; ring
      symm
      rw [hf, squareWave, Real.sign_of_neg (hcos.symm ▸ hsinNeg)]
    · refine (tendsto_const_nhds :
        Tendsto (fun _ : ℝ => (1 : ℝ))
          (nhdsWithin x (Set.Ioi x)) (nhds 1)).congr' ?_
      filter_upwards [
        mem_nhdsWithin_of_mem_nhds
          (Iio_mem_nhds (lt_add_of_pos_right x Real.pi_pos)),
        self_mem_nhdsWithin] with y hyclose hyright
      have hyclose' : y < x + Real.pi := hyclose
      have hdeltaPos : 0 < y - x := sub_pos.mpr hyright
      have hdeltaUpper : y - x < Real.pi := by linarith
      have hsinPos : 0 < Real.sin (y - x) :=
        Real.sin_pos_of_pos_of_lt_pi hdeltaPos hdeltaUpper
      have hcos : Real.cos y = Real.sin (y - x) := by
        calc
          Real.cos y = Real.cos (x + (y - x)) := by ring_nf
          _ = Real.cos x * Real.cos (y - x) -
              Real.sin x * Real.sin (y - x) := Real.cos_add _ _
          _ = Real.sin (y - x) := by rw [hx, hs]; ring
      symm
      rw [hf, squareWave, Real.sign_of_pos (hcos.symm ▸ hsinPos)]
    · rw [hf, squareWave, hx, Real.sign_zero]
      norm_num

theorem gap23 (f : ℝ → ℝ) (hf : ∀ x, f x = squareWave x) :
    ∀ x, f x = squareWaveSeries x := by
  intro x
  rw [hf x, gap20 x]

end

end ProofGap.Exercise2952
