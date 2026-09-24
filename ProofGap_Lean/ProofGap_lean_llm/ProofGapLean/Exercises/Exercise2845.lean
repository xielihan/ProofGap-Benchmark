import ProofGapLean.Prelude.Analysis
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Orthogonality
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Calculus.IteratedDeriv.ConvergenceOnBall
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import ProofGapLean.Exercises.Exercise1221_2

namespace ProofGap.Exercise2845

noncomputable section

open scoped Interval

def arcsineIntegrand (t : ℝ) : ℝ :=
  1 / Real.sqrt (1 - t ^ 2)

def arcsineIntegrandTerm (t : ℝ) (n : ℕ) : ℝ :=
  (Nat.factorial (2 * n) : ℝ) /
    ((4 : ℝ) ^ n * (Nat.factorial n : ℝ) ^ 2) * t ^ (2 * n)

def arcsineTerm (x : ℝ) (n : ℕ) : ℝ :=
  (Nat.factorial (2 * n) : ℝ) /
    ((4 : ℝ) ^ n * (Nat.factorial n : ℝ) ^ 2 * (2 * n + 1)) *
      x ^ (2 * n + 1)

def sineCompositionTerm (u x : ℝ) (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n * u ^ (2 * n + 1) * Real.arcsin x ^ (2 * n + 1) /
    (Nat.factorial (2 * n + 1) : ℝ)

def sineArcsineTerm (u x : ℝ) (n : ℕ) : ℝ :=
  u *
      (∏ k ∈ Finset.range n, (((2 * k + 1 : ℕ) : ℝ) ^ 2 - u ^ 2)) /
      (Nat.factorial (2 * n + 1) : ℝ) *
    x ^ (2 * n + 1)

private theorem multichoose_succ_real (r : ℝ) (n : ℕ) :
    Ring.multichoose r (n + 1) =
      Ring.multichoose r n * (r + n) / (n + 1) := by
  have h0 := Ring.factorial_nsmul_multichoose_eq_ascPochhammer r n
  have h1 := Ring.factorial_nsmul_multichoose_eq_ascPochhammer r (n + 1)
  simp only [nsmul_eq_mul] at h0 h1
  rw [ascPochhammer_succ_right, Polynomial.smeval_mul,
    Polynomial.smeval_add, Polynomial.smeval_X,
    Polynomial.smeval_natCast] at h1
  rw [← h0] at h1
  rw [Nat.factorial_succ] at h1
  push_cast at h1
  norm_num [pow_one, pow_zero, nsmul_eq_mul] at h1
  have hn : (n + 1 : ℝ) ≠ 0 := by positivity
  have hf : (Nat.factorial n : ℝ) ≠ 0 := by positivity
  apply (eq_div_iff hn).2
  apply mul_left_cancel₀ hf
  calc
    (Nat.factorial n : ℝ) *
          (Ring.multichoose r (n + 1) * (n + 1)) =
        (n + 1) * (Nat.factorial n : ℝ) *
          Ring.multichoose r (n + 1) := by ring
    _ = (Nat.factorial n : ℝ) * Ring.multichoose r n *
          (r + n) := h1
    _ = (Nat.factorial n : ℝ) *
          (Ring.multichoose r n * (r + n)) := by ring

private theorem half_multichoose_eq (n : ℕ) :
    Ring.multichoose (1 / 2 : ℝ) n =
      (Nat.factorial (2 * n) : ℝ) /
        ((4 : ℝ) ^ n * (Nat.factorial n : ℝ) ^ 2) := by
  induction n with
  | zero =>
      norm_num [Ring.multichoose_zero_right]
  | succ n ih =>
      rw [multichoose_succ_real, ih]
      rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega,
        Nat.factorial_succ, Nat.factorial_succ, Nat.factorial_succ,
        pow_succ]
      push_cast
      field_simp
      ring

private theorem choose_half_eq (n : ℕ) :
    Ring.choose ((1 / 2 : ℝ) + n - 1) n =
      (Nat.factorial (2 * n) : ℝ) /
        ((4 : ℝ) ^ n * (Nat.factorial n : ℝ) ^ 2) := by
  rw [← Ring.multichoose_eq]
  exact half_multichoose_eq n

private def arcsineCoefficient (n : ℕ) : ℝ :=
  (Nat.factorial (2 * n) : ℝ) /
    ((4 : ℝ) ^ n * (Nat.factorial n : ℝ) ^ 2)

private theorem arcsineCoefficient_eq (n : ℕ) :
    arcsineCoefficient n = Ring.multichoose (1 / 2 : ℝ) n := by
  exact (half_multichoose_eq n).symm

private theorem arcsineCoefficient_succ (n : ℕ) :
    arcsineCoefficient (n + 1) =
      arcsineCoefficient n * ((n : ℝ) + 1 / 2) / ((n : ℝ) + 1) := by
  rw [arcsineCoefficient_eq, arcsineCoefficient_eq,
    multichoose_succ_real]
  push_cast
  ring

private theorem arcsineCoefficient_nonneg (n : ℕ) :
    0 ≤ arcsineCoefficient n := by
  induction n with
  | zero => norm_num [arcsineCoefficient]
  | succ n ih =>
      rw [arcsineCoefficient_succ]
      positivity

private theorem arcsineCoefficient_le_one (n : ℕ) :
    arcsineCoefficient n ≤ 1 := by
  induction n with
  | zero => norm_num [arcsineCoefficient]
  | succ n ih =>
      rw [arcsineCoefficient_succ]
      have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      have hfac : ((n : ℝ) + 1 / 2) / ((n : ℝ) + 1) ≤ 1 := by
        apply (div_le_one (by linarith)).2
        linarith
      calc
        arcsineCoefficient n * ((n : ℝ) + 1 / 2) / ((n : ℝ) + 1) =
            arcsineCoefficient n *
              (((n : ℝ) + 1 / 2) / ((n : ℝ) + 1)) := by ring
        _ ≤ 1 *
              (((n : ℝ) + 1 / 2) / ((n : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_right ih (by positivity)
        _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left hfac (by norm_num)
        _ = 1 := by ring

private theorem arcsineIntegrand_hasSum (t : ℝ) (ht : |t| < 1) :
    HasSum (arcsineIntegrandTerm t)
      (arcsineIntegrand t) := by
  have hzabs : |-(t ^ 2)| < 1 := by
    rw [abs_neg, abs_pow]
    nlinarith [abs_nonneg t]
  have hz : -(t ^ 2) ∈ Metric.eball (0 : ℝ) 1 := by
    simp only [Metric.mem_eball, edist_dist, dist_zero_right,
      ENNReal.ofReal_lt_one]
    simpa [Real.norm_eq_abs] using hzabs
  have h :=
    (Real.one_add_rpow_hasFPowerSeriesOnBall_zero
      (a := -(1 / 2 : ℝ))).hasSum hz
  have hfun :
      (fun n : ℕ =>
        (binomialSeries ℝ (-(1 / 2 : ℝ)) n)
          (fun _ => -(t ^ 2))) =
        arcsineIntegrandTerm t := by
    funext n
    rw [binomialSeries_apply]
    simp only [smul_eq_mul]
    rw [show (List.ofFn (fun _ : Fin n => -(t ^ 2))).prod =
        (-(t ^ 2)) ^ n by simp]
    rw [show -(t ^ 2) = (-1 : ℝ) * t ^ 2 by ring, mul_pow,
      ← pow_mul]
    rw [Ring.choose_neg']
    simp only [Units.smul_def]
    rw [Int.coe_negOnePow_natCast]
    push_cast
    rw [half_multichoose_eq]
    simp only [arcsineIntegrandTerm]
    simp only [zsmul_eq_mul]
    push_cast
    have hsign : (-1 : ℝ) ^ n * (-1 : ℝ) ^ n = 1 := by
      rw [← pow_add, ← two_mul]
      simp [pow_mul]
    calc
      ((-1 : ℝ) ^ n *
            ((Nat.factorial (2 * n) : ℝ) /
              ((4 : ℝ) ^ n * (Nat.factorial n : ℝ) ^ 2))) *
          ((-1 : ℝ) ^ n * t ^ (2 * n)) =
          ((-1 : ℝ) ^ n * (-1 : ℝ) ^ n) *
            (((Nat.factorial (2 * n) : ℝ) /
              ((4 : ℝ) ^ n * (Nat.factorial n : ℝ) ^ 2)) *
                t ^ (2 * n)) := by ring
      _ = _ := by rw [hsign]; ring
  rw [hfun] at h
  have hpos : 0 < 1 - t ^ 2 := by
    have hsq : t ^ 2 < 1 := (sq_lt_one_iff_abs_lt_one t).2 ht
    linarith
  have hvalue :
      (1 - t ^ 2) ^ (-(1 / 2 : ℝ)) =
        arcsineIntegrand t := by
    unfold arcsineIntegrand
    rw [Real.sqrt_eq_rpow, Real.rpow_neg hpos.le]
    simp [arcsineIntegrand, one_div]
  convert h using 1
  simpa [sub_eq_add_neg] using hvalue.symm

private def arcsineSeriesTerm (n : ℕ) (x : ℝ) : ℝ :=
  arcsineCoefficient n * x ^ (2 * n + 1) / (2 * n + 1 : ℕ)

private theorem arcsineSeriesTerm_eq (n : ℕ) (x : ℝ) :
    arcsineSeriesTerm n x = arcsineTerm x n := by
  unfold arcsineSeriesTerm arcsineCoefficient arcsineTerm
  field_simp
  push_cast
  ring

private def arcsineSeries (x : ℝ) : ℝ :=
  ∑' n, arcsineSeriesTerm n x

private theorem arcsineTerm_hasDerivAt (n : ℕ) (x : ℝ) :
    HasDerivAt (arcsineSeriesTerm n)
      (arcsineIntegrandTerm x n) x := by
  convert ((((hasDerivAt_id x).pow (2 * n + 1)).const_mul
    (arcsineCoefficient n)).div_const (((2 * n + 1 : ℕ) : ℝ))) using 1 <;>
    simp only [arcsineSeriesTerm, arcsineIntegrandTerm,
      arcsineCoefficient, id_eq, Nat.add_sub_cancel,
      Nat.cast_add, Nat.cast_mul] <;>
    field_simp <;>
    ring

private theorem arcsineSeries_eq_arcsin (x : ℝ) (hx : |x| < 1) :
    arcsineSeries x = Real.arcsin x := by
  let r : ℝ := (|x| + 1) / 2
  have hr0 : 0 < r := by
    dsimp [r]
    nlinarith [abs_nonneg x]
  have hxr : |x| < r := by
    dsimp [r]
    linarith
  have hr1 : r < 1 := by
    dsimp [r]
    linarith
  have hbound (n : ℕ) (y : ℝ)
      (hy : y ∈ Set.Ioo (-r) r) :
      ‖arcsineIntegrandTerm y n‖ ≤ r ^ (2 * n) := by
    change ‖arcsineCoefficient n * y ^ (2 * n)‖ ≤ _
    rw [Real.norm_eq_abs, abs_mul,
      abs_pow, abs_of_nonneg (arcsineCoefficient_nonneg n)]
    calc
      arcsineCoefficient n * |y| ^ (2 * n) ≤
          1 * |y| ^ (2 * n) := by
        gcongr
        exact arcsineCoefficient_le_one n
      _ ≤ 1 * r ^ (2 * n) := by
        gcongr
        exact (abs_lt.2 hy).le
      _ = r ^ (2 * n) := one_mul _
  have hboundSum : Summable (fun n : ℕ => r ^ (2 * n)) := by
    have h :
        Summable (fun n : ℕ => ((r ^ 2) ^ n)) :=
      summable_geometric_of_norm_lt_one (by
        rw [Real.norm_eq_abs, abs_pow, abs_of_pos hr0]
        nlinarith)
    simpa [pow_mul] using h
  have hseriesDeriv (y : ℝ) (hy : y ∈ Set.Ioo (-r) r) :
      HasDerivAt arcsineSeries (arcsineIntegrand y) y := by
    have h :=
      hasDerivAt_tsum_of_isPreconnected hboundSum
        isOpen_Ioo isPreconnected_Ioo
        (fun n z hz => arcsineTerm_hasDerivAt n z)
        hbound
        (show (0 : ℝ) ∈ Set.Ioo (-r) r by
          constructor <;> linarith)
        (show Summable (fun n : ℕ => arcsineSeriesTerm n 0) by
          simp [arcsineSeriesTerm])
        hy
    have hy1 : |y| < 1 := (abs_lt.2 hy).trans hr1
    rw [(arcsineIntegrand_hasSum y hy1).tsum_eq] at h
    simpa only [arcsineSeries] using h
  have harcsinDeriv (y : ℝ) (hy : y ∈ Set.Ioo (-r) r) :
      HasDerivAt Real.arcsin (arcsineIntegrand y) y := by
    apply Real.hasDerivAt_arcsin
    · have hy1 : |y| < 1 := (abs_lt.2 hy).trans hr1
      exact ne_of_gt (abs_lt.1 hy1).1
    · have hy1 : |y| < 1 := (abs_lt.2 hy).trans hr1
      exact ne_of_lt (abs_lt.1 hy1).2
  have heq :
      Set.EqOn arcsineSeries Real.arcsin (Set.Ioo (-r) r) := by
    apply isOpen_Ioo.eqOn_of_deriv_eq
      (x := (0 : ℝ)) isPreconnected_Ioo
    · intro y hy
      exact (hseriesDeriv y hy).differentiableAt.differentiableWithinAt
    · intro y hy
      exact (harcsinDeriv y hy).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [(hseriesDeriv y hy).deriv, (harcsinDeriv y hy).deriv]
    · constructor <;> linarith
    · have hzero : ∀ n : ℕ, arcsineSeriesTerm n 0 = 0 := by
        intro n
        simp [arcsineSeriesTerm, show 0 < 2 * n + 1 by omega]
      simp only [arcsineSeries, hzero, tsum_zero, Real.arcsin_zero]
  exact heq (abs_lt.1 hxr)

private def sineRatioFactor (u x : ℝ) (n : ℕ) : ℝ :=
  ((((2 * n + 1 : ℕ) : ℝ) ^ 2 - u ^ 2) * x ^ 2) /
    (((2 * n + 2 : ℕ) : ℝ) * ((2 * n + 3 : ℕ) : ℝ))

private theorem sineArcsineTerm_succ (u x : ℝ) (n : ℕ) :
    sineArcsineTerm u x (n + 1) =
      sineArcsineTerm u x n * sineRatioFactor u x n := by
  unfold sineArcsineTerm sineRatioFactor
  rw [Finset.prod_range_succ]
  have hfac :
      (Nat.factorial (2 * (n + 1) + 1) : ℝ) =
        ((2 * n + 3 : ℕ) : ℝ) * ((2 * n + 2 : ℕ) : ℝ) *
          (Nat.factorial (2 * n + 1) : ℝ) := by
    rw [show 2 * (n + 1) + 1 = (2 * n + 2) + 1 by omega,
      Nat.factorial_succ,
      show 2 * n + 2 = (2 * n + 1) + 1 by omega,
      Nat.factorial_succ]
    push_cast
    ring
  rw [hfac]
  have hf : (Nat.factorial (2 * n + 1) : ℝ) ≠ 0 := by positivity
  field_simp [hf]
  push_cast
  ring

private theorem sineRatioFactor_tendsto (u x : ℝ) :
    Tendsto (sineRatioFactor u x) Filter.atTop (nhds (x ^ 2)) := by
  have hidx : Tendsto (fun n : ℕ => 2 * n + 1) Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop.2 ?_
    intro b
    filter_upwards [Filter.eventually_ge_atTop b] with n hn
    omega
  have hcast :
      Tendsto (fun n : ℕ => (((2 * n + 1 : ℕ) : ℝ)))
        Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop.comp hidx
  have ha :
      Tendsto
        (fun n : ℕ =>
          (((2 * n + 1 : ℕ) : ℝ)) /
            (((2 * n + 1 : ℕ) : ℝ) + 1))
        Filter.atTop (nhds 1) := by
    convert (tendsto_natCast_div_add_atTop (𝕜 := ℝ) 1).comp hidx using 1
  have hb :
      Tendsto
        (fun n : ℕ =>
          (((2 * n + 1 : ℕ) : ℝ)) /
            (((2 * n + 1 : ℕ) : ℝ) + 2))
        Filter.atTop (nhds 1) := by
    convert (tendsto_natCast_div_add_atTop (𝕜 := ℝ) 2).comp hidx using 1
  have hc1 :
      Tendsto (fun n : ℕ => (((2 * n + 1 : ℕ) : ℝ)) + 1)
        Filter.atTop Filter.atTop :=
    Filter.Tendsto.atTop_add hcast tendsto_const_nhds
  have hc2 :
      Tendsto (fun n : ℕ => (((2 * n + 1 : ℕ) : ℝ)) + 2)
        Filter.atTop Filter.atTop :=
    Filter.Tendsto.atTop_add hcast tendsto_const_nhds
  have hi1 :
      Tendsto (fun n : ℕ => 1 / ((((2 * n + 1 : ℕ) : ℝ)) + 1))
        Filter.atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hc1
  have hi2 :
      Tendsto (fun n : ℕ => 1 / ((((2 * n + 1 : ℕ) : ℝ)) + 2))
        Filter.atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hc2
  have hmain :=
    ((ha.mul hb).mul_const (x ^ 2)).sub
      ((tendsto_const_nhds (x := u ^ 2 * x ^ 2)).mul (hi1.mul hi2))
  convert hmain using 1
  · funext n
    unfold sineRatioFactor
    have h1 : (((2 * n + 1 : ℕ) : ℝ) + 1) ≠ 0 := by positivity
    have h2 : (((2 * n + 1 : ℕ) : ℝ) + 2) ≠ 0 := by positivity
    push_cast
    field_simp [h1, h2]
    ring_nf
  · ring_nf

private theorem sineArcsineTerm_summable (u x : ℝ) (hx : |x| < 1) :
    Summable (sineArcsineTerm u x) := by
  have hsq : |x ^ 2| < 1 := by
    rw [abs_pow]
    nlinarith [abs_nonneg x]
  obtain ⟨q, hxq, hq1⟩ : ∃ q : ℝ, |x ^ 2| < q ∧ q < 1 :=
    exists_between hsq
  have hratio :
      ∀ᶠ n : ℕ in Filter.atTop,
        ‖sineArcsineTerm u x (n + 1)‖ ≤
          q * ‖sineArcsineTerm u x n‖ := by
    have hlim :
        Tendsto (fun n : ℕ => ‖sineRatioFactor u x n‖)
          Filter.atTop (nhds ‖x ^ 2‖) :=
      (sineRatioFactor_tendsto u x).norm
    have hev : ∀ᶠ n : ℕ in Filter.atTop, ‖sineRatioFactor u x n‖ < q :=
      (tendsto_order.1 hlim).2 _ hxq
    filter_upwards [hev] with n hn
    rw [sineArcsineTerm_succ, norm_mul]
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right hn.le
      (norm_nonneg (sineArcsineTerm u x n))
  exact summable_of_ratio_norm_eventually_le hq1 hratio

private theorem analyticAt_arcsin (x : ℝ) (hx : |x| < 1) :
    AnalyticAt ℝ Real.arcsin x := by
  have hxI : x ∈ Set.Ioo (-1 : ℝ) 1 := abs_lt.1 hx
  have hq : 0 < 1 - x ^ 2 := by
    exact sub_pos.2 ((sq_lt_one_iff_abs_lt_one x).2 hx)
  have hc : Real.cos (Real.arcsin x) ≠ 0 := by
    rw [Real.cos_arcsin]
    positivity
  let i : ℝ ≃L[ℝ] ℝ :=
    ContinuousLinearEquiv.unitsEquivAut ℝ
      (Units.mk0 (Real.cos (Real.arcsin x)) hc)
  have hi :
      fderiv ℝ Real.sin (Real.arcsin x) = (i : ℝ →L[ℝ] ℝ) := by
    rw [(Real.hasDerivAt_sin (Real.arcsin x)).hasFDerivAt.fderiv]
    ext y
    simp [i, ContinuousLinearEquiv.unitsEquivAut, Units.smul_def]
  have h :=
    Real.sinPartialHomeomorph.analyticAt_symm
      hxI Real.analyticAt_sin hi
  simpa using h

private theorem analyticAt_sine_arcsine (u x : ℝ) (hx : |x| < 1) :
    AnalyticAt ℝ (fun y => Real.sin (u * Real.arcsin y)) x := by
  simpa [Function.comp_def, smul_eq_mul] using
    Real.analyticAt_sin.comp
      ((analyticAt_arcsin x hx).const_smul (c := u))

private theorem sineTaylor_even (u : ℝ) (k : ℕ) :
    iteratedDeriv (2 * k)
        (fun x : ℝ => Real.sin (u * Real.arcsin x)) 0 = 0 := by
  simpa [iteratedDeriv_eq_iterate,
    ProofGap.Exercise1221_2.iterDeriv,
    ProofGap.Exercise1221_2.y,
    ProofGap.Exercise1221_2.f] using
      ProofGap.Exercise1221_2.gap15 u k

private theorem oddProduct_sign (u : ℝ) (k : ℕ) :
    (-1 : ℝ) ^ k *
        ProofGap.Exercise1221_2.oddProduct u k =
      ∏ j ∈ Finset.range k,
        (((2 * j + 1 : ℕ) : ℝ) ^ 2 - u ^ 2) := by
  unfold ProofGap.Exercise1221_2.oddProduct
  calc
    (-1 : ℝ) ^ k *
          (∏ j ∈ Finset.range k,
            (u ^ 2 - (2 * j + 1 : ℝ) ^ 2)) =
        (∏ _j ∈ Finset.range k, (-1 : ℝ)) *
          (∏ j ∈ Finset.range k,
            (u ^ 2 - (2 * j + 1 : ℝ) ^ 2)) := by simp
    _ = ∏ j ∈ Finset.range k,
          ((-1 : ℝ) * (u ^ 2 - (2 * j + 1 : ℝ) ^ 2)) := by
      rw [Finset.prod_mul_distrib]
    _ = ∏ j ∈ Finset.range k,
          (((2 * j + 1 : ℕ) : ℝ) ^ 2 - u ^ 2) := by
      apply Finset.prod_congr rfl
      intro j hj
      push_cast
      ring

private theorem sineTaylor_odd (u : ℝ) (k : ℕ) :
    iteratedDeriv (2 * k + 1)
          (fun x : ℝ => Real.sin (u * Real.arcsin x)) 0 /
        (Nat.factorial (2 * k + 1) : ℝ) =
      sineArcsineTerm u 1 k := by
  have hderiv :
      iteratedDeriv (2 * k + 1)
          (fun x : ℝ => Real.sin (u * Real.arcsin x)) 0 =
        (-1 : ℝ) ^ k * u *
          ProofGap.Exercise1221_2.oddProduct u k := by
    simpa [iteratedDeriv_eq_iterate,
      ProofGap.Exercise1221_2.iterDeriv,
      ProofGap.Exercise1221_2.y,
      ProofGap.Exercise1221_2.f] using
        ProofGap.Exercise1221_2.gap20 u k
  rw [hderiv]
  unfold sineArcsineTerm
  rw [one_pow, mul_one]
  rw [← oddProduct_sign u k]
  ring

private theorem sineArcsineTerm_scale (u x : ℝ) (k : ℕ) :
    sineArcsineTerm u x k =
      sineArcsineTerm u 1 k * x ^ (2 * k + 1) := by
  unfold sineArcsineTerm
  rw [one_pow, mul_one]

private def sineFunction (u x : ℝ) : ℝ :=
  Real.sin (u * Real.arcsin x)

private def sineTaylorCoefficient (u : ℝ) (n : ℕ) : ℝ :=
  iteratedDeriv n (sineFunction u) 0 / (Nat.factorial n : ℝ)

private def sineTaylorSeries (u : ℝ) : FormalMultilinearSeries ℝ ℝ ℝ :=
  FormalMultilinearSeries.ofScalars ℝ (sineTaylorCoefficient u)

private theorem sineTaylorSeries_eq (u : ℝ) :
    sineTaylorSeries u =
      FormalMultilinearSeries.ofScalars ℝ
        (fun n => iteratedDeriv n (sineFunction u) 0 /
          (Nat.factorial n : ℝ)) := by
  rfl

private theorem sineTaylorSeries_norm_even (u r : ℝ) (k : ℕ) :
    ‖sineTaylorSeries u (2 * k)‖ * r ^ (2 * k) = 0 := by
  rw [sineTaylorSeries, FormalMultilinearSeries.ofScalars_norm]
  change ‖iteratedDeriv (2 * k)
      (fun y : ℝ => Real.sin (u * Real.arcsin y)) 0 /
        (Nat.factorial (2 * k) : ℝ)‖ * r ^ (2 * k) = 0
  rw [sineTaylor_even]
  simp

private theorem sineTaylorSeries_norm_odd (u r : ℝ) (k : ℕ)
    (hr : 0 ≤ r) :
    ‖sineTaylorSeries u (2 * k + 1)‖ * r ^ (2 * k + 1) =
      ‖sineArcsineTerm u r k‖ := by
  rw [sineTaylorSeries, FormalMultilinearSeries.ofScalars_norm]
  change ‖iteratedDeriv (2 * k + 1)
      (fun y : ℝ => Real.sin (u * Real.arcsin y)) 0 /
        (Nat.factorial (2 * k + 1) : ℝ)‖ *
      r ^ (2 * k + 1) = _
  rw [sineTaylor_odd, sineArcsineTerm_scale u r k, norm_mul,
    norm_pow]
  simp only [Real.norm_eq_abs, abs_of_nonneg hr]

private theorem sineTaylorSeries_radius (u : ℝ) (r : NNReal)
    (hr : |(r : ℝ)| < 1) :
    (r : ENNReal) ≤ (sineTaylorSeries u).radius := by
  apply (sineTaylorSeries u).le_radius_of_summable_norm
  apply Summable.even_add_odd
  · have heq :
        (fun k : ℕ =>
          ‖sineTaylorSeries u (2 * k)‖ * (r : ℝ) ^ (2 * k)) =
          fun _ => 0 := by
      funext k
      exact sineTaylorSeries_norm_even u (r : ℝ) k
    rw [heq]
    exact summable_zero
  · have hs := (sineArcsineTerm_summable u (r : ℝ) hr).norm
    have heq :
        (fun k : ℕ =>
          ‖sineTaylorSeries u (2 * k + 1)‖ *
            (r : ℝ) ^ (2 * k + 1)) =
          fun k => ‖sineArcsineTerm u (r : ℝ) k‖ := by
      funext k
      exact sineTaylorSeries_norm_odd u (r : ℝ) k r.property
    rw [heq]
    exact hs

private theorem sineFunction_analyticOn_ball (u : ℝ) (r : NNReal)
    (hr : (r : ℝ) < 1) :
    AnalyticOn ℝ (sineFunction u)
      (Metric.eball (0 : ℝ) (r : ENNReal)) := by
  intro y hy
  apply (analyticAt_sine_arcsine u y ?_).analyticWithinAt
  have hyr : |y| < (r : ℝ) := by
    simpa [Metric.mem_eball, edist_dist, dist_zero_right,
      Real.norm_eq_abs] using hy
  exact hyr.trans hr

private theorem sineTaylorSeries_apply_even (u x : ℝ) (k : ℕ) :
    sineTaylorSeries u (2 * k) (fun _ => x) = 0 := by
  rw [sineTaylorSeries, FormalMultilinearSeries.ofScalars_apply_eq]
  simp only [smul_eq_mul]
  change iteratedDeriv (2 * k)
      (fun y : ℝ => Real.sin (u * Real.arcsin y)) 0 /
        (Nat.factorial (2 * k) : ℝ) * x ^ (2 * k) = 0
  rw [sineTaylor_even]
  simp

private theorem sineTaylorSeries_apply_odd (u x : ℝ) (k : ℕ) :
    sineTaylorSeries u (2 * k + 1) (fun _ => x) =
      sineArcsineTerm u x k := by
  rw [sineTaylorSeries, FormalMultilinearSeries.ofScalars_apply_eq]
  simp only [smul_eq_mul]
  change iteratedDeriv (2 * k + 1)
        (fun y : ℝ => Real.sin (u * Real.arcsin y)) 0 /
      (Nat.factorial (2 * k + 1) : ℝ) *
        x ^ (2 * k + 1) = _
  rw [sineTaylor_odd, ← sineArcsineTerm_scale]

attribute [irreducible] sineFunction sineTaylorCoefficient sineTaylorSeries

set_option maxHeartbeats 600000 in
private theorem sineTaylorSeries_hasSum_at
    (u x : ℝ) (r : NNReal) (hr0 : 0 < (r : ℝ))
    (hrlt : (r : ℝ) < 1) (hxr : |x| < (r : ℝ)) :
    HasSum (fun n => sineTaylorSeries u n (fun _ => x))
      (sineFunction u x) := by
  have hrabs : |(r : ℝ)| < 1 := by simpa using hrlt
  have hp :
      HasFPowerSeriesOnBall (sineFunction u) (sineTaylorSeries u)
        0 (r : ENNReal) := by
    rw [sineTaylorSeries_eq]
    apply (sineFunction_analyticOn_ball u r hrlt).hasFPowerSeriesOnSubball
    · exact_mod_cast hr0
    · simpa only [← sineTaylorSeries_eq] using
        sineTaylorSeries_radius u r hrabs
  have hxball : x ∈ Metric.eball (0 : ℝ) (r : ENNReal) := by
    simpa [Metric.mem_eball, edist_dist, dist_zero_right,
      Real.norm_eq_abs] using hxr
  simpa only [zero_add] using hp.hasSum hxball

private theorem hasSum_even_odd_zero {a : ℕ → ℝ} {s : ℝ}
    (heven : HasSum (fun k => a (2 * k)) 0)
    (hodd : HasSum (fun k => a (2 * k + 1)) s) :
    HasSum a s := by
  simpa only [zero_add] using heven.even_add_odd hodd

private theorem sineTaylorSeries_hasSum_transformed
    (u x : ℝ) (hx : |x| < 1) :
    HasSum (fun n => sineTaylorSeries u n (fun _ => x))
      (∑' k, sineArcsineTerm u x k) := by
  have heven :
      HasSum (fun k => sineTaylorSeries u (2 * k) (fun _ => x)) 0 := by
    refine HasSum.congr_fun
      (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℝ)) 0) ?_
    intro k
    exact sineTaylorSeries_apply_even u x k
  have hodd :
      HasSum (fun k => sineTaylorSeries u (2 * k + 1) (fun _ => x))
        (∑' k, sineArcsineTerm u x k) := by
    refine HasSum.congr_fun
      (sineArcsineTerm_summable u x hx).hasSum ?_
    intro k
    exact sineTaylorSeries_apply_odd u x k
  exact hasSum_even_odd_zero heven hodd

private theorem sineTaylor_hasSum (u x : ℝ) (hx : |x| < 1) :
    HasSum (sineArcsineTerm u x)
      (Real.sin (u * Real.arcsin x)) := by
  let rReal : ℝ := (|x| + 1) / 2
  have hr0 : 0 < rReal := by
    dsimp [rReal]
    nlinarith [abs_nonneg x]
  have hxr : |x| < rReal := by
    dsimp [rReal]
    linarith
  have hr1 : rReal < 1 := by
    dsimp [rReal]
    linarith
  let r : NNReal := ⟨rReal, hr0.le⟩
  have hrcoe : (r : ℝ) = rReal := rfl
  have hrlt : (r : ℝ) < 1 := by
    simpa [hrcoe] using hr1
  have hTaylor :
      HasSum (fun n => sineTaylorSeries u n (fun _ => x))
        (sineFunction u x) := by
    exact sineTaylorSeries_hasSum_at u x r
      (by simpa [hrcoe] using hr0) hrlt (by simpa [hrcoe] using hxr)
  have hfull :=
    sineTaylorSeries_hasSum_transformed u x hx
  have heq :
      (∑' k, sineArcsineTerm u x k) =
        Real.sin (u * Real.arcsin x) := by
    simpa [sineFunction] using hfull.unique hTaylor
  rw [← heq]
  exact (sineArcsineTerm_summable u x hx).hasSum

theorem gap1
    (f : ℝ → ℝ) (u : ℝ) (hf : ∀ x, f x = Real.sin (u * Real.arcsin x)) :
    ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      Real.arcsin x = ∫ t in (0 : ℝ)..x, arcsineIntegrand t := by
  intro x hx
  have hsub : Set.uIcc (0 : ℝ) x ⊆ Set.uIcc (-1 : ℝ) 1 :=
    Set.uIcc_subset_uIcc (by norm_num) (by
      simpa [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using hx)
  have hdiff :
      ∀ y ∈ Set.uIoo (0 : ℝ) x, DifferentiableAt ℝ Real.arcsin y := by
    intro y hy
    have hy' : y ∈ Set.Ioo (-1 : ℝ) 1 := by
      rcases le_total 0 x with h0x | hx0
      · rw [Set.uIoo_of_le h0x] at hy
        rcases hy with ⟨hy0, hyx⟩
        constructor <;> linarith [hx.1, hx.2]
      · rw [Set.uIoo_of_ge hx0] at hy
        rcases hy with ⟨hyx, hy0⟩
        constructor <;> linarith [hx.1, hx.2]
    exact Real.differentiableAt_arcsin.2
      ⟨ne_of_gt hy'.1, ne_of_lt hy'.2⟩
  have hint :
      IntervalIntegrable (deriv Real.arcsin) MeasureTheory.volume (0 : ℝ) x := by
    rw [Real.deriv_arcsin]
    simpa [one_div] using
      Polynomial.Chebyshev.intervalIntegrable_sqrt_one_sub_sq_inv.mono_set hsub
  have hftc :=
    intervalIntegral.integral_deriv_eq_sub_uIoo
      Real.continuous_arcsin.continuousOn hdiff hint
  symm
  simpa [Real.deriv_arcsin, arcsineIntegrand] using hftc

theorem gap2
    (f : ℝ → ℝ) (u : ℝ) (hf : ∀ x, f x = Real.sin (u * Real.arcsin x))
    (harcsin :
      ∀ x ∈ Set.Icc (-1 : ℝ) 1,
        Real.arcsin x = ∫ t in (0 : ℝ)..x, arcsineIntegrand t) :
    ∀ x ∈ Set.Ioo (-1 : ℝ) 1,
      (∫ t in (0 : ℝ)..x, arcsineIntegrand t) =
        ∫ t in (0 : ℝ)..x, ∑' n, arcsineIntegrandTerm t n := by
  intro x hx
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : |t| < 1 := by
    apply abs_lt.2
    rcases le_total 0 x with h0x | hx0
    · rw [Set.uIcc_of_le h0x] at ht
      exact ⟨by linarith [ht.1], by linarith [ht.2, hx.2]⟩
    · rw [Set.uIcc_of_ge hx0] at ht
      exact ⟨by linarith [ht.1, hx.1], by linarith [ht.2]⟩
  exact (arcsineIntegrand_hasSum t ht').tsum_eq.symm

theorem gap3
    (f : ℝ → ℝ) (u : ℝ) (hf : ∀ x, f x = Real.sin (u * Real.arcsin x))
    (harcsin :
      ∀ x ∈ Set.Icc (-1 : ℝ) 1,
        Real.arcsin x = ∫ t in (0 : ℝ)..x, arcsineIntegrand t)
    (hintegrand :
      ∀ x ∈ Set.Ioo (-1 : ℝ) 1,
        (∫ t in (0 : ℝ)..x, arcsineIntegrand t) =
          ∫ t in (0 : ℝ)..x, ∑' n, arcsineIntegrandTerm t n) :
    ∀ x ∈ Set.Ioo (-1 : ℝ) 1,
      (∫ t in (0 : ℝ)..x, ∑' n, arcsineIntegrandTerm t n) =
        ∑' n, arcsineTerm x n := by
  intro x hx
  have hxabs : |x| < 1 := abs_lt.2 hx
  calc
    (∫ t in (0 : ℝ)..x, ∑' n, arcsineIntegrandTerm t n) =
        ∫ t in (0 : ℝ)..x, arcsineIntegrand t :=
      (hintegrand x hx).symm
    _ = Real.arcsin x :=
      (harcsin x ⟨hx.1.le, hx.2.le⟩).symm
    _ = arcsineSeries x := (arcsineSeries_eq_arcsin x hxabs).symm
    _ = ∑' n, arcsineTerm x n := by
      apply tsum_congr
      intro n
      exact arcsineSeriesTerm_eq n x

theorem gap4
    (f : ℝ → ℝ) (u : ℝ) (hf : ∀ x, f x = Real.sin (u * Real.arcsin x))
    (harcsin :
      ∀ x ∈ Set.Icc (-1 : ℝ) 1,
        Real.arcsin x = ∫ t in (0 : ℝ)..x, arcsineIntegrand t)
    (hintegrand :
      ∀ x ∈ Set.Ioo (-1 : ℝ) 1,
        (∫ t in (0 : ℝ)..x, arcsineIntegrand t) =
          ∫ t in (0 : ℝ)..x, ∑' n, arcsineIntegrandTerm t n)
    (hintegral :
      ∀ x ∈ Set.Ioo (-1 : ℝ) 1,
        (∫ t in (0 : ℝ)..x, ∑' n, arcsineIntegrandTerm t n) =
          ∑' n, arcsineTerm x n) :
    ∀ x ∈ Set.Ioo (-1 : ℝ) 1, Real.arcsin x = ∑' n, arcsineTerm x n := by
  intro x hx
  calc
    Real.arcsin x =
        ∫ t in (0 : ℝ)..x, arcsineIntegrand t :=
      harcsin x ⟨hx.1.le, hx.2.le⟩
    _ = ∫ t in (0 : ℝ)..x, ∑' n, arcsineIntegrandTerm t n :=
      hintegrand x hx
    _ = ∑' n, arcsineTerm x n := hintegral x hx

theorem gap5
    (f : ℝ → ℝ) (u : ℝ) (hf : ∀ x, f x = Real.sin (u * Real.arcsin x))
    (harcsin :
      ∀ x ∈ Set.Icc (-1 : ℝ) 1,
        Real.arcsin x = ∫ t in (0 : ℝ)..x, arcsineIntegrand t)
    (hintegrand :
      ∀ x ∈ Set.Ioo (-1 : ℝ) 1,
        (∫ t in (0 : ℝ)..x, arcsineIntegrand t) =
          ∫ t in (0 : ℝ)..x, ∑' n, arcsineIntegrandTerm t n)
    (hintegral :
      ∀ x ∈ Set.Ioo (-1 : ℝ) 1,
        (∫ t in (0 : ℝ)..x, ∑' n, arcsineIntegrandTerm t n) =
          ∑' n, arcsineTerm x n)
    (harcsinSeries :
      ∀ x ∈ Set.Ioo (-1 : ℝ) 1, Real.arcsin x = ∑' n, arcsineTerm x n) :
    ∀ x, f x = ∑' n, sineCompositionTerm u x n := by
  intro x
  rw [hf, Real.sin_eq_tsum]
  apply tsum_congr
  intro n
  unfold sineCompositionTerm
  rw [mul_pow]
  ring

theorem gap6
    (f : ℝ → ℝ) (u : ℝ) (hf : ∀ x, f x = Real.sin (u * Real.arcsin x))
    (harcsin :
      ∀ x ∈ Set.Icc (-1 : ℝ) 1,
        Real.arcsin x = ∫ t in (0 : ℝ)..x, arcsineIntegrand t)
    (hintegrand :
      ∀ x ∈ Set.Ioo (-1 : ℝ) 1,
        (∫ t in (0 : ℝ)..x, arcsineIntegrand t) =
          ∫ t in (0 : ℝ)..x, ∑' n, arcsineIntegrandTerm t n)
    (hintegral :
      ∀ x ∈ Set.Ioo (-1 : ℝ) 1,
        (∫ t in (0 : ℝ)..x, ∑' n, arcsineIntegrandTerm t n) =
          ∑' n, arcsineTerm x n)
    (harcsinSeries :
      ∀ x ∈ Set.Ioo (-1 : ℝ) 1, Real.arcsin x = ∑' n, arcsineTerm x n)
    (hsine : ∀ x, f x = ∑' n, sineCompositionTerm u x n) :
    ∀ x ∈ Set.Ioo (-1 : ℝ) 1, f x = ∑' n, sineArcsineTerm u x n := by
  intro x hx
  rw [hf]
  exact (sineTaylor_hasSum u x (abs_lt.2 hx)).tsum_eq.symm

theorem gap7
    (f : ℝ → ℝ) (u : ℝ) (hf : ∀ x, f x = Real.sin (u * Real.arcsin x))
    (harcsin :
      ∀ x ∈ Set.Icc (-1 : ℝ) 1,
        Real.arcsin x = ∫ t in (0 : ℝ)..x, arcsineIntegrand t)
    (hintegrand :
      ∀ x ∈ Set.Ioo (-1 : ℝ) 1,
        (∫ t in (0 : ℝ)..x, arcsineIntegrand t) =
          ∫ t in (0 : ℝ)..x, ∑' n, arcsineIntegrandTerm t n)
    (hintegral :
      ∀ x ∈ Set.Ioo (-1 : ℝ) 1,
        (∫ t in (0 : ℝ)..x, ∑' n, arcsineIntegrandTerm t n) =
          ∑' n, arcsineTerm x n)
    (harcsinSeries :
      ∀ x ∈ Set.Ioo (-1 : ℝ) 1, Real.arcsin x = ∑' n, arcsineTerm x n)
    (hsine : ∀ x, f x = ∑' n, sineCompositionTerm u x n)
    (htransformed :
      ∀ x ∈ Set.Ioo (-1 : ℝ) 1, f x = ∑' n, sineArcsineTerm u x n) :
    ∀ x ∈ Set.Ioo (-1 : ℝ) 1, Summable (sineArcsineTerm u x) := by
  intro x hx
  exact sineArcsineTerm_summable u x (abs_lt.2 hx)

end

end ProofGap.Exercise2845
