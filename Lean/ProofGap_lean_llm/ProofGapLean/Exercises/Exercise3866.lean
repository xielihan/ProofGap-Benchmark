import ProofGapLean.Prelude.Analysis
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Bochner.Set

namespace ProofGap.Exercise3866

noncomputable section

open MeasureTheory Set
open scoped Interval Topology

def betaFn (p q : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..1,
    Real.rpow x (p - 1) * Real.rpow (1 - x) (q - 1)

def kernel (p x : ℝ) : ℝ :=
  (Real.rpow x (p - 1) - Real.rpow x (-p)) / (1 - x)

def regularizedKernel (p x : ℝ) : ℝ :=
  if x = 1 then 1 - 2 * p else kernel p x

def derivativeQuotient (p x : ℝ) : ℝ :=
  ((p - 1) * Real.rpow x (p - 2) +
    p * Real.rpow x (-p - 1)) / (-1)

def p₀ (p : ℝ) : ℝ :=
  max p (1 - p)

def I (p ε : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..1,
    (Real.rpow x (p - 1) - Real.rpow x (-p)) /
      Real.rpow (1 - x) (1 - ε)

def gammaExpression (p ε : ℝ) : ℝ :=
  Real.Gamma ε *
      (Real.Gamma p * Real.Gamma (1 - p + ε) -
        Real.Gamma (1 - p) * Real.Gamma (p + ε)) /
    (Real.Gamma (p + ε) * Real.Gamma (1 - p + ε))

private def coeff (p : ℝ) (n : ℕ) : ℝ :=
  1 / ((n : ℝ) + p) - 1 / ((n : ℝ) + 1 - p)

private def term (p : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  Real.rpow x ((n : ℝ) + p - 1) -
    Real.rpow x ((n : ℝ) - p)

private def cotCoeff (p : ℝ) (n : ℕ) : ℝ :=
  1 / (p - ((n : ℝ) + 1)) + 1 / (p + ((n : ℝ) + 1))

private theorem p_mem_integerComplement
    (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    (p : ℂ) ∈ Complex.integerComplement := by
  rw [Complex.mem_integerComplement_iff]
  rintro ⟨n, hn⟩
  have hnR : (n : ℝ) = p := by
    exact_mod_cast congrArg Complex.re hn
  have hn0 : (0 : ℤ) < n := by
    exact_mod_cast (hnR.symm ▸ hp)
  have hn1 : n < (1 : ℤ) := by
    exact_mod_cast (hnR.symm ▸ hp1)
  omega

private theorem coeff_summable
    (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    Summable (coeff p) := by
  have hbase :
      Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ (2 : ℕ)) := by
    have h :=
      (Real.summable_one_div_nat_pow (p := 2)).2 (by norm_num)
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff 1).2 h
  have hmajor :
      Summable
        (fun n : ℕ => |1 - 2 * p| * (1 / ((n : ℝ) + 1) ^ (2 : ℕ))) :=
    hbase.mul_left _
  have hshift : Summable (fun n : ℕ => coeff p (n + 1)) := by
    refine hmajor.of_norm_bounded (fun n => ?_)
    have hn : 0 < (n : ℝ) + 1 := by positivity
    have hA : 0 < (n : ℝ) + 1 + p := by positivity
    have hB : 0 < (n : ℝ) + 2 - p := by linarith
    have hB' : (n : ℝ) + 1 + 1 - p ≠ 0 := by linarith
    have hprod :
        ((n : ℝ) + 1) ^ 2 ≤
          ((n : ℝ) + 1 + p) * ((n : ℝ) + 2 - p) := by
      nlinarith [mul_nonneg
        (by linarith : 0 ≤ p)
        (by linarith : 0 ≤ (n : ℝ) + 1 - p)]
    have heq :
        coeff p (n + 1) =
          (1 - 2 * p) /
            (((n : ℝ) + 1 + p) * ((n : ℝ) + 2 - p)) := by
      unfold coeff
      push_cast
      field_simp [hA.ne', hB.ne', hB']
      ring
    rw [heq, Real.norm_eq_abs, abs_div,
      abs_of_pos (mul_pos hA hB)]
    have hdenSq : 0 < ((n : ℝ) + 1) ^ 2 := sq_pos_of_pos hn
    calc
      |1 - 2 * p| /
            (((n : ℝ) + 1 + p) * ((n : ℝ) + 2 - p)) ≤
          |1 - 2 * p| / ((n : ℝ) + 1) ^ 2 :=
        div_le_div_of_nonneg_left (abs_nonneg _) hdenSq hprod
      _ = |1 - 2 * p| * (1 / ((n : ℝ) + 1) ^ 2) := by ring
  exact (summable_nat_add_iff 1).mp (by simpa using hshift)

private theorem cotCoeff_summable
    (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    Summable (cotCoeff p) := by
  have hc := summable_cotTerm (p_mem_integerComplement p hp hp1)
  rw [← Complex.summable_ofReal]
  apply hc.congr
  intro n
  simp only [cotCoeff, cotTerm,
    Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_div,
    Complex.ofReal_one, Complex.ofReal_natCast]

private theorem sum_coeff_identity
    (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (N : ℕ) :
    (∑ n ∈ Finset.range N, coeff p n) =
      1 / p + (∑ n ∈ Finset.range N, cotCoeff p n) -
        1 / ((N : ℝ) + p) := by
  induction N with
  | zero =>
      simp
  | succ N ih =>
      simp only [Finset.sum_range_succ, Nat.cast_add, Nat.cast_one]
      rw [ih]
      have hNp : 0 < (N : ℝ) + p := by positivity
      have hN1p : 0 < (N : ℝ) + 1 - p := by
        have hN : (0 : ℝ) ≤ N := by positivity
        linarith
      have hN1p' : 0 < (N : ℝ) + 1 + p := by positivity
      have hCotNeg : p - ((N : ℝ) + 1) ≠ 0 := by linarith
      have hlocal :
          coeff p N =
            cotCoeff p N + 1 / ((N : ℝ) + p) -
              1 / ((N : ℝ) + 1 + p) := by
        unfold coeff cotCoeff
        field_simp [hNp.ne', hN1p.ne', hN1p'.ne', hCotNeg]
        ring
      rw [hlocal]
      ring

private theorem tsum_coeff_eq_cotCoeff
    (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    (∑' n : ℕ, coeff p n) =
      1 / p + ∑' n : ℕ, cotCoeff p n := by
  have hcoeff :=
    (coeff_summable p hp hp1).hasSum.tendsto_sum_nat
  have hcot :=
    (cotCoeff_summable p hp hp1).hasSum.tendsto_sum_nat
  have hden :
      Filter.Tendsto (fun N : ℕ => (N : ℝ) + p)
        Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_right Filter.atTop p
      tendsto_natCast_atTop_atTop
  have hboundary :
      Filter.Tendsto (fun N : ℕ => 1 / ((N : ℝ) + p))
        Filter.atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hden
  have hrhs :
      Filter.Tendsto
        (fun N : ℕ =>
          1 / p + (∑ n ∈ Finset.range N, cotCoeff p n) -
            1 / ((N : ℝ) + p))
        Filter.atTop
        (nhds (1 / p + ∑' n : ℕ, cotCoeff p n)) := by
    simpa only [sub_zero] using
      (tendsto_const_nhds.add hcot).sub hboundary
  have hrhs' :
      Filter.Tendsto
        (fun N : ℕ => ∑ n ∈ Finset.range N, coeff p n)
        Filter.atTop
        (nhds (1 / p + ∑' n : ℕ, cotCoeff p n)) :=
    hrhs.congr'
      (Filter.Eventually.of_forall
        (fun N => (sum_coeff_identity p hp hp1 N).symm))
  exact tendsto_nhds_unique hcoeff hrhs'

private theorem one_div_add_tsum_cotCoeff_eq_closed
    (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    1 / p + ∑' n : ℕ, cotCoeff p n =
      Real.pi * Real.cos (p * Real.pi) / Real.sin (p * Real.pi) := by
  have hz := p_mem_integerComplement p hp hp1
  have hseries := cot_series_rep' hz
  apply Complex.ofReal_injective
  calc
    (((1 / p + ∑' n : ℕ, cotCoeff p n : ℝ) : ℝ) : ℂ) =
        1 / (p : ℂ) + ∑' n : ℕ, cotTerm (p : ℂ) n := by
      rw [Complex.ofReal_add, Complex.ofReal_div, Complex.ofReal_one,
        Complex.ofReal_tsum]
      congr 1
      apply tsum_congr
      intro n
      simp only [cotCoeff, cotTerm, Complex.ofReal_add, Complex.ofReal_sub,
        Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_natCast]
    _ = (Real.pi : ℂ) * Complex.cot ((Real.pi : ℂ) * (p : ℂ)) := by
      rw [← hseries]
      ring
    _ = ((Real.pi * Real.cos (p * Real.pi) /
          Real.sin (p * Real.pi) : ℝ) : ℂ) := by
      rw [Complex.cot]
      rw [← Complex.ofReal_mul]
      rw [← Complex.ofReal_cos, ← Complex.ofReal_sin]
      push_cast
      ring

private theorem term_integrable
    (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (n : ℕ) :
    IntegrableOn (term p n) (Ioo (0 : ℝ) 1) volume := by
  apply Integrable.sub
  · exact
      (intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).2
        (by
          have hn : (0 : ℝ) ≤ n := by positivity
          linarith)
  · exact
      (intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).2
        (by
          have hn : (0 : ℝ) ≤ n := by positivity
          linarith)

private theorem rpow_setIntegral
    (r : ℝ) (hr : -1 < r) :
    (∫ x in Ioo (0 : ℝ) 1, Real.rpow x r ∂volume) =
      1 / (r + 1) := by
  rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le zero_le_one]
  simp only [Real.rpow_eq_pow]
  rw [integral_rpow (Or.inl hr)]
  rw [Real.one_rpow, Real.zero_rpow (by linarith : r + 1 ≠ 0)]
  ring

private theorem term_integral
    (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (n : ℕ) :
    (∫ x in Ioo (0 : ℝ) 1, term p n x ∂volume) =
      coeff p n := by
  have h1 :
      IntegrableOn (fun x : ℝ => Real.rpow x ((n : ℝ) + p - 1))
        (Ioo (0 : ℝ) 1) volume :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).2
      (by
        have hn : (0 : ℝ) ≤ n := by positivity
        linarith)
  have h2 :
      IntegrableOn (fun x : ℝ => Real.rpow x ((n : ℝ) - p))
        (Ioo (0 : ℝ) 1) volume :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).2
      (by
        have hn : (0 : ℝ) ≤ n := by positivity
        linarith)
  change
    (∫ x in Ioo (0 : ℝ) 1,
      Real.rpow x ((n : ℝ) + p - 1) -
        Real.rpow x ((n : ℝ) - p) ∂volume) = coeff p n
  rw [integral_sub h1 h2,
    rpow_setIntegral _ (by
      have hn : (0 : ℝ) ≤ n := by positivity
      linarith),
    rpow_setIntegral _ (by
      have hn : (0 : ℝ) ≤ n := by positivity
      linarith)]
  unfold coeff
  ring_nf

private theorem term_nonneg_of_le_half
    (p : ℝ) (hpHalf : p ≤ 1 / 2)
    (n : ℕ) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    0 ≤ term p n x := by
  unfold term
  rw [sub_nonneg]
  have hexp :
      (n : ℝ) + p - 1 ≤ (n : ℝ) - p := by
    linarith
  exact
    (Real.rpow_le_rpow_left_iff_of_base_lt_one hx.1 hx.2).2 hexp

private theorem term_nonpos_of_half_le
    (p : ℝ) (hpHalf : 1 / 2 ≤ p)
    (n : ℕ) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    term p n x ≤ 0 := by
  unfold term
  rw [sub_nonpos]
  have hexp :
      (n : ℝ) - p ≤ (n : ℝ) + p - 1 := by
    linarith
  exact
    (Real.rpow_le_rpow_left_iff_of_base_lt_one hx.1 hx.2).2 hexp

private theorem integral_norm_term
    (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (n : ℕ) :
    (∫ x in Ioo (0 : ℝ) 1, ‖term p n x‖ ∂volume) =
      ‖coeff p n‖ := by
  by_cases hhalf : p ≤ 1 / 2
  · have hnonneg :
        ∀ x ∈ Ioo (0 : ℝ) 1, 0 ≤ term p n x :=
      fun x hx => term_nonneg_of_le_half p hhalf n hx
    have hcoeff : 0 ≤ coeff p n := by
      rw [← term_integral p hp hp1 n]
      exact setIntegral_nonneg measurableSet_Ioo hnonneg
    calc
      (∫ x in Ioo (0 : ℝ) 1, ‖term p n x‖ ∂volume) =
          ∫ x in Ioo (0 : ℝ) 1, term p n x ∂volume := by
        apply setIntegral_congr_fun measurableSet_Ioo
        intro x hx
        exact Real.norm_of_nonneg (hnonneg x hx)
      _ = coeff p n := term_integral p hp hp1 n
      _ = ‖coeff p n‖ := (Real.norm_of_nonneg hcoeff).symm
  · have hhalf' : 1 / 2 ≤ p := by linarith
    have hnonpos :
        ∀ x ∈ Ioo (0 : ℝ) 1, term p n x ≤ 0 :=
      fun x hx => term_nonpos_of_half_le p hhalf' n hx
    have hcoeff : coeff p n ≤ 0 := by
      have hneg :=
        setIntegral_nonneg (μ := volume) measurableSet_Ioo
          (fun x hx => neg_nonneg.mpr (hnonpos x hx))
      rw [integral_neg, term_integral p hp hp1 n] at hneg
      linarith
    calc
      (∫ x in Ioo (0 : ℝ) 1, ‖term p n x‖ ∂volume) =
          ∫ x in Ioo (0 : ℝ) 1, -term p n x ∂volume := by
        apply setIntegral_congr_fun measurableSet_Ioo
        intro x hx
        exact Real.norm_of_nonpos (hnonpos x hx)
      _ = -(∫ x in Ioo (0 : ℝ) 1, term p n x ∂volume) := by
        rw [integral_neg]
      _ = -coeff p n := by rw [term_integral p hp hp1 n]
      _ = ‖coeff p n‖ := (Real.norm_of_nonpos hcoeff).symm

private theorem term_series_eq_kernel
    (p x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) :
    (∑' n : ℕ, term p n x) = kernel p x := by
  have hx0 : 0 < x := hx.1
  have hxnorm : ‖x‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos hx0]
    exact hx.2
  have hgeom : Summable (fun n : ℕ => x ^ n) :=
    summable_geometric_of_norm_lt_one hxnorm
  have hApoint :
      ∀ n : ℕ,
        Real.rpow x ((n : ℝ) + p - 1) =
          Real.rpow x (p - 1) * x ^ n := by
    intro n
    calc
      Real.rpow x ((n : ℝ) + p - 1) =
          Real.rpow x ((p - 1) + (n : ℝ)) := by
        congr 1
        ring
      _ = Real.rpow x (p - 1) * Real.rpow x (n : ℝ) :=
        Real.rpow_add hx0 _ _
      _ = Real.rpow x (p - 1) * x ^ n := by
        congr 1
        exact Real.rpow_natCast x n
  have hBpoint :
      ∀ n : ℕ,
        Real.rpow x ((n : ℝ) - p) =
          Real.rpow x (-p) * x ^ n := by
    intro n
    calc
      Real.rpow x ((n : ℝ) - p) =
          Real.rpow x ((-p) + (n : ℝ)) := by
        congr 1
        ring
      _ = Real.rpow x (-p) * Real.rpow x (n : ℝ) :=
        Real.rpow_add hx0 _ _
      _ = Real.rpow x (-p) * x ^ n := by
        congr 1
        exact Real.rpow_natCast x n
  have hA :
      Summable (fun n : ℕ => Real.rpow x ((n : ℝ) + p - 1)) :=
    (hgeom.mul_left (Real.rpow x (p - 1))).congr
      (fun n => (hApoint n).symm)
  have hB :
      Summable (fun n : ℕ => Real.rpow x ((n : ℝ) - p)) :=
    (hgeom.mul_left (Real.rpow x (-p))).congr
      (fun n => (hBpoint n).symm)
  have hden : 1 - x ≠ 0 := (sub_pos.mpr hx.2).ne'
  unfold term kernel
  rw [hA.tsum_sub hB, tsum_congr hApoint, tsum_congr hBpoint,
    tsum_mul_left, tsum_mul_left, tsum_geometric_of_norm_lt_one hxnorm]
  field_simp [hden]

private theorem kernel_integral_eq_tsum_coeff
    (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    (∫ x in Ioo (0 : ℝ) 1, kernel p x ∂volume) =
      ∑' n : ℕ, coeff p n := by
  let μ : Measure ℝ := volume.restrict (Ioo (0 : ℝ) 1)
  have htermInt : ∀ n : ℕ, Integrable (term p n) μ :=
    fun n => term_integrable p hp hp1 n
  have hnormSum :
      Summable (fun n : ℕ => ∫ x, ‖term p n x‖ ∂μ) := by
    have h := (coeff_summable p hp hp1).norm
    apply h.congr
    intro n
    change
      ‖coeff p n‖ =
        ∫ x in Ioo (0 : ℝ) 1, ‖term p n x‖ ∂volume
    exact (integral_norm_term p hp hp1 n).symm
  have hswap :=
    integral_tsum_of_summable_integral_norm htermInt hnormSum
  change (∫ x, kernel p x ∂μ) = ∑' n : ℕ, coeff p n
  calc
    (∫ x, kernel p x ∂μ) =
        ∫ x, (∑' n : ℕ, term p n x) ∂μ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      exact (term_series_eq_kernel p x hx).symm
    _ = ∑' n : ℕ, ∫ x, term p n x ∂μ := hswap.symm
    _ = ∑' n : ℕ, coeff p n := by
      apply tsum_congr
      intro n
      change
        (∫ x in Ioo (0 : ℝ) 1, term p n x ∂volume) =
          coeff p n
      exact term_integral p hp hp1 n

private theorem kernel_integral_closed
    (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    (∫ x in Ioo (0 : ℝ) 1, kernel p x ∂volume) =
      Real.pi * Real.cos (p * Real.pi) / Real.sin (p * Real.pi) := by
  rw [kernel_integral_eq_tsum_coeff p hp hp1,
    tsum_coeff_eq_cotCoeff p hp hp1,
    one_div_add_tsum_cotCoeff_eq_closed p hp hp1]

private theorem numerator_hasDerivAt
    (p x : ℝ) (hx : 0 < x) :
    HasDerivAt
      (fun y : ℝ => Real.rpow y (p - 1) - Real.rpow y (-p))
      ((p - 1) * Real.rpow x (p - 2) +
        p * Real.rpow x (-p - 1)) x := by
  have hA :=
    Real.hasDerivAt_rpow_const (x := x) (p := p - 1)
      (Or.inl hx.ne')
  have hB :=
    Real.hasDerivAt_rpow_const (x := x) (p := -p)
      (Or.inl hx.ne')
  convert hA.sub hB using 1 <;> ring_nf
  rfl

private theorem derivativeQuotient_continuousAt_one (p : ℝ) :
    ContinuousAt (derivativeQuotient p) 1 := by
  have hA :
      ContinuousAt (fun x : ℝ => Real.rpow x (p - 2)) 1 :=
    Real.continuousAt_rpow_const 1 (p - 2) (Or.inl one_ne_zero)
  have hB :
      ContinuousAt (fun x : ℝ => Real.rpow x (-p - 1)) 1 :=
    Real.continuousAt_rpow_const 1 (-p - 1) (Or.inl one_ne_zero)
  unfold derivativeQuotient
  exact ((continuousAt_const.mul hA).add
    (continuousAt_const.mul hB)).div_const (-1)

private theorem derivativeQuotient_tendsto_one (p : ℝ) :
    Tendsto (derivativeQuotient p) (nhds 1) (nhds (1 - 2 * p)) := by
  convert (derivativeQuotient_continuousAt_one p).tendsto using 1
  simp [derivativeQuotient]
  ring

private theorem kernel_tendsto_one_punctured (p : ℝ) :
    Tendsto (kernel p) (nhdsWithin 1 ({1}ᶜ : Set ℝ))
      (nhds (1 - 2 * p)) := by
  let f : ℝ → ℝ :=
    fun x => Real.rpow x (p - 1) - Real.rpow x (-p)
  let f' : ℝ → ℝ :=
    fun x => (p - 1) * Real.rpow x (p - 2) +
      p * Real.rpow x (-p - 1)
  let g : ℝ → ℝ := fun x => 1 - x
  let g' : ℝ → ℝ := fun _ => -1
  have hpos : ∀ᶠ x : ℝ in nhdsWithin 1 ({1}ᶜ : Set ℝ), 0 < x := by
    have h : ∀ᶠ x : ℝ in nhds (1 : ℝ), 0 < x :=
      Ioi_mem_nhds one_pos
    exact h.filter_mono inf_le_left
  have hfder : ∀ᶠ x in nhdsWithin 1 ({1}ᶜ : Set ℝ),
      HasDerivAt f (f' x) x := by
    filter_upwards [hpos] with x hx
    exact numerator_hasDerivAt p x hx
  have hgder : ∀ᶠ x in nhdsWithin 1 ({1}ᶜ : Set ℝ),
      HasDerivAt g (g' x) x := by
    filter_upwards with x
    simpa [g, g'] using
      (hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)
  have hg' : ∀ᶠ x in nhdsWithin 1 ({1}ᶜ : Set ℝ), g' x ≠ 0 := by
    filter_upwards with x
    simp [g']
  have hf0 : Tendsto f (nhdsWithin 1 ({1}ᶜ : Set ℝ)) (nhds 0) := by
    have hA :
        ContinuousAt (fun x : ℝ => Real.rpow x (p - 1)) 1 :=
      Real.continuousAt_rpow_const 1 (p - 1) (Or.inl one_ne_zero)
    have hB :
        ContinuousAt (fun x : ℝ => Real.rpow x (-p)) 1 :=
      Real.continuousAt_rpow_const 1 (-p) (Or.inl one_ne_zero)
    have hfull := (hA.sub hB).tendsto
    have h := hfull.mono_left
      (show nhdsWithin 1 ({1}ᶜ : Set ℝ) ≤ nhds (1 : ℝ) from inf_le_left)
    simpa [f] using h
  have hg0 : Tendsto g (nhdsWithin 1 ({1}ᶜ : Set ℝ)) (nhds 0) := by
    have h : ContinuousAt (fun x : ℝ => 1 - x) 1 :=
      continuousAt_const.sub continuousAt_id
    simpa [g] using h.tendsto.mono_left inf_le_left
  have hdiv :
      Tendsto (fun x => f' x / g' x)
        (nhdsWithin 1 ({1}ᶜ : Set ℝ)) (nhds (1 - 2 * p)) := by
    have h :=
      (derivativeQuotient_tendsto_one p).mono_left
        (show nhdsWithin 1 ({1}ᶜ : Set ℝ) ≤ nhds (1 : ℝ) from inf_le_left)
    simpa [f', g', derivativeQuotient] using h
  have h :=
    HasDerivAt.lhopital_zero_nhdsNE hfder hgder hg' hf0 hg0 hdiv
  simpa [f, g, kernel] using h

private theorem kernel_tendsto_one_left (p : ℝ) :
    Tendsto (kernel p) (nhdsWithin 1 (Iio 1))
      (nhds (1 - 2 * p)) :=
  (kernel_tendsto_one_punctured p).mono_left (nhdsLT_le_nhdsNE 1)

theorem gap1 (p L : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    Tendsto (kernel p) (nhdsWithin 1 (Set.Iio 1)) (nhds L) ↔
      Tendsto (derivativeQuotient p)
        (nhdsWithin 1 (Set.Iio 1)) (nhds L) := by
  have hk := kernel_tendsto_one_left p
  have hd :=
    (derivativeQuotient_tendsto_one p).mono_left
      (show nhdsWithin 1 (Iio 1) ≤ nhds 1 from inf_le_left)
  constructor
  · intro h
    have hL : L = 1 - 2 * p := tendsto_nhds_unique h hk
    simpa [hL] using hd
  · intro h
    have hL : L = 1 - 2 * p := tendsto_nhds_unique h hd
    simpa [hL] using hk

theorem gap2 (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    Tendsto (derivativeQuotient p)
      (nhdsWithin 1 (Set.Iio 1)) (nhds (1 - 2 * p)) :=
  (derivativeQuotient_tendsto_one p).mono_left inf_le_left

theorem gap3 (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    Tendsto (kernel p)
      (nhdsWithin 1 (Set.Iio 1)) (nhds (1 - 2 * p)) :=
  kernel_tendsto_one_left p

theorem gap4 (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    ContinuousAt (regularizedKernel p) 1 := by
  rw [continuousAt_iff_punctured_nhds]
  have heq :
      regularizedKernel p =ᶠ[nhdsWithin 1 ({1}ᶜ : Set ℝ)] kernel p := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hx
    simp [regularizedKernel, hx]
  have hvalue : regularizedKernel p 1 = 1 - 2 * p := by
    simp [regularizedKernel]
  rw [hvalue]
  exact (kernel_tendsto_one_punctured p).congr' heq.symm

theorem gap5 (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    0 < p₀ p := by
  unfold p₀
  exact hp.trans_le (le_max_left _ _)

theorem gap6 (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    p₀ p < 1 := by
  unfold p₀
  rw [max_lt_iff]
  exact ⟨hp1, by linarith⟩

theorem gap7 : (0 : ℝ) < 1 := zero_lt_one

private theorem weighted_kernel_eq
    (p p₀' x : ℝ) (hx : 0 < x) :
    Real.rpow x p₀' * |kernel p x| =
      |(Real.rpow x (p₀' - (1 - p)) -
          Real.rpow x (p₀' - p)) / (1 - x)| := by
  have hA :
      Real.rpow x p₀' * Real.rpow x (p - 1) =
        Real.rpow x (p₀' - (1 - p)) := by
    calc
      Real.rpow x p₀' * Real.rpow x (p - 1) =
          Real.rpow x (p₀' + (p - 1)) :=
        (Real.rpow_add hx _ _).symm
      _ = Real.rpow x (p₀' - (1 - p)) := by
        congr 1
        ring
  have hB :
      Real.rpow x p₀' * Real.rpow x (-p) =
        Real.rpow x (p₀' - p) := by
    calc
      Real.rpow x p₀' * Real.rpow x (-p) =
          Real.rpow x (p₀' + (-p)) :=
        (Real.rpow_add hx _ _).symm
      _ = Real.rpow x (p₀' - p) := by
        congr 1
  calc
    Real.rpow x p₀' * |kernel p x| =
        |Real.rpow x p₀'| * |kernel p x| := by
      congr 1
      exact (abs_of_pos (Real.rpow_pos_of_pos hx _)).symm
    _ = |Real.rpow x p₀' * kernel p x| := (abs_mul _ _).symm
    _ = _ := by
      apply congrArg abs
      unfold kernel
      calc
        Real.rpow x p₀' *
              ((Real.rpow x (p - 1) - Real.rpow x (-p)) / (1 - x)) =
            (Real.rpow x p₀' * Real.rpow x (p - 1) -
              Real.rpow x p₀' * Real.rpow x (-p)) / (1 - x) := by
          ring
        _ = _ := by rw [hA, hB]

theorem gap8 (p p₀' L : ℝ)
    (hp : 0 < p) (hp1 : p < 1)
    (h₀ : p₀ p < p₀') (h₁ : p₀' < 1) :
    Tendsto
        (fun x => Real.rpow x p₀' * |kernel p x|)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds L) ↔
      Tendsto
        (fun x =>
          |(Real.rpow x (p₀' - (1 - p)) -
              Real.rpow x (p₀' - p)) / (1 - x)|)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds L) := by
  have heq :
      (fun x => Real.rpow x p₀' * |kernel p x|) =ᶠ[nhdsWithin 0 (Ioi 0)]
        (fun x =>
          |(Real.rpow x (p₀' - (1 - p)) -
              Real.rpow x (p₀' - p)) / (1 - x)|) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact weighted_kernel_eq p p₀' x hx
  constructor <;> intro h
  · exact h.congr' heq
  · exact h.congr' heq.symm

theorem gap9 (p p₀' : ℝ)
    (hp : 0 < p) (hp1 : p < 1)
    (h₀ : p₀ p < p₀') (h₁ : p₀' < 1) :
    Tendsto
      (fun x =>
        |(Real.rpow x (p₀' - (1 - p)) -
            Real.rpow x (p₀' - p)) / (1 - x)|)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hApos : 0 < p₀' - (1 - p) := by
    have hmax : 1 - p ≤ p₀ p := le_max_right _ _
    linarith
  have hBpos : 0 < p₀' - p := by
    have hmax : p ≤ p₀ p := le_max_left _ _
    linarith
  have hA :
      Tendsto (fun x : ℝ => Real.rpow x (p₀' - (1 - p)))
        (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    have hfull :=
      (Real.continuousAt_rpow_const 0 (p₀' - (1 - p))
        (Or.inr hApos.le)).tendsto
    have h := hfull.mono_left
      (show nhdsWithin 0 (Ioi 0) ≤ nhds (0 : ℝ) from inf_le_left)
    simpa [Real.zero_rpow hApos.ne'] using h
  have hB :
      Tendsto (fun x : ℝ => Real.rpow x (p₀' - p))
        (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    have hfull :=
      (Real.continuousAt_rpow_const 0 (p₀' - p)
        (Or.inr hBpos.le)).tendsto
    have h := hfull.mono_left
      (show nhdsWithin 0 (Ioi 0) ≤ nhds (0 : ℝ) from inf_le_left)
    simpa [Real.zero_rpow hBpos.ne'] using h
  have hden :
      Tendsto (fun x : ℝ => 1 - x)
        (nhdsWithin 0 (Ioi 0)) (nhds 1) := by
    have hc : ContinuousAt (fun x : ℝ => (1 : ℝ) - x) 0 :=
      continuousAt_const.sub continuousAt_id
    simpa using hc.tendsto.mono_left
      (show nhdsWithin 0 (Ioi 0) ≤ nhds (0 : ℝ) from inf_le_left)
  have hquot := (hA.sub hB).div hden (by norm_num : (1 : ℝ) ≠ 0)
  simpa using hquot.abs

theorem gap10 (p p₀' : ℝ)
    (hp : 0 < p) (hp1 : p < 1)
    (h₀ : p₀ p < p₀') (h₁ : p₀' < 1) :
    Tendsto
      (fun x => Real.rpow x p₀' * |kernel p x|)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  exact (gap8 p p₀' 0 hp hp1 h₀ h₁).2
    (gap9 p p₀' hp hp1 h₀ h₁)

private theorem kernel_continuousAt_of_pos_of_ne_one
    (p x : ℝ) (hx0 : 0 < x) (hx1 : x ≠ 1) :
    ContinuousAt (kernel p) x := by
  have hA :
      ContinuousAt (fun y : ℝ => Real.rpow y (p - 1)) x :=
    Real.continuousAt_rpow_const x (p - 1) (Or.inl hx0.ne')
  have hB :
      ContinuousAt (fun y : ℝ => Real.rpow y (-p)) x :=
    Real.continuousAt_rpow_const x (-p) (Or.inl hx0.ne')
  have hden : ContinuousAt (fun y : ℝ => 1 - y) x :=
    continuousAt_const.sub continuousAt_id
  unfold kernel
  exact (hA.sub hB).div hden (sub_ne_zero.mpr hx1.symm)

private theorem regularizedKernel_continuousOn_half_one
    (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    ContinuousOn (regularizedKernel p) (Icc (1 / 2 : ℝ) 1) := by
  intro x hx
  apply ContinuousAt.continuousWithinAt
  by_cases hxeq : x = 1
  · subst x
    exact gap4 p hp hp1
  · have hx0 : 0 < x := by linarith [hx.1]
    have hk := kernel_continuousAt_of_pos_of_ne_one p x hx0 hxeq
    apply hk.congr_of_eventuallyEq
    have hmem : ({1}ᶜ : Set ℝ) ∈ nhds x :=
      isOpen_compl_singleton.mem_nhds (by simpa using hxeq)
    filter_upwards [hmem] with y hy
    have hyne : y ≠ 1 := by simpa using hy
    simp [regularizedKernel, hyne]

private theorem kernel_abs_intervalIntegrable_small
    (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    IntervalIntegrable (fun x => |kernel p x|)
      volume (0 : ℝ) (1 / 2) := by
  let M : ℝ → ℝ := fun x =>
    2 * (Real.rpow x (p - 1) + Real.rpow x (-p))
  have hA :
      IntervalIntegrable (fun x : ℝ => Real.rpow x (p - 1))
        volume (0 : ℝ) (1 / 2) :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have hB :
      IntervalIntegrable (fun x : ℝ => Real.rpow x (-p))
        volume (0 : ℝ) (1 / 2) :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have hM : IntervalIntegrable M volume (0 : ℝ) (1 / 2) := by
    exact (hA.add hB).const_mul 2
  rw [intervalIntegrable_iff] at hM ⊢
  refine hM.mono' ?_ ?_
  · apply ContinuousOn.aestronglyMeasurable
    · intro x hx
      rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)] at hx
      have hx0 : 0 < x := hx.1
      have hx1 : x ≠ 1 := by linarith [hx.2]
      exact
        (kernel_continuousAt_of_pos_of_ne_one p x hx0 hx1).abs.continuousWithinAt
    · exact measurableSet_uIoc
  · filter_upwards [ae_restrict_mem measurableSet_uIoc] with x hx
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)] at hx
    have hx0 : 0 < x := hx.1
    have hxhalf : x ≤ 1 / 2 := hx.2
    have hden : 0 < 1 - x := by linarith
    have hdenHalf : 1 / 2 ≤ 1 - x := by linarith
    have hApos : 0 < Real.rpow x (p - 1) :=
      Real.rpow_pos_of_pos hx0 _
    have hBpos : 0 < Real.rpow x (-p) :=
      Real.rpow_pos_of_pos hx0 _
    have hnum :
        |Real.rpow x (p - 1) - Real.rpow x (-p)| ≤
          Real.rpow x (p - 1) + Real.rpow x (-p) := by
      calc
        |Real.rpow x (p - 1) - Real.rpow x (-p)| =
            |Real.rpow x (p - 1) + (-Real.rpow x (-p))| := by ring
        _ ≤ |Real.rpow x (p - 1)| + |-Real.rpow x (-p)| :=
          abs_add_le _ _
        _ = Real.rpow x (p - 1) + Real.rpow x (-p) := by
          rw [abs_of_pos hApos, abs_neg, abs_of_pos hBpos]
    have hdiv :
        |Real.rpow x (p - 1) - Real.rpow x (-p)| / (1 - x) ≤
          2 * (Real.rpow x (p - 1) + Real.rpow x (-p)) := by
      rw [div_le_iff₀ hden]
      nlinarith [add_pos hApos hBpos]
    change ‖|kernel p x|‖ ≤ M x
    rw [Real.norm_eq_abs, abs_of_nonneg (abs_nonneg _), kernel, abs_div,
      abs_of_pos hden]
    exact hdiv

private theorem kernel_abs_intervalIntegrable_large
    (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    IntervalIntegrable (fun x => |kernel p x|)
      volume (1 / 2 : ℝ) 1 := by
  have hreg :
      IntervalIntegrable (fun x => |regularizedKernel p x|)
        volume (1 / 2 : ℝ) 1 :=
    ContinuousOn.intervalIntegrable (by
      rw [uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1)]
      exact (regularizedKernel_continuousOn_half_one p hp hp1).abs)
  rw [intervalIntegrable_iff] at hreg ⊢
  apply hreg.congr
  have hne :
      ∀ᵐ x ∂volume.restrict (Ι (1 / 2 : ℝ) 1), x ≠ 1 := by
    simp [ae_iff, measure_singleton]
  filter_upwards [hne] with x hx
  simp [regularizedKernel, hx]

theorem gap11 (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    IntervalIntegrable (fun x => |kernel p x|)
      volume (0 : ℝ) 1 := by
  exact (kernel_abs_intervalIntegrable_small p hp hp1).trans
    (kernel_abs_intervalIntegrable_large p hp hp1)

theorem gap12 (p x ε : ℝ)
    (hp : 0 < p) (hp1 : p < 1)
    (hx : x ∈ Set.Ioo (0 : ℝ) 1) (hε : 0 ≤ ε) :
    |Real.rpow x (p - 1) - Real.rpow x (-p)| /
        Real.rpow (1 - x) (1 - ε) ≤
      |Real.rpow x (p - 1) - Real.rpow x (-p)| / (1 - x) := by
  have hbase0 : 0 < 1 - x := sub_pos.mpr hx.2
  have hbase1 : 1 - x ≤ 1 := by linarith [hx.1]
  have hpow :
      1 - x ≤ Real.rpow (1 - x) (1 - ε) := by
    calc
      1 - x = Real.rpow (1 - x) 1 := (Real.rpow_one _).symm
      _ ≤ Real.rpow (1 - x) (1 - ε) :=
        Real.rpow_le_rpow_of_exponent_ge hbase0 hbase1 (by linarith)
  exact div_le_div_of_nonneg_left (abs_nonneg _) hbase0 hpow

private theorem I_integrand_aestronglyMeasurable (p ε : ℝ) :
    AEStronglyMeasurable
      (fun x : ℝ =>
        (Real.rpow x (p - 1) - Real.rpow x (-p)) /
          Real.rpow (1 - x) (1 - ε))
      (volume.restrict (Ι (0 : ℝ) 1)) := by
  apply Measurable.aestronglyMeasurable
  measurability

theorem gap13 (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    ContinuousOn (I p) (Set.Ico (0 : ℝ) 1) := by
  intro ε hε
  let F : ℝ → ℝ → ℝ := fun η x =>
    (Real.rpow x (p - 1) - Real.rpow x (-p)) /
      Real.rpow (1 - x) (1 - η)
  change ContinuousWithinAt
    (fun η => ∫ x in (0 : ℝ)..1, F η x) (Ico 0 1) ε
  apply intervalIntegral.continuousWithinAt_of_dominated_interval
      (bound := fun x => |kernel p x|)
  · exact Filter.Eventually.of_forall (fun η =>
      I_integrand_aestronglyMeasurable p η)
  · filter_upwards [self_mem_nhdsWithin] with η hη
    have hη0 : 0 ≤ η := hη.1
    have hne0 : ∀ᵐ x : ℝ ∂volume, x ≠ 0 := by
      simp [ae_iff, measure_singleton]
    have hne1 : ∀ᵐ x : ℝ ∂volume, x ≠ 1 := by
      simp [ae_iff, measure_singleton]
    filter_upwards [hne0, hne1] with x hx0 hx1 hxmem
    rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hxmem
    have hxIoo : x ∈ Ioo (0 : ℝ) 1 :=
      ⟨hxmem.1, lt_of_le_of_ne hxmem.2 hx1⟩
    have hbase : 0 < 1 - x := sub_pos.mpr hxIoo.2
    change ‖F η x‖ ≤ |kernel p x|
    have hdenabs :
        |Real.rpow (1 - x) (1 - η)| =
          Real.rpow (1 - x) (1 - η) :=
      abs_of_pos (Real.rpow_pos_of_pos hbase _)
    have hbaseabs : |1 - x| = 1 - x := abs_of_pos hbase
    rw [Real.norm_eq_abs, abs_div, hdenabs, kernel, abs_div, hbaseabs]
    exact gap12 p x η hp hp1 hxIoo hη0
  · exact gap11 p hp hp1
  · have hne0 : ∀ᵐ x : ℝ ∂volume, x ≠ 0 := by
      simp [ae_iff, measure_singleton]
    have hne1 : ∀ᵐ x : ℝ ∂volume, x ≠ 1 := by
      simp [ae_iff, measure_singleton]
    filter_upwards [hne0, hne1] with x hx0 hx1 hxmem
    rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hxmem
    have hxIoo : x ∈ Ioo (0 : ℝ) 1 :=
      ⟨hxmem.1, lt_of_le_of_ne hxmem.2 hx1⟩
    have hbase : 0 < 1 - x := sub_pos.mpr hxIoo.2
    have hpow :
        Continuous (fun η : ℝ => Real.rpow (1 - x) (1 - η)) :=
      (Real.continuous_const_rpow hbase.ne').comp
        (continuous_const.sub continuous_id)
    have hcont :
        Continuous (fun η : ℝ => F η x) := by
      apply continuous_const.div hpow
      intro η
      exact (Real.rpow_pos_of_pos hbase _).ne'
    exact hcont.continuousAt.continuousWithinAt

private theorem betaKernel_intervalIntegrable
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable
      (fun x : ℝ =>
        Real.rpow x (a - 1) * Real.rpow (1 - x) (b - 1))
      volume (0 : ℝ) 1 := by
  have hc :=
    Complex.betaIntegral_convergent
      (u := (a : ℂ)) (v := (b : ℂ)) (by simpa) (by simpa)
  rw [intervalIntegrable_iff] at hc ⊢
  have hr :
      IntegrableOn
        (fun x : ℝ =>
          (((x : ℂ) ^ ((a : ℂ) - 1) *
            (1 - (x : ℂ)) ^ ((b : ℂ) - 1)).re))
        (Ι (0 : ℝ) 1) volume :=
    hc.re
  refine hr.congr_fun ?_ measurableSet_uIoc
  intro x hx
  rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
  have hx0 : 0 ≤ x := hx.1.le
  have hx1 : 0 ≤ 1 - x := sub_nonneg.mpr hx.2
  change
    (((x : ℂ) ^ ((a : ℂ) - 1) *
      (1 - (x : ℂ)) ^ ((b : ℂ) - 1)).re) =
        Real.rpow x (a - 1) * Real.rpow (1 - x) (b - 1)
  have haexp : (a : ℂ) - 1 = ((a - 1 : ℝ) : ℂ) := by push_cast; rfl
  have hbexp : (b : ℂ) - 1 = ((b - 1 : ℝ) : ℂ) := by push_cast; rfl
  rw [haexp, hbexp, ← Complex.ofReal_cpow hx0,
    show 1 - (x : ℂ) = ((1 - x : ℝ) : ℂ) by push_cast; rfl,
    ← Complex.ofReal_cpow hx1, ← Complex.ofReal_mul]
  simp

theorem gap14 (p ε : ℝ)
    (hp : 0 < p) (hp1 : p < 1) (hε : 0 < ε) :
    I p ε = betaFn p ε - betaFn (1 - p) ε := by
  have hB1 := betaKernel_intervalIntegrable p ε hp hε
  have hB2 :=
    betaKernel_intervalIntegrable (1 - p) ε (by linarith) hε
  rw [betaFn, betaFn, ← intervalIntegral.integral_sub hB1 hB2]
  unfold I
  apply intervalIntegral.integral_congr_ae
  have hne0 : ∀ᵐ x : ℝ ∂volume, x ≠ 0 := by
    simp [ae_iff, measure_singleton]
  have hne1 : ∀ᵐ x : ℝ ∂volume, x ≠ 1 := by
    simp [ae_iff, measure_singleton]
  filter_upwards [hne0, hne1] with x hx0 hx1 hxmem
  rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hxmem
  have hxpos : 0 < x := hxmem.1
  have hbase : 0 < 1 - x :=
    sub_pos.mpr (lt_of_le_of_ne hxmem.2 hx1)
  have hneg :
      Real.rpow (1 - x) (ε - 1) =
        (Real.rpow (1 - x) (1 - ε))⁻¹ := by
    calc
      Real.rpow (1 - x) (ε - 1) =
          Real.rpow (1 - x) (-(1 - ε)) := by
        congr 1
        ring
      _ = (Real.rpow (1 - x) (1 - ε))⁻¹ :=
        Real.rpow_neg hbase.le (1 - ε)
  rw [show (1 - p) - 1 = -p by ring, hneg]
  ring

theorem gap15 (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    (∫ x in (0 : ℝ)..1, kernel p x) = I p 0 := by
  unfold kernel I
  apply intervalIntegral.integral_congr
  intro x hx
  have hone :
      Real.rpow (1 - x) 1 = 1 - x := Real.rpow_one _
  change
    (Real.rpow x (p - 1) - Real.rpow x (-p)) / (1 - x) =
      (Real.rpow x (p - 1) - Real.rpow x (-p)) /
        Real.rpow (1 - x) (1 - 0)
  rw [sub_zero]
  congr 1
  exact hone.symm

theorem gap16 (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    Tendsto (I p) (nhdsWithin 0 (Set.Ioi 0)) (nhds (I p 0)) := by
  have hcont :=
    gap13 p hp hp1 0 ⟨le_rfl, zero_lt_one⟩
  have hsmall :
      Tendsto (I p) (nhdsWithin 0 (Ioo 0 1)) (nhds (I p 0)) :=
    hcont.mono_left (nhdsWithin_mono 0 (by
      intro x hx
      exact ⟨hx.1.le, hx.2⟩))
  have hfilter :
      nhdsWithin (0 : ℝ) (Ioo 0 1) = nhdsWithin 0 (Ioi 0) := by
    have h :=
      nhdsWithin_inter_of_mem
        (a := (0 : ℝ)) (s := Iio 1) (t := Ioi 0)
        (mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds zero_lt_one))
    have hset : Iio (1 : ℝ) ∩ Ioi 0 = Ioo 0 1 := by
      ext x
      simp [and_comm]
    rw [hset] at h
    exact h
  rw [hfilter] at hsmall
  exact hsmall

theorem gap17 (p L : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    Tendsto (I p) (nhdsWithin 0 (Set.Ioi 0)) (nhds L) ↔
      Tendsto (fun ε => betaFn p ε - betaFn (1 - p) ε)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds L) := by
  have heq :
      I p =ᶠ[nhdsWithin 0 (Ioi 0)]
        (fun ε => betaFn p ε - betaFn (1 - p) ε) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact gap14 p ε hp hp1 hε
  constructor <;> intro h
  · exact h.congr' heq
  · exact h.congr' heq.symm

theorem gap18 (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    Tendsto (fun ε => betaFn p ε - betaFn (1 - p) ε)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (∫ x in (0 : ℝ)..1, kernel p x)) := by
  have h :=
    (gap17 p (I p 0) hp hp1).1 (gap16 p hp hp1)
  rw [← gap15 p hp hp1] at h
  exact h

private theorem betaFn_eq_gamma
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    betaFn a b =
      Real.Gamma a * Real.Gamma b / Real.Gamma (a + b) := by
  apply Complex.ofReal_injective
  rw [betaFn, ← intervalIntegral.integral_ofReal]
  have hIntegral :
      (∫ x in (0 : ℝ)..1,
        (((Real.rpow x (a - 1) *
          Real.rpow (1 - x) (b - 1) : ℝ) : ℂ))) =
        Complex.betaIntegral (a : ℂ) (b : ℂ) := by
    unfold Complex.betaIntegral
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
    have hx0 : 0 ≤ x := hx.1
    have hx1 : 0 ≤ 1 - x := sub_nonneg.mpr hx.2
    change
      (((Real.rpow x (a - 1) *
        Real.rpow (1 - x) (b - 1) : ℝ) : ℂ)) =
        (x : ℂ) ^ ((a : ℂ) - 1) *
          (1 - (x : ℂ)) ^ ((b : ℂ) - 1)
    rw [Complex.ofReal_mul]
    congr 1
    · calc
        ((Real.rpow x (a - 1) : ℝ) : ℂ) =
            (x : ℂ) ^ ((a - 1 : ℝ) : ℂ) :=
          Complex.ofReal_cpow hx0 (a - 1)
        _ = (x : ℂ) ^ ((a : ℂ) - 1) := by push_cast; rfl
    · calc
        ((Real.rpow (1 - x) (b - 1) : ℝ) : ℂ) =
            ((1 - x : ℝ) : ℂ) ^ ((b - 1 : ℝ) : ℂ) :=
          Complex.ofReal_cpow hx1 (b - 1)
        _ = (1 - (x : ℂ)) ^ ((b : ℂ) - 1) := by push_cast; rfl
  rw [hIntegral,
    Complex.betaIntegral_eq_Gamma_mul_div (a : ℂ) (b : ℂ)
      (by simpa) (by simpa)]
  simp only [← Complex.Gamma_ofReal, Complex.ofReal_mul,
    Complex.ofReal_div, Complex.ofReal_add]

private def gammaNumerator (p ε : ℝ) : ℝ :=
  Real.Gamma p * Real.Gamma (1 - p + ε) -
    Real.Gamma (1 - p) * Real.Gamma (p + ε)

private def reflectedExpression (p ε : ℝ) : ℝ :=
  1 / (Real.Gamma p * Real.Gamma (1 - p) * Real.Gamma 1) *
    (Real.Gamma ε * Real.Gamma (1 - ε) * gammaNumerator p ε)

private def sineExpression (p ε : ℝ) : ℝ :=
  Real.sin (Real.pi * p) *
    (gammaNumerator p ε / Real.sin (Real.pi * ε))

private def gammaRatio (p ε : ℝ) : ℝ :=
  (Real.Gamma p * Real.Gamma (1 - p) * Real.Gamma 1) /
    (Real.Gamma (1 - ε) * Real.Gamma (p + ε) *
      Real.Gamma (1 - p + ε))

private theorem gamma_continuousAt_pos (a : ℝ) (ha : 0 < a) :
    ContinuousAt Real.Gamma a := by
  exact (Real.differentiableAt_Gamma (by
    intro m hm
    have hm0 : (0 : ℝ) ≤ m := by positivity
    linarith)).continuousAt

private theorem beta_difference_eq_gammaExpression
    (p ε : ℝ) (hp : 0 < p) (hp1 : p < 1) (hε : 0 < ε) :
    betaFn p ε - betaFn (1 - p) ε = gammaExpression p ε := by
  rw [betaFn_eq_gamma p ε hp hε,
    betaFn_eq_gamma (1 - p) ε (by linarith) hε]
  have hA : Real.Gamma (p + ε) ≠ 0 :=
    (Real.Gamma_pos_of_pos (add_pos hp hε)).ne'
  have hB : Real.Gamma (1 - p + ε) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by linarith)).ne'
  unfold gammaExpression
  field_simp [hA, hB]

theorem gap19 (p L : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    Tendsto (fun ε => betaFn p ε - betaFn (1 - p) ε)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds L) ↔
      Tendsto (gammaExpression p)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds L) := by
  have heq :
      (fun ε => betaFn p ε - betaFn (1 - p) ε) =ᶠ[nhdsWithin 0 (Ioi 0)]
        gammaExpression p := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact beta_difference_eq_gammaExpression p ε hp hp1 hε
  constructor <;> intro h
  · exact h.congr' heq
  · exact h.congr' heq.symm

private theorem gammaRatio_tendsto_one
    (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    Tendsto (gammaRatio p) (nhdsWithin 0 (Ioi 0)) (nhds 1) := by
  have hinner1 :
      Tendsto (fun ε : ℝ => (1 : ℝ) - ε)
        (nhds 0) (nhds 1) := by
    simpa using
      (show ContinuousAt (fun ε : ℝ => (1 : ℝ) - ε) 0 from
        continuousAt_const.sub continuousAt_id).tendsto
  have hinnerp :
      Tendsto (fun ε : ℝ => p + ε)
        (nhds 0) (nhds p) := by
    simpa using
      (show ContinuousAt (fun ε : ℝ => p + ε) 0 from
        continuousAt_const.add continuousAt_id).tendsto
  have hinner1p :
      Tendsto (fun ε : ℝ => 1 - p + ε)
        (nhds 0) (nhds (1 - p)) := by
    simpa using
      (show ContinuousAt (fun ε : ℝ => 1 - p + ε) 0 from
        continuousAt_const.add continuousAt_id).tendsto
  have hG1 :
      Tendsto (fun ε : ℝ => Real.Gamma (1 - ε))
        (nhds 0) (nhds (Real.Gamma 1)) :=
    (gamma_continuousAt_pos 1 zero_lt_one).tendsto.comp
      hinner1
  have hGp :
    Tendsto (fun ε : ℝ => Real.Gamma (p + ε))
        (nhds 0) (nhds (Real.Gamma p)) :=
    (gamma_continuousAt_pos p hp).tendsto.comp
      hinnerp
  have hG1p :
    Tendsto (fun ε : ℝ => Real.Gamma (1 - p + ε))
        (nhds 0) (nhds (Real.Gamma (1 - p))) :=
    (gamma_continuousAt_pos (1 - p) (by linarith)).tendsto.comp
      hinner1p
  have hden :=
    (hG1.mul hGp).mul hG1p
  have hden0 :
      Real.Gamma 1 * Real.Gamma p * Real.Gamma (1 - p) ≠ 0 := by
    exact mul_ne_zero
      (mul_ne_zero (Real.Gamma_pos_of_pos zero_lt_one).ne'
        (Real.Gamma_pos_of_pos hp).ne')
      (Real.Gamma_pos_of_pos (by linarith)).ne'
  have hfull :
      Tendsto
        (fun ε : ℝ =>
          (Real.Gamma p * Real.Gamma (1 - p) * Real.Gamma 1) /
            (Real.Gamma (1 - ε) * Real.Gamma (p + ε) *
              Real.Gamma (1 - p + ε)))
        (nhds 0)
        (nhds
          ((Real.Gamma p * Real.Gamma (1 - p) * Real.Gamma 1) /
            (Real.Gamma 1 * Real.Gamma p * Real.Gamma (1 - p)))) :=
    tendsto_const_nhds.div hden hden0
  have hval :
      (Real.Gamma p * Real.Gamma (1 - p) * Real.Gamma 1) /
          (Real.Gamma 1 * Real.Gamma p * Real.Gamma (1 - p)) = 1 := by
    have hGp0 : Real.Gamma p ≠ 0 :=
      (Real.Gamma_pos_of_pos hp).ne'
    have hG1p0 : Real.Gamma (1 - p) ≠ 0 :=
      (Real.Gamma_pos_of_pos (by linarith)).ne'
    rw [Real.Gamma_one]
    field_simp [hGp0, hG1p0]
  have hfull' :
      Tendsto (gammaRatio p) (nhds 0) (nhds 1) := by
    rw [hval] at hfull
    change
      Tendsto
        (fun ε : ℝ =>
          (Real.Gamma p * Real.Gamma (1 - p) * Real.Gamma 1) /
            (Real.Gamma (1 - ε) * Real.Gamma (p + ε) *
              Real.Gamma (1 - p + ε)))
        (nhds 0) (nhds 1)
    exact hfull
  exact hfull'.mono_left
    (show nhdsWithin 0 (Ioi 0) ≤ nhds (0 : ℝ) from inf_le_left)

private theorem gammaExpression_eq_ratio_mul
    (p ε : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (hε : 0 < ε) (hε1 : ε < 1) :
    gammaExpression p ε =
      gammaRatio p ε * reflectedExpression p ε := by
  have hGp : Real.Gamma p ≠ 0 :=
    (Real.Gamma_pos_of_pos hp).ne'
  have hG1p : Real.Gamma (1 - p) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by linarith)).ne'
  have hG1 : Real.Gamma 1 ≠ 0 :=
    (Real.Gamma_pos_of_pos zero_lt_one).ne'
  have hGe : Real.Gamma ε ≠ 0 :=
    (Real.Gamma_pos_of_pos hε).ne'
  have hG1e : Real.Gamma (1 - ε) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by linarith)).ne'
  have hGpe : Real.Gamma (p + ε) ≠ 0 :=
    (Real.Gamma_pos_of_pos (add_pos hp hε)).ne'
  have hG1pe : Real.Gamma (1 - p + ε) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by linarith)).ne'
  unfold gammaExpression gammaRatio reflectedExpression gammaNumerator
  field_simp [hGp, hG1p, hG1, hGe, hG1e, hGpe, hG1pe]

theorem gap20 (p L : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    Tendsto (gammaExpression p)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds L) ↔
      Tendsto
        (fun ε =>
          1 / (Real.Gamma p * Real.Gamma (1 - p) * Real.Gamma 1) *
            (Real.Gamma ε * Real.Gamma (1 - ε) *
              (Real.Gamma p * Real.Gamma (1 - p + ε) -
                Real.Gamma (1 - p) * Real.Gamma (p + ε))))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds L) := by
  change Tendsto (gammaExpression p) (nhdsWithin 0 (Ioi 0)) (nhds L) ↔
    Tendsto (reflectedExpression p) (nhdsWithin 0 (Ioi 0)) (nhds L)
  have hlt : ∀ᶠ ε : ℝ in nhdsWithin 0 (Ioi 0), ε < 1 :=
    (show ∀ᶠ ε : ℝ in nhds (0 : ℝ), ε < 1 from
      Iio_mem_nhds zero_lt_one).filter_mono inf_le_left
  have hpos : ∀ᶠ ε : ℝ in nhdsWithin 0 (Ioi 0), 0 < ε :=
    self_mem_nhdsWithin
  have heq :
      gammaExpression p =ᶠ[nhdsWithin 0 (Ioi 0)]
        fun ε => gammaRatio p ε * reflectedExpression p ε := by
    filter_upwards [hpos, hlt] with ε hε hε1
    exact gammaExpression_eq_ratio_mul p ε hp hp1 hε hε1
  have hratio := gammaRatio_tendsto_one p hp hp1
  have hratioInv :
      Tendsto (fun ε => (gammaRatio p ε)⁻¹)
        (nhdsWithin 0 (Ioi 0)) (nhds 1) := by
    simpa using hratio.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  have hratioNe :
      ∀ᶠ ε in nhdsWithin 0 (Ioi 0), gammaRatio p ε ≠ 0 :=
    (hratio.eventually (compl_singleton_mem_nhds_iff.mpr one_ne_zero))
  have heqInv :
      reflectedExpression p =ᶠ[nhdsWithin 0 (Ioi 0)]
        fun ε => (gammaRatio p ε)⁻¹ * gammaExpression p ε := by
    filter_upwards [heq, hratioNe] with ε he hne
    rw [he]
    field_simp
  constructor
  · intro hgamma
    have h := hratioInv.mul hgamma
    have hlim :
        Tendsto (fun ε => (gammaRatio p ε)⁻¹ * gammaExpression p ε)
          (nhdsWithin 0 (Ioi 0)) (nhds L) := by
      convert h using 1 <;> simp
    exact hlim.congr' heqInv.symm
  · intro href
    have h := hratio.mul href
    have hlim :
        Tendsto (fun ε => gammaRatio p ε * reflectedExpression p ε)
          (nhdsWithin 0 (Ioi 0)) (nhds L) := by
      convert h using 1 <;> simp
    exact hlim.congr' heq.symm

private theorem reflectedExpression_eq_sineExpression
    (p ε : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (hε : 0 < ε) (hε1 : ε < 1) :
    reflectedExpression p ε = sineExpression p ε := by
  have hsinp : Real.sin (Real.pi * p) ≠ 0 := by
    have harg0 : 0 < Real.pi * p := mul_pos Real.pi_pos hp
    have harg1 : Real.pi * p < Real.pi := by nlinarith [Real.pi_pos]
    exact (Real.sin_pos_of_pos_of_lt_pi harg0 harg1).ne'
  have hsine : Real.sin (Real.pi * ε) ≠ 0 := by
    have harg0 : 0 < Real.pi * ε := mul_pos Real.pi_pos hε
    have harg1 : Real.pi * ε < Real.pi := by nlinarith [Real.pi_pos]
    exact (Real.sin_pos_of_pos_of_lt_pi harg0 harg1).ne'
  unfold reflectedExpression sineExpression
  rw [Real.Gamma_one, Real.Gamma_mul_Gamma_one_sub p,
    Real.Gamma_mul_Gamma_one_sub ε]
  unfold gammaNumerator
  field_simp [hsinp, hsine, Real.pi_ne_zero]

theorem gap21 (p L : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    Tendsto (fun ε => betaFn p ε - betaFn (1 - p) ε)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds L) ↔
      Tendsto
        (fun ε =>
          Real.sin (Real.pi * p) *
            ((Real.Gamma p * Real.Gamma (1 - p + ε) -
                Real.Gamma (1 - p) * Real.Gamma (p + ε)) /
              Real.sin (Real.pi * ε)))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds L) := by
  change Tendsto (fun ε => betaFn p ε - betaFn (1 - p) ε)
      (nhdsWithin 0 (Ioi 0)) (nhds L) ↔
    Tendsto (sineExpression p) (nhdsWithin 0 (Ioi 0)) (nhds L)
  have hlt : ∀ᶠ ε : ℝ in nhdsWithin 0 (Ioi 0), ε < 1 :=
    (show ∀ᶠ ε : ℝ in nhds (0 : ℝ), ε < 1 from
      Iio_mem_nhds zero_lt_one).filter_mono inf_le_left
  have hpos : ∀ᶠ ε : ℝ in nhdsWithin 0 (Ioi 0), 0 < ε :=
    self_mem_nhdsWithin
  have heq :
      reflectedExpression p =ᶠ[nhdsWithin 0 (Ioi 0)] sineExpression p := by
    filter_upwards [hpos, hlt] with ε hε hε1
    exact reflectedExpression_eq_sineExpression p ε hp hp1 hε hε1
  have href :
      Tendsto (reflectedExpression p) (nhdsWithin 0 (Ioi 0)) (nhds L) ↔
        Tendsto (sineExpression p) (nhdsWithin 0 (Ioi 0)) (nhds L) := by
    constructor <;> intro h
    · exact h.congr' heq
    · exact h.congr' heq.symm
  exact (gap19 p L hp hp1).trans ((gap20 p L hp hp1).trans href)

private theorem gamma_differentiableAt_pos (a : ℝ) (ha : 0 < a) :
    DifferentiableAt ℝ Real.Gamma a := by
  exact Real.differentiableAt_Gamma (by
    intro m hm
    have hm0 : (0 : ℝ) ≤ m := by positivity
    linarith)

theorem gap22 (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    Tendsto (fun ε => betaFn p ε - betaFn (1 - p) ε)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (Real.sin (Real.pi * p) / Real.pi *
          (Real.Gamma p * deriv Real.Gamma (1 - p) -
            Real.Gamma (1 - p) * deriv Real.Gamma p))) := by
  let D :=
    Real.Gamma p * deriv Real.Gamma (1 - p) -
      Real.Gamma (1 - p) * deriv Real.Gamma p
  have hinner1p :
      HasDerivAt (fun ε : ℝ => 1 - p + ε) 1 0 := by
    convert (hasDerivAt_const (0 : ℝ) (1 - p)).add
      (hasDerivAt_id (𝕜 := ℝ) 0) using 1 <;> simp
  have hinnerp :
      HasDerivAt (fun ε : ℝ => p + ε) 1 0 := by
    convert (hasDerivAt_const (0 : ℝ) p).add
      (hasDerivAt_id (𝕜 := ℝ) 0) using 1 <;> simp
  have hG1p :
      HasDerivAt (fun ε : ℝ => Real.Gamma (1 - p + ε))
        (deriv Real.Gamma (1 - p)) 0 := by
    have hbase :
        HasDerivAt Real.Gamma (deriv Real.Gamma (1 - p))
          (1 - p + 0) := by
      simpa using
        (gamma_differentiableAt_pos (1 - p) (by linarith)).hasDerivAt
    simpa only [Function.comp_apply, mul_one] using
      hbase.comp 0 hinner1p
  have hGp :
      HasDerivAt (fun ε : ℝ => Real.Gamma (p + ε))
        (deriv Real.Gamma p) 0 := by
    have hbase :
        HasDerivAt Real.Gamma (deriv Real.Gamma p) (p + 0) := by
      simpa using (gamma_differentiableAt_pos p hp).hasDerivAt
    simpa only [Function.comp_apply, mul_one] using
      hbase.comp 0 hinnerp
  have hN :
      HasDerivAt (gammaNumerator p) D 0 := by
    have h :=
      ((hasDerivAt_const (0 : ℝ) (Real.Gamma p)).mul hG1p).sub
        ((hasDerivAt_const (0 : ℝ) (Real.Gamma (1 - p))).mul hGp)
    unfold gammaNumerator D
    convert h using 1 <;> ring
  have hN0 : gammaNumerator p 0 = 0 := by
    unfold gammaNumerator
    ring
  have hNslope :
      Tendsto (fun ε : ℝ => gammaNumerator p ε / ε)
        (nhdsWithin 0 (Ioi 0)) (nhds D) := by
    simpa only [zero_add, hN0, sub_zero, smul_eq_mul, div_eq_mul_inv,
      mul_comm] using hN.tendsto_slope_zero_right
  have harg :
      HasDerivAt (fun ε : ℝ => Real.pi * ε) Real.pi 0 := by
    simpa only [id_eq, mul_one] using
      (hasDerivAt_id (𝕜 := ℝ) 0).const_mul Real.pi
  have hsin :
      HasDerivAt (fun ε : ℝ => Real.sin (Real.pi * ε)) Real.pi 0 := by
    have hbase :
        HasDerivAt Real.sin (Real.cos 0) (Real.pi * 0) := by
      simpa using Real.hasDerivAt_sin 0
    simpa only [Function.comp_apply, Real.cos_zero, one_mul] using
      hbase.comp 0 harg
  have hslopeSin :
      Tendsto (fun ε : ℝ => Real.sin (Real.pi * ε) / ε)
        (nhdsWithin 0 (Ioi 0)) (nhds Real.pi) := by
    simpa only [zero_add, mul_zero, Real.sin_zero, sub_zero, smul_eq_mul,
      div_eq_mul_inv, mul_comm] using hsin.tendsto_slope_zero_right
  have hquot :
      Tendsto
        (fun ε : ℝ =>
          (gammaNumerator p ε / ε) /
            (Real.sin (Real.pi * ε) / ε))
        (nhdsWithin 0 (Ioi 0)) (nhds (D / Real.pi)) :=
    hNslope.div hslopeSin Real.pi_ne_zero
  have hpos :
      ∀ᶠ ε : ℝ in nhdsWithin 0 (Ioi 0), 0 < ε :=
    self_mem_nhdsWithin
  have hlt :
      ∀ᶠ ε : ℝ in nhdsWithin 0 (Ioi 0), ε < 1 :=
    (show ∀ᶠ ε : ℝ in nhds (0 : ℝ), ε < 1 from
      Iio_mem_nhds zero_lt_one).filter_mono inf_le_left
  have heq :
      (fun ε : ℝ =>
        (gammaNumerator p ε / ε) /
          (Real.sin (Real.pi * ε) / ε)) =ᶠ[nhdsWithin 0 (Ioi 0)]
        fun ε => gammaNumerator p ε / Real.sin (Real.pi * ε) := by
    filter_upwards [hpos, hlt] with ε hε hε1
    have hε0 : ε ≠ 0 := hε.ne'
    have hsin0 : Real.sin (Real.pi * ε) ≠ 0 := by
      have harg0 : 0 < Real.pi * ε := mul_pos Real.pi_pos hε
      have harg1 : Real.pi * ε < Real.pi := by
        nlinarith [Real.pi_pos]
      exact (Real.sin_pos_of_pos_of_lt_pi harg0 harg1).ne'
    field_simp [hε0, hsin0]
  have hquot' :
      Tendsto
        (fun ε : ℝ =>
          gammaNumerator p ε / Real.sin (Real.pi * ε))
        (nhdsWithin 0 (Ioi 0)) (nhds (D / Real.pi)) :=
    hquot.congr' heq
  have hsine :
      Tendsto (sineExpression p)
        (nhdsWithin 0 (Ioi 0))
        (nhds (Real.sin (Real.pi * p) / Real.pi * D)) := by
    have hconst :
        Tendsto (fun _ : ℝ => Real.sin (Real.pi * p))
          (nhdsWithin 0 (Ioi 0)) (nhds (Real.sin (Real.pi * p))) :=
      tendsto_const_nhds
    have hmul := hconst.mul hquot'
    unfold sineExpression
    convert hmul using 1 <;> ring
  exact (gap21 p
    (Real.sin (Real.pi * p) / Real.pi *
      (Real.Gamma p * deriv Real.Gamma (1 - p) -
        Real.Gamma (1 - p) * deriv Real.Gamma p)) hp hp1).2
    (by simpa only [D] using hsine)

theorem gap23 (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    Real.Gamma p * deriv Real.Gamma (1 - p) -
        Real.Gamma (1 - p) * deriv Real.Gamma p =
      -deriv (fun q => Real.Gamma q * Real.Gamma (1 - q)) p := by
  have hGp :
      HasDerivAt Real.Gamma (deriv Real.Gamma p) p :=
    (gamma_differentiableAt_pos p hp).hasDerivAt
  have hinner :
      HasDerivAt (fun q : ℝ => 1 - q) (-1) p := by
    convert (hasDerivAt_const p (1 : ℝ)).sub
      (hasDerivAt_id (𝕜 := ℝ) p) using 1 <;> norm_num
  have hG1p :
      HasDerivAt (fun q : ℝ => Real.Gamma (1 - q))
        (-(deriv Real.Gamma (1 - p))) p := by
    have hbase :
        HasDerivAt Real.Gamma (deriv Real.Gamma (1 - p)) (1 - p) :=
      (gamma_differentiableAt_pos (1 - p) (by linarith)).hasDerivAt
    convert hbase.comp p hinner using 1 <;> simp
  have hprod :
      HasDerivAt (fun q : ℝ => Real.Gamma q * Real.Gamma (1 - q))
        (deriv Real.Gamma p * Real.Gamma (1 - p) +
          Real.Gamma p * (-(deriv Real.Gamma (1 - p)))) p := by
    convert hGp.mul hG1p using 1
  rw [hprod.deriv]
  ring

theorem gap24 (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    -deriv (fun q => Real.Gamma q * Real.Gamma (1 - q)) p =
      -deriv (fun q => Real.pi / Real.sin (q * Real.pi)) p := by
  have heq :
      (fun q : ℝ => Real.Gamma q * Real.Gamma (1 - q)) =ᶠ[nhds p]
        fun q => Real.pi / Real.sin (q * Real.pi) := by
    filter_upwards with q
    rw [Real.Gamma_mul_Gamma_one_sub]
    congr 2
    ring
  rw [heq.deriv_eq]

theorem gap25 (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    -deriv (fun q => Real.pi / Real.sin (q * Real.pi)) p =
      Real.pi ^ 2 * Real.cos (p * Real.pi) /
        Real.sin (p * Real.pi) ^ 2 := by
  have hsin0 : Real.sin (p * Real.pi) ≠ 0 := by
    have harg0 : 0 < p * Real.pi := mul_pos hp Real.pi_pos
    have harg1 : p * Real.pi < Real.pi := by
      nlinarith [Real.pi_pos]
    exact (Real.sin_pos_of_pos_of_lt_pi harg0 harg1).ne'
  have harg :
      HasDerivAt (fun q : ℝ => q * Real.pi) Real.pi p := by
    simpa only [id_eq, one_mul] using
      (hasDerivAt_id (𝕜 := ℝ) p).mul_const Real.pi
  have hsin :
      HasDerivAt (fun q : ℝ => Real.sin (q * Real.pi))
        (Real.cos (p * Real.pi) * Real.pi) p := by
    simpa only [Function.comp_apply] using
      (Real.hasDerivAt_sin (p * Real.pi)).comp p harg
  have hquot :
      HasDerivAt (fun q : ℝ => Real.pi / Real.sin (q * Real.pi))
        ((0 * Real.sin (p * Real.pi) -
            Real.pi * (Real.cos (p * Real.pi) * Real.pi)) /
          Real.sin (p * Real.pi) ^ 2) p := by
    convert (hasDerivAt_const p Real.pi).div hsin hsin0 using 1
  rw [hquot.deriv]
  ring

theorem gap26 (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    Real.Gamma p * deriv Real.Gamma (1 - p) -
        Real.Gamma (1 - p) * deriv Real.Gamma p =
      Real.pi ^ 2 * Real.cos (p * Real.pi) /
        Real.sin (p * Real.pi) ^ 2 := by
  calc
    Real.Gamma p * deriv Real.Gamma (1 - p) -
        Real.Gamma (1 - p) * deriv Real.Gamma p =
      -deriv (fun q => Real.Gamma q * Real.Gamma (1 - q)) p :=
        gap23 p hp hp1
    _ = -deriv (fun q => Real.pi / Real.sin (q * Real.pi)) p :=
      gap24 p hp hp1
    _ = Real.pi ^ 2 * Real.cos (p * Real.pi) /
        Real.sin (p * Real.pi) ^ 2 :=
      gap25 p hp hp1

theorem gap27 (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    (∫ x in (0 : ℝ)..1, kernel p x) =
      Real.pi * (Real.cos (p * Real.pi) / Real.sin (p * Real.pi)) := by
  rw [intervalIntegral.integral_of_le zero_le_one,
    MeasureTheory.integral_Ioc_eq_integral_Ioo,
    kernel_integral_closed p hp hp1]
  ring

end

end ProofGap.Exercise3866
