import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Complex.OperatorNorm
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.NumberTheory.Bernoulli
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Basic

namespace ProofGap.Exercise2892

noncomputable section

open scoped BigOperators

def coth (x : ℝ) : ℝ :=
  Real.cosh x / Real.sinh x

def sinhTerm (x : ℝ) (n : ℕ) : ℝ :=
  x ^ (2 * n + 1) / (Nat.factorial (2 * n + 1) : ℝ)

def coshTerm (x : ℝ) (n : ℕ) : ℝ :=
  x ^ (2 * n) / (Nat.factorial (2 * n) : ℝ)

def coshTail (x : ℝ) : ℝ :=
  ∑' k : ℕ, x ^ (2 * (k + 1)) /
    (Nat.factorial (2 * (k + 1)) : ℝ)

def sechMaclaurinTerm (x : ℝ) (n : ℕ) : ℝ :=
  iteratedDeriv n (fun y : ℝ => 1 / Real.cosh y) 0 /
    (Nat.factorial n : ℝ) * x ^ n

def bernoulliMagnitude (n : ℕ) : ℝ :=
  |(((bernoulli (2 * n) : ℚ) : ℝ))|

def B (n : ℕ) : ℝ :=
  bernoulliMagnitude n

def tanhCoefficient (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ (n + 1) * (2 : ℝ) ^ (2 * n) *
    ((2 : ℝ) ^ (2 * n) - 1) * B n /
      (Nat.factorial (2 * n) : ℝ)

def tanhSeriesTerm (x : ℝ) (k : ℕ) : ℝ :=
  tanhCoefficient (k + 1) * x ^ (2 * k + 1)

def bernoulliEvenTerm (x : ℝ) (k : ℕ) : ℝ :=
  let n : ℕ := k + 1
  (-1 : ℝ) ^ (n + 1) * B n * x ^ (2 * n) /
    (Nat.factorial (2 * n) : ℝ)

def cothTailTerm (x : ℝ) (k : ℕ) : ℝ :=
  let n : ℕ := k + 1
  (-1 : ℝ) ^ (n + 1) * B n * (2 : ℝ) ^ (2 * n) *
    x ^ (2 * n - 1) / (Nat.factorial (2 * n) : ℝ)

private def expQuotientSeries (z : ℂ) : ℂ :=
  ∑' n : ℕ, z ^ n / (Nat.factorial (n + 1) : ℂ)

private def expQuotientFPowerSeries : FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ
    (fun n => 1 / (Nat.factorial (n + 1) : ℂ))

private theorem expQuotientFPowerSeries_radius :
    expQuotientFPowerSeries.radius = ⊤ := by
  apply expQuotientFPowerSeries.radius_eq_top_of_summable_norm
  intro r
  have hs : Summable (fun n : ℕ =>
      (r : ℝ) ^ n / (Nat.factorial n : ℝ)) :=
    Real.summable_pow_div_factorial r
  have hbound : Summable (fun n : ℕ =>
      (r : ℝ) ^ n / (Nat.factorial (n + 1) : ℝ)) := by
    refine Summable.of_nonneg_of_le (fun n => by positivity) ?_ hs
    intro n
    have hfac : (Nat.factorial n : ℝ) ≤ Nat.factorial (n + 1) := by
      rw [Nat.factorial_succ]
      push_cast
      nlinarith [show (0 : ℝ) ≤ n by positivity,
        show (0 : ℝ) < Nat.factorial n by positivity]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) hfac
  simpa [expQuotientFPowerSeries,
    FormalMultilinearSeries.ofScalars_norm, norm_div, div_eq_mul_inv,
    mul_comm] using hbound

private theorem expQuotient_hasFPowerSeriesOnBall :
    HasFPowerSeriesOnBall expQuotientSeries expQuotientFPowerSeries 0 ⊤ := by
  refine ⟨by rw [expQuotientFPowerSeries_radius], by simp, ?_⟩
  intro z hz
  have hs : Summable (fun n : ℕ =>
      z ^ n / (Nat.factorial (n + 1) : ℂ)) := by
    have hfac : Summable (fun n : ℕ =>
        ‖z‖ ^ n / (Nat.factorial (n + 1) : ℝ)) := by
      have hbase := Real.summable_pow_div_factorial ‖z‖
      refine Summable.of_nonneg_of_le (fun n => by positivity) ?_ hbase
      intro n
      have hle : (Nat.factorial n : ℝ) ≤ Nat.factorial (n + 1) := by
        rw [Nat.factorial_succ]
        push_cast
        nlinarith [show (0 : ℝ) ≤ n by positivity,
          show (0 : ℝ) < Nat.factorial n by positivity]
      exact div_le_div_of_nonneg_left (by positivity) (by positivity) hle
    have hnorm : Summable (fun n : ℕ =>
        ‖z ^ n / (Nat.factorial (n + 1) : ℂ)‖) := by
      simpa [norm_div, norm_pow] using hfac
    exact hnorm.of_norm
  convert hs.hasSum using 1
  · funext n
    unfold expQuotientFPowerSeries
    rw [FormalMultilinearSeries.ofScalars_apply_eq]
    simp [smul_eq_mul]
    ring
  · simp [expQuotientSeries]

private theorem expQuotientSeries_mul (z : ℂ) :
    expQuotientSeries z * z = Complex.exp z - 1 := by
  have hexp : HasSum (fun n : ℕ => z ^ n / (Nat.factorial n : ℂ))
      (Complex.exp z) := by
    rw [Complex.exp_eq_exp_ℂ]
    exact NormedSpace.expSeries_div_hasSum_exp z
  have htail := (hasSum_nat_add_iff' 1).2 hexp
  calc
    expQuotientSeries z * z =
        ∑' n : ℕ, (z ^ n / (Nat.factorial (n + 1) : ℂ)) * z := by
      rw [expQuotientSeries, tsum_mul_right]
    _ = ∑' n : ℕ, z ^ (n + 1) / (Nat.factorial (n + 1) : ℂ) := by
      apply tsum_congr
      intro n
      rw [pow_succ]
      ring
    _ = Complex.exp z - 1 := by simpa using htail.tsum_eq

@[simp] private theorem expQuotientSeries_zero : expQuotientSeries 0 = 1 := by
  rw [expQuotientSeries]
  rw [show (fun n : ℕ => (0 : ℂ) ^ n / (Nat.factorial (n + 1) : ℂ)) =
      fun n => if n = 0 then 1 else 0 by
    funext n
    cases n <;> simp]
  simp

private theorem expQuotientSeries_ne_zero_of_norm_lt_two_pi
    {z : ℂ} (hz : ‖z‖ < 2 * Real.pi) : expQuotientSeries z ≠ 0 := by
  intro hzero
  by_cases hz0 : z = 0
  · subst z
    simpa using hzero
  have hexp : Complex.exp z = 1 := by
    have hmul := expQuotientSeries_mul z
    rw [hzero, zero_mul] at hmul
    exact sub_eq_zero.mp hmul.symm
  rcases Complex.exp_eq_one_iff.mp hexp with ⟨n, hn⟩
  have hn0 : n ≠ 0 := by
    intro hnzero
    subst n
    simp at hn
    exact hz0 hn
  have hnabs : (1 : ℝ) ≤ |(n : ℝ)| := by
    exact_mod_cast Int.one_le_abs hn0
  have hperiod :
      ‖(n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)‖ =
        |(n : ℝ)| * (2 * Real.pi) := by
    simp [norm_mul, Complex.norm_intCast, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [hn, hperiod] at hz
  nlinarith [Real.pi_pos]

private def bernoulliFunctionComplex (z : ℂ) : ℂ :=
  (expQuotientSeries z)⁻¹

private def bernoulliFunctionReal (x : ℝ) : ℝ :=
  (bernoulliFunctionComplex x).re

@[simp] private theorem bernoulliFunctionReal_zero :
    bernoulliFunctionReal 0 = 1 := by
  simp [bernoulliFunctionReal, bernoulliFunctionComplex]

private theorem bernoulliFunctionReal_eq (x : ℝ) (hx : x ≠ 0) :
    bernoulliFunctionReal x = x / (Real.exp x - 1) := by
  have hxc : (x : ℂ) ≠ 0 := by exact_mod_cast hx
  have hden : Real.exp x - 1 ≠ 0 := by
    intro hzero
    have : Real.exp x = 1 := sub_eq_zero.mp hzero
    exact hx (Real.exp_injective (by simpa using this))
  have hmul := expQuotientSeries_mul (x : ℂ)
  have hquot :
      expQuotientSeries (x : ℂ) =
        (Complex.exp x - 1) / x := by
    exact (eq_div_iff hxc).2 hmul
  have hcomplex :
      bernoulliFunctionComplex (x : ℂ) =
        ((x / (Real.exp x - 1) : ℝ) : ℂ) := by
    unfold bernoulliFunctionComplex
    rw [hquot, inv_div]
    push_cast
    field_simp [hden]
  calc
    bernoulliFunctionReal x = (bernoulliFunctionComplex (x : ℂ)).re := rfl
    _ = (((x / (Real.exp x - 1) : ℝ) : ℂ)).re :=
      congrArg Complex.re hcomplex
    _ = x / (Real.exp x - 1) :=
      Complex.ofReal_re (x / (Real.exp x - 1))

set_option backward.isDefEq.respectTransparency false in
private theorem bernoulliFunctionReal_hasSum_taylor
    (x : ℝ) (hx : |x| < 2 * Real.pi) :
    HasSum
      (fun n : ℕ =>
        iteratedDeriv n bernoulliFunctionReal 0 /
          (Nat.factorial n : ℝ) * x ^ n)
      (bernoulliFunctionReal x) := by
  obtain ⟨r, hxr, hrpi⟩ := exists_between hx
  have hr0 : 0 < r := lt_of_le_of_lt (abs_nonneg _) hxr
  let R : NNReal := ⟨r, hr0.le⟩
  have hsubset : Metric.closedBall (0 : ℂ) R ⊆
      Metric.ball (0 : ℂ) (2 * Real.pi) := by
    intro z hz
    have hzr : ‖z‖ ≤ r := by
      simpa [R, dist_eq_norm] using hz
    have : ‖z‖ < 2 * Real.pi := lt_of_le_of_lt hzr hrpi
    simpa [dist_eq_norm] using this
  have hHdiff : Differentiable ℂ expQuotientSeries := by
    intro z
    exact (expQuotient_hasFPowerSeriesOnBall.analyticAt_of_mem (by simp)).differentiableAt
  have hGdiff : DifferentiableOn ℂ bernoulliFunctionComplex
      (Metric.closedBall (0 : ℂ) R) := by
    intro z hz
    have hzpi : ‖z‖ < 2 * Real.pi := by
      have := hsubset hz
      simpa [dist_eq_norm] using this
    simpa [bernoulliFunctionComplex] using
      ((hHdiff z).inv (expQuotientSeries_ne_zero_of_norm_lt_two_pi hzpi)).differentiableWithinAt
  have hR0 : (0 : NNReal) < R := hr0
  have hG := hGdiff.hasFPowerSeriesOnBall hR0
  have hGreal := hG.restrictScalars (𝕜 := ℝ)
  have hpre := hGreal.compContinuousLinearMap
    (u := Complex.ofRealCLM) (x := (0 : ℝ))
  have hraw := Complex.reCLM.comp_hasFPowerSeriesOnBall hpre
  let q : FormalMultilinearSeries ℝ ℝ ℝ :=
    Complex.reCLM.compFormalMultilinearSeries
      ((FormalMultilinearSeries.restrictScalars ℝ
        (cauchyPowerSeries bernoulliFunctionComplex 0 R)).compContinuousLinearMap
          Complex.ofRealCLM)
  have hq : HasFPowerSeriesOnBall bernoulliFunctionReal q 0 R := by
    have hc := hraw.congr (g := bernoulliFunctionReal) ?_
    · simpa [q, Complex.ofRealCLM_enorm] using hc
    · intro y hy
      rfl
  have hy : x ∈ Metric.eball (0 : ℝ) R := by
    rw [Metric.eball_coe]
    simpa [R, Real.norm_eq_abs] using hxr
  have hs := hq.hasSum hy
  have hterm : ∀ n : ℕ,
      (q n) (fun _ => x) =
        iteratedDeriv n bernoulliFunctionReal 0 /
          (Nat.factorial n : ℝ) * x ^ n := by
    intro n
    have hfact := hq.factorial_smul (1 : ℝ) n
    simp only [FormalMultilinearSeries.apply_eq_prod_smul_coeff,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul, nsmul_eq_mul, one_pow, one_mul] at hfact
    have hcoeff :
        q.coeff n = iteratedDeriv n bernoulliFunctionReal 0 /
          (Nat.factorial n : ℝ) := by
      apply (eq_div_iff (by positivity : (Nat.factorial n : ℝ) ≠ 0)).2
      rw [mul_comm]
      simpa [← iteratedDeriv_eq_iteratedFDeriv] using hfact
    simp only [FormalMultilinearSeries.apply_eq_prod_smul_coeff,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul, hcoeff]
    ring
  simpa using hs.congr_fun (fun n => (hterm n).symm)

private def zetaEvenValue (k : ℕ) : ℝ :=
  (-1 : ℝ) ^ (k + 1) * 2 ^ (2 * k - 1) * Real.pi ^ (2 * k) *
    ((bernoulli (2 * k) : ℚ) : ℝ) / (Nat.factorial (2 * k) : ℝ)

private theorem zetaEvenValue_nonneg (k : ℕ) (hk : k ≠ 0) :
    0 ≤ zetaEvenValue k := by
  apply (hasSum_zeta_nat hk).nonneg
  intro n
  positivity

private theorem zetaEvenValue_le (k : ℕ) (hk : 1 ≤ k) :
    zetaEvenValue k ≤ Real.pi ^ 2 / 6 := by
  apply hasSum_le (g := fun n : ℕ => 1 / (n : ℝ) ^ 2)
      (fun n => by
        by_cases hn : n = 0
        · subst n
          have hpow : 2 * k ≠ 0 := by omega
          simp [hpow]
        · have hn1 : (1 : ℝ) ≤ n := by
            exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn)
          have hp : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ (2 * k) := by
            exact pow_le_pow_right₀ hn1 (by omega)
          exact one_div_le_one_div_of_le (by positivity) hp)
      (hasSum_zeta_nat (Nat.ne_of_gt hk)) hasSum_zeta_two

private theorem abs_bernoulli_even_div_factorial (k : ℕ) (hk : k ≠ 0) :
    |(((bernoulli (2 * k) : ℚ) : ℝ))| /
        (Nat.factorial (2 * k) : ℝ) =
      2 * zetaEvenValue k / (2 * Real.pi) ^ (2 * k) := by
  have hzt : (∑' n : ℕ, 1 / (n : ℝ) ^ (2 * k)) = zetaEvenValue k := by
    simpa [zetaEvenValue] using (hasSum_zeta_nat hk).tsum_eq
  rw [← hzt]
  have hz := congrArg abs (hasSum_zeta_nat hk).tsum_eq
  have hsum_nonneg : 0 ≤ ∑' n : ℕ, 1 / (n : ℝ) ^ (2 * k) := by
    rw [hzt]
    exact zetaEvenValue_nonneg k hk
  rw [abs_of_nonneg hsum_nonneg] at hz
  simp only [abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow] at hz
  norm_num at hz
  rw [abs_of_pos Real.pi_pos] at hz
  have hz' : (∑' n : ℕ, 1 / (n : ℝ) ^ (2 * k)) =
      2 ^ (2 * k - 1) * Real.pi ^ (2 * k) *
        |(((bernoulli (2 * k) : ℚ) : ℝ))| /
          (Nat.factorial (2 * k) : ℝ) := by
    simpa only [one_div] using hz
  rw [hz']
  field_simp
  have hp : (2 : ℝ) ^ (2 * k) = 2 ^ (2 * k - 1) * 2 := by
    rw [← pow_succ]
    congr 1
    omega
  rw [mul_pow, hp]
  ring

private def bernoulliSeriesTerm (x : ℝ) (n : ℕ) : ℝ :=
  (((bernoulli n : ℚ) : ℝ) / (Nat.factorial n : ℝ)) * x ^ n

private theorem norm_bernoulliSeriesTerm_even_le (x : ℝ) (k : ℕ) :
    ‖bernoulliSeriesTerm x (2 * (k + 1))‖ ≤
      (Real.pi ^ 2 / 3) *
        ((|x| / (2 * Real.pi)) ^ 2) ^ (k + 1) := by
  let n := k + 1
  have hn : n ≠ 0 := by omega
  have hzle := zetaEvenValue_le n (by omega)
  have hz0 := zetaEvenValue_nonneg n hn
  calc
    ‖bernoulliSeriesTerm x (2 * (k + 1))‖ =
        (2 * zetaEvenValue n / (2 * Real.pi) ^ (2 * n)) *
          |x| ^ (2 * n) := by
      rw [show k + 1 = n by rfl]
      simp only [bernoulliSeriesTerm, norm_mul, norm_div, Real.norm_eq_abs,
        norm_pow, norm_natCast]
      rw [abs_bernoulli_even_div_factorial n hn]
    _ = 2 * zetaEvenValue n * (|x| / (2 * Real.pi)) ^ (2 * n) := by
      rw [div_pow]
      field_simp
    _ ≤ (Real.pi ^ 2 / 3) * (|x| / (2 * Real.pi)) ^ (2 * n) := by
      gcongr
      nlinarith
    _ = (Real.pi ^ 2 / 3) *
        ((|x| / (2 * Real.pi)) ^ 2) ^ (k + 1) := by
      dsimp [n]
      rw [← pow_mul]

private theorem summable_norm_bernoulliSeriesTerm_even (x : ℝ)
    (hx : |x| < 2 * Real.pi) :
    Summable (fun k : ℕ => ‖bernoulliSeriesTerm x (2 * k)‖) := by
  let r : ℝ := (|x| / (2 * Real.pi)) ^ 2
  have hden : 0 < 2 * Real.pi := by positivity
  have hratio : |x| / (2 * Real.pi) < 1 := (div_lt_one hden).2 hx
  have hr0 : 0 ≤ r := sq_nonneg _
  have hr1 : r < 1 := by
    dsimp [r]
    nlinarith [div_nonneg (abs_nonneg x) hden.le]
  have hgeom : Summable (fun k : ℕ => (Real.pi ^ 2 / 3) * r ^ (k + 1)) := by
    exact ((summable_geometric_of_abs_lt_one
      (by simpa [abs_of_nonneg hr0] using hr1)).mul_left
        (Real.pi ^ 2 / 3)).comp_injective (fun _ _ h => by omega)
  rw [← summable_nat_add_iff 1]
  refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) ?_ hgeom
  intro k
  simpa [r] using norm_bernoulliSeriesTerm_even_le x k

private theorem summable_norm_bernoulliSeriesTerm_odd (x : ℝ) :
    Summable (fun k : ℕ => ‖bernoulliSeriesTerm x (2 * k + 1)‖) := by
  apply summable_of_ne_finset_zero (s := {0})
  intro k hk
  have hk0 : k ≠ 0 := by simpa using hk
  have hoddn : Odd (2 * k + 1) := ⟨k, by omega⟩
  have hgt : 1 < 2 * k + 1 := by omega
  simp [bernoulliSeriesTerm, bernoulli_eq_zero_of_odd hoddn hgt]

private theorem summable_norm_bernoulliSeriesTerm (x : ℝ)
    (hx : |x| < 2 * Real.pi) :
    Summable (fun n => ‖bernoulliSeriesTerm x n‖) := by
  let f : ℕ → ℝ := fun n => ‖bernoulliSeriesTerm x n‖
  have he : HasSum (fun k => f (2 * k)) (∑' k, f (2 * k)) :=
    (summable_norm_bernoulliSeriesTerm_even x hx).hasSum
  have ho : HasSum (fun k => f (2 * k + 1)) (∑' k, f (2 * k + 1)) :=
    (summable_norm_bernoulliSeriesTerm_odd x).hasSum
  exact (HasSum.even_add_odd (f := f) he ho).summable

private theorem bernoulli_convolution (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1),
      (((bernoulli k : ℚ) : ℝ) / (Nat.factorial k : ℝ)) *
        (1 / (Nat.factorial (n - k + 1) : ℝ))) =
      if n = 0 then 1 else 0 := by
  have hps := congrArg (PowerSeries.coeff (n + 1))
    (bernoulliPowerSeries_mul_exp_sub_one ℝ)
  simp only [bernoulliPowerSeries, PowerSeries.coeff_mul,
    PowerSeries.coeff_X, PowerSeries.coeff_mk] at hps
  rw [Finset.Nat.sum_antidiagonal_succ'] at hps
  simpa [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] using hps

private def expQuotientTerm (x : ℝ) (n : ℕ) : ℝ :=
  x ^ n / (Nat.factorial (n + 1) : ℝ)

private theorem summable_norm_expQuotientTerm (x : ℝ) :
    Summable (fun n => ‖expQuotientTerm x n‖) := by
  have hbase := Real.summable_pow_div_factorial |x|
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) ?_ hbase
  intro n
  simp only [expQuotientTerm, norm_div, norm_pow, Real.norm_eq_abs,
    norm_natCast]
  have hfac : (Nat.factorial n : ℝ) ≤ Nat.factorial (n + 1) := by
    rw [Nat.factorial_succ]
    push_cast
    nlinarith [show (0 : ℝ) ≤ n by positivity,
      show (0 : ℝ) < Nat.factorial n by positivity]
  exact div_le_div_of_nonneg_left (by positivity) (by positivity) hfac

private theorem hasSum_expQuotientTerm (x : ℝ) (hx : x ≠ 0) :
    HasSum (expQuotientTerm x) ((Real.exp x - 1) / x) := by
  have hexp : HasSum (fun n : ℕ => x ^ n / (Nat.factorial n : ℝ))
      (Real.exp x) := by
    simpa only [Real.exp_eq_exp_ℝ] using
      (NormedSpace.expSeries_div_hasSum_exp x)
  have hs := (hasSum_nat_add_iff' 1).2 hexp
  have hscaled := hs.mul_left (1 / x)
  convert hscaled using 1
  · funext n
    simp [expQuotientTerm, pow_succ]
    field_simp
  · simp
    field_simp

private theorem bernoulliSeries_hasSum (x : ℝ) (hx0 : x ≠ 0)
    (hx : |x| < 2 * Real.pi) :
    HasSum (bernoulliSeriesTerm x) (x / (Real.exp x - 1)) := by
  have hnormA := summable_norm_bernoulliSeriesTerm x hx
  have hnormQ := summable_norm_expQuotientTerm x
  have hc := hasSum_sum_range_mul_of_summable_norm hnormA hnormQ
  have hc' : HasSum (fun n : ℕ => if n = 0 then 1 else 0)
      ((∑' n, bernoulliSeriesTerm x n) *
        ∑' n, expQuotientTerm x n) := by
    convert hc using 1
    funext n
    symm
    calc
      (∑ k ∈ Finset.range (n + 1),
          bernoulliSeriesTerm x k * expQuotientTerm x (n - k)) =
          x ^ n * (∑ k ∈ Finset.range (n + 1),
            (((bernoulli k : ℚ) : ℝ) / (Nat.factorial k : ℝ)) *
              (1 / (Nat.factorial (n - k + 1) : ℝ))) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        simp only [bernoulliSeriesTerm, expQuotientTerm]
        have hkn : k ≤ n := by
          exact Nat.lt_succ_iff.mp (by
            simpa [Nat.succ_eq_add_one] using Finset.mem_range.mp hk)
        field_simp
        rw [mul_assoc, ← pow_add, Nat.add_sub_of_le hkn]
      _ = x ^ n * (if n = 0 then 1 else 0) := by
        rw [bernoulli_convolution n]
      _ = if n = 0 then 1 else 0 := by
        split_ifs with hn <;> simp [hn]
  have hprod : (∑' n, bernoulliSeriesTerm x n) *
      ∑' n, expQuotientTerm x n = 1 := by
    simpa using hc'.tsum_eq.symm
  rw [(hasSum_expQuotientTerm x hx0).tsum_eq] at hprod
  have hden : Real.exp x - 1 ≠ 0 := by
    intro hzero
    have : Real.exp x = 1 := sub_eq_zero.mp hzero
    exact hx0 (Real.exp_injective (by simpa using this))
  have hsum : (∑' n, bernoulliSeriesTerm x n) =
      x / (Real.exp x - 1) := by
    field_simp [hx0, hden] at hprod ⊢
    nlinarith
  simpa [hsum] using (summable_norm_bernoulliSeriesTerm x hx).of_norm.hasSum

private theorem signed_abs_bernoulli_even (n : ℕ) (hn : n ≠ 0) :
    (-1 : ℝ) ^ (n + 1) * |(((bernoulli (2 * n) : ℚ) : ℝ))| =
      (((bernoulli (2 * n) : ℚ) : ℝ)) := by
  have hz0 := zetaEvenValue_nonneg n hn
  have hcoef : 0 <
      (2 : ℝ) ^ (2 * n - 1) * Real.pi ^ (2 * n) /
        (Nat.factorial (2 * n) : ℝ) := by positivity
  have hprod : 0 ≤
      ((2 : ℝ) ^ (2 * n - 1) * Real.pi ^ (2 * n) /
        (Nat.factorial (2 * n) : ℝ)) *
          ((-1 : ℝ) ^ (n + 1) * (((bernoulli (2 * n) : ℚ) : ℝ))) := by
    unfold zetaEvenValue at hz0
    convert hz0 using 1 <;> ring
  have hsign : 0 ≤
      (-1 : ℝ) ^ (n + 1) * (((bernoulli (2 * n) : ℚ) : ℝ)) :=
    (mul_nonneg_iff_of_pos_left hcoef).mp hprod
  have habs : |(((bernoulli (2 * n) : ℚ) : ℝ))| =
      (-1 : ℝ) ^ (n + 1) * (((bernoulli (2 * n) : ℚ) : ℝ)) := by
    have := abs_of_nonneg hsign
    simpa [abs_mul] using this
  rw [habs, ← mul_assoc, ← pow_add]
  convert one_mul (((bernoulli (2 * n) : ℚ) : ℝ)) using 1
  norm_num

private theorem bernoulliEvenTerm_eq_bernoulliSeriesTerm (x : ℝ) (k : ℕ) :
    bernoulliEvenTerm x k = bernoulliSeriesTerm x (2 * (k + 1)) := by
  unfold bernoulliEvenTerm B bernoulliMagnitude
  dsimp
  rw [signed_abs_bernoulli_even (k + 1) (by omega)]
  simp [bernoulliSeriesTerm]
  ring

private theorem bernoulliSeries_even_expansion (x : ℝ) (hx0 : x ≠ 0)
    (hx : |x| < 2 * Real.pi) :
    x / (Real.exp x - 1) =
      1 - x / 2 + ∑' k, bernoulliEvenTerm x k := by
  let f := bernoulliSeriesTerm x
  have hf : Summable f :=
    (summable_norm_bernoulliSeriesTerm x hx).of_norm
  have heven : Summable (fun k : ℕ => f (2 * k)) :=
    hf.comp_injective (fun _ _ h => by omega)
  have hodd : Summable (fun k : ℕ => f (2 * k + 1)) :=
    hf.comp_injective (fun _ _ h => by omega)
  have htail0 := (hasSum_nat_add_iff' 1).2 heven.hasSum
  have htail : HasSum (bernoulliEvenTerm x)
      ((∑' k, f (2 * k)) - 1) := by
    convert htail0 using 1
    · funext k
      simpa [f] using (bernoulliEvenTerm_eq_bernoulliSeriesTerm x k)
    · simp [f, bernoulliSeriesTerm]
  have hodd_tsum : (∑' k, f (2 * k + 1)) = -x / 2 := by
    calc
      (∑' k, f (2 * k + 1)) = f 1 := by
        apply tsum_eq_single 0
        intro k hk
        have hk0 : k ≠ 0 := by simpa using hk
        have hoddn : Odd (2 * k + 1) := ⟨k, by omega⟩
        have hgt : 1 < 2 * k + 1 := by omega
        simp [f, bernoulliSeriesTerm, bernoulli_eq_zero_of_odd hoddn hgt]
      _ = -x / 2 := by
        simp [f, bernoulliSeriesTerm]
        ring
  have hsplit := tsum_even_add_odd heven hodd
  have hfull := (bernoulliSeries_hasSum x hx0 hx).tsum_eq
  have htailSum := htail.tsum_eq
  dsimp [f] at hsplit hfull
  rw [hodd_tsum] at hsplit
  nlinarith

private theorem summable_bernoulliEvenTerm (x : ℝ)
    (hx : |x| < 2 * Real.pi) : Summable (bernoulliEvenTerm x) := by
  let f := bernoulliSeriesTerm x
  have hf : Summable f :=
    (summable_norm_bernoulliSeriesTerm x hx).of_norm
  have heven : Summable (fun k : ℕ => f (2 * k)) :=
    hf.comp_injective (fun _ _ h => by omega)
  have htail0 := (hasSum_nat_add_iff' 1).2 heven.hasSum
  have htail : HasSum (bernoulliEvenTerm x)
      ((∑' k, f (2 * k)) - 1) := by
    convert htail0 using 1
    · funext k
      simpa [f] using (bernoulliEvenTerm_eq_bernoulliSeriesTerm x k)
    · simp [f, bernoulliSeriesTerm]
  exact htail.summable

private theorem mul_coth_eq (x : ℝ) (hx : x ≠ 0) :
    x * coth x = (2 * x) / (Real.exp (2 * x) - 1) + x := by
  have hsinh : Real.sinh x ≠ 0 := Real.sinh_ne_zero.mpr hx
  have hden : Real.exp (2 * x) - 1 ≠ 0 := by
    intro hzero
    have : Real.exp (2 * x) = 1 := sub_eq_zero.mp hzero
    have : 2 * x = 0 := Real.exp_injective (by simpa using this)
    exact hx (by nlinarith)
  have hexpsq : Real.exp x * Real.exp x = Real.exp (2 * x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hden2 : Real.exp x ^ 2 - 1 ≠ 0 := by
    rw [pow_two, hexpsq]
    exact hden
  have hden' : Real.exp (x * 2) - 1 ≠ 0 := by
    simpa [mul_comm] using hden
  have hexpsq' : Real.exp x ^ 2 = Real.exp (x * 2) := by
    rw [pow_two, hexpsq]
    congr 1
    ring
  unfold coth
  rw [Real.cosh_eq, Real.sinh_eq, Real.exp_neg]
  field_simp [Real.exp_ne_zero, hden, hden', hsinh, hden2]
  rw [hexpsq']
  ring

private theorem cothTailTerm_hasSum (x : ℝ) (hx : x ≠ 0)
    (hbound : |x| < Real.pi) :
    HasSum (cothTailTerm x) (coth x - 1 / x) := by
  have h2x : 2 * x ≠ 0 := mul_ne_zero (by norm_num) hx
  have hbound2 : |2 * x| < 2 * Real.pi := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    nlinarith
  have hbern := bernoulliSeries_even_expansion (2 * x) h2x hbound2
  have hmain : x * coth x = 1 + ∑' k, bernoulliEvenTerm (2 * x) k := by
    rw [mul_coth_eq x hx, hbern]
    ring
  have hterm : ∀ k, cothTailTerm x k * x = bernoulliEvenTerm (2 * x) k := by
    intro k
    have hpow : x ^ (2 * (k + 1) - 1) * x = x ^ (2 * (k + 1)) := by
      rw [← pow_succ]
      congr 1 <;> omega
    unfold cothTailTerm bernoulliEvenTerm
    dsimp
    rw [mul_pow]
    field_simp
    ring_nf at hpow ⊢
    rw [hpow]
  have hA : Summable (bernoulliEvenTerm (2 * x)) :=
    summable_bernoulliEvenTerm (2 * x) hbound2
  have htail : Summable (cothTailTerm x) := by
    apply (hA.mul_left (1 / x)).congr
    intro k
    field_simp [hx]
    simpa [mul_comm] using (hterm k).symm
  have hsum : (∑' k, cothTailTerm x k) * x =
      ∑' k, bernoulliEvenTerm (2 * x) k := by
    calc
      (∑' k, cothTailTerm x k) * x =
          ∑' k, cothTailTerm x k * x := by rw [tsum_mul_right]
      _ = ∑' k, bernoulliEvenTerm (2 * x) k := tsum_congr hterm
  have hvalue : (∑' k, cothTailTerm x k) = coth x - 1 / x := by
    field_simp [hx]
    nlinarith
  simpa [hvalue] using htail.hasSum

private theorem tanh_eq_two_coth_sub_coth (x : ℝ) :
    Real.tanh x = 2 * coth (2 * x) - coth x := by
  by_cases hx : x = 0
  · subst x
    simp [coth]
  · have hsinh : Real.sinh x ≠ 0 := Real.sinh_ne_zero.mpr hx
    have hcosh : Real.cosh x ≠ 0 := (Real.cosh_pos x).ne'
    have hsinh2 : Real.sinh (2 * x) ≠ 0 := by
      rw [Real.sinh_two_mul]
      positivity
    rw [Real.tanh_eq_sinh_div_cosh]
    unfold coth
    rw [Real.sinh_two_mul, Real.cosh_two_mul]
    field_simp [hsinh, hcosh, hsinh2]
    nlinarith [Real.cosh_sq_sub_sinh_sq x]

private theorem tanhSeriesTerm_eq_cothTailTerm (x : ℝ) (k : ℕ) :
    tanhSeriesTerm x k =
      2 * cothTailTerm (2 * x) k - cothTailTerm x k := by
  let n := k + 1
  have hn : n ≠ 0 := by omega
  have hp : 2 * (2 : ℝ) ^ (2 * n - 1) = 2 ^ (2 * n) := by
    rw [mul_comm, ← pow_succ]
    congr 1 <;> omega
  have hm : 2 * n - 1 = 2 * k + 1 := by
    dsimp [n]
    omega
  unfold tanhSeriesTerm tanhCoefficient cothTailTerm
  dsimp [n]
  rw [mul_pow, hm]
  field_simp
  ring_nf at hp ⊢

private theorem tanhSeriesTerm_hasSum (x : ℝ) (hbound : |x| < Real.pi / 2) :
    HasSum (tanhSeriesTerm x) (Real.tanh x) := by
  by_cases hx : x = 0
  · subst x
    have hz : tanhSeriesTerm 0 = fun _ : ℕ => 0 := by
      funext k
      simp [tanhSeriesTerm, show 2 * k + 1 ≠ 0 by omega]
    rw [hz]
    simpa using (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℝ)) 0)
  · have hxpi : |x| < Real.pi := by
      nlinarith [Real.pi_pos]
    have h2x : 2 * x ≠ 0 := mul_ne_zero (by norm_num) hx
    have h2xpi : |2 * x| < Real.pi := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      nlinarith
    have h₁ := cothTailTerm_hasSum x hx hxpi
    have h₂ := cothTailTerm_hasSum (2 * x) h2x h2xpi
    have hsub := (h₂.mul_left 2).sub h₁
    have hlimit :
        2 * (coth (2 * x) - 1 / (2 * x)) - (coth x - 1 / x) =
          Real.tanh x := by
      rw [tanh_eq_two_coth_sub_coth]
      field_simp [hx]
      ring
    rw [hlimit] at hsub
    exact hsub.congr_fun (fun k => tanhSeriesTerm_eq_cothTailTerm x k)

private theorem complex_cosh_ne_zero_of_norm_lt_half_pi
    {z : ℂ} (hz : ‖z‖ < Real.pi / 2) : Complex.cosh z ≠ 0 := by
  intro hcosh
  have hsum : Complex.exp z + Complex.exp (-z) = 0 := by
    simpa [Complex.cosh] using hcosh
  have hexp2 : Complex.exp (2 * z) = -1 := by
    have hmul := congrArg (fun w : ℂ => w * Complex.exp z) hsum
    have hsq : Complex.exp z * Complex.exp z = Complex.exp (2 * z) := by
      rw [← Complex.exp_add]
      congr 1
      ring
    dsimp only at hmul
    rw [add_mul, Complex.exp_neg] at hmul
    rw [inv_mul_cancel₀ (Complex.exp_ne_zero z)] at hmul
    rw [hsq] at hmul
    exact eq_neg_of_add_eq_zero_left (by simpa using hmul)
  have hexp4 : Complex.exp (4 * z) = 1 := by
    calc
      Complex.exp (4 * z) = Complex.exp (2 * z) * Complex.exp (2 * z) := by
        rw [← Complex.exp_add]
        congr 1
        ring
      _ = 1 := by rw [hexp2]; ring
  rcases Complex.exp_eq_one_iff.mp hexp4 with ⟨n, hn⟩
  have hnorm4 : ‖(4 : ℂ) * z‖ < 2 * Real.pi := by
    rw [norm_mul]
    norm_num
    nlinarith [Real.pi_pos]
  by_cases hn0 : n = 0
  · subst n
    simp at hn
    have hz0 : z = 0 := by
      apply mul_left_cancel₀ (show (4 : ℂ) ≠ 0 by norm_num)
      simpa using hn
    subst z
    simp at hcosh
  · have hnabs : (1 : ℝ) ≤ |(n : ℝ)| := by
      exact_mod_cast Int.one_le_abs hn0
    have hperiod :
        ‖(n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)‖ =
          |(n : ℝ)| * (2 * Real.pi) := by
      simp [Complex.norm_intCast, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    rw [hn, hperiod] at hnorm4
    nlinarith [Real.pi_pos]

private def complexSech (z : ℂ) : ℂ :=
  (Complex.cosh z)⁻¹

set_option backward.isDefEq.respectTransparency false in
private theorem sech_hasSum_taylor (x : ℝ) (hx : |x| < Real.pi / 2) :
    HasSum
      (fun n : ℕ =>
        iteratedDeriv n (fun y : ℝ => 1 / Real.cosh y) 0 /
          (Nat.factorial n : ℝ) * x ^ n)
      (1 / Real.cosh x) := by
  obtain ⟨r, hxr, hrpi⟩ := exists_between hx
  have hr0 : 0 < r := lt_of_le_of_lt (abs_nonneg _) hxr
  let R : NNReal := ⟨r, hr0.le⟩
  have hsubset : Metric.closedBall (0 : ℂ) R ⊆
      Metric.ball (0 : ℂ) (Real.pi / 2) := by
    intro z hz
    have hzr : ‖z‖ ≤ r := by
      simpa [R, dist_eq_norm] using hz
    have : ‖z‖ < Real.pi / 2 := lt_of_le_of_lt hzr hrpi
    simpa [dist_eq_norm] using this
  have hGdiff : DifferentiableOn ℂ complexSech
      (Metric.closedBall (0 : ℂ) R) := by
    intro z hz
    have hzpi : ‖z‖ < Real.pi / 2 := by
      have := hsubset hz
      simpa [dist_eq_norm] using this
    simpa [complexSech] using
      ((Complex.differentiable_cosh z).inv
        (complex_cosh_ne_zero_of_norm_lt_half_pi hzpi)).differentiableWithinAt
  have hR0 : (0 : NNReal) < R := hr0
  have hG := hGdiff.hasFPowerSeriesOnBall hR0
  have hGreal := hG.restrictScalars (𝕜 := ℝ)
  have hpre := hGreal.compContinuousLinearMap
    (u := Complex.ofRealCLM) (x := (0 : ℝ))
  have hraw := Complex.reCLM.comp_hasFPowerSeriesOnBall hpre
  let q : FormalMultilinearSeries ℝ ℝ ℝ :=
    Complex.reCLM.compFormalMultilinearSeries
      ((FormalMultilinearSeries.restrictScalars ℝ
        (cauchyPowerSeries complexSech 0 R)).compContinuousLinearMap
          Complex.ofRealCLM)
  have hq : HasFPowerSeriesOnBall (fun y : ℝ => 1 / Real.cosh y) q 0 R := by
    have hc := hraw.congr (g := fun y : ℝ => 1 / Real.cosh y) ?_
    · simpa [q, Complex.ofRealCLM_enorm] using hc
    · intro y hy
      simp [complexSech, one_div, ← Complex.ofReal_cosh]
  have hy : x ∈ Metric.eball (0 : ℝ) R := by
    rw [Metric.eball_coe]
    simpa [R, Real.norm_eq_abs] using hxr
  have hs := hq.hasSum hy
  have hterm : ∀ n : ℕ,
      (q n) (fun _ => x) =
        iteratedDeriv n (fun y : ℝ => 1 / Real.cosh y) 0 /
          (Nat.factorial n : ℝ) * x ^ n := by
    intro n
    have hfact := hq.factorial_smul (1 : ℝ) n
    simp only [FormalMultilinearSeries.apply_eq_prod_smul_coeff,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul, nsmul_eq_mul, one_pow, one_mul] at hfact
    have hcoeff :
        q.coeff n = iteratedDeriv n (fun y : ℝ => 1 / Real.cosh y) 0 /
          (Nat.factorial n : ℝ) := by
      apply (eq_div_iff (by positivity : (Nat.factorial n : ℝ) ≠ 0)).2
      rw [mul_comm]
      simpa [← iteratedDeriv_eq_iteratedFDeriv] using hfact
    simp only [FormalMultilinearSeries.apply_eq_prod_smul_coeff,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul, hcoeff]
    ring
  simpa using hs.congr_fun (fun n => (hterm n).symm)

theorem gap1 :
    ∀ x : ℝ, Real.tanh x = Real.sinh x / Real.cosh x := by
  exact Real.tanh_eq_sinh_div_cosh

theorem gap2 :
    ∀ x : ℝ, Real.sinh x / Real.cosh x =
      (∑' n, sinhTerm x n) / (∑' n, coshTerm x n) := by
  intro x
  unfold sinhTerm coshTerm
  rw [← Real.sinh_eq_tsum, ← Real.cosh_eq_tsum]

theorem gap3 :
    ∀ x : ℝ, Real.tanh x =
      (∑' n, sinhTerm x n) / (∑' n, coshTerm x n) := by
  intro x
  rw [gap1 x, gap2 x]

theorem gap4 :
    ∀ x : ℝ, |coshTail x| < 1 →
      Real.tanh x =
        (∑' n, sinhTerm x n) *
          (∑' m : ℕ, (-coshTail x) ^ m) := by
  intro x htail
  have htailSum : coshTail x = Real.cosh x - 1 := by
    have hs := (hasSum_nat_add_iff' 1).2 (Real.hasSum_cosh x)
    simpa [coshTail] using hs.tsum_eq
  have hgeom :
      (∑' m : ℕ, (-coshTail x) ^ m) = 1 / Real.cosh x := by
    rw [tsum_geometric_of_abs_lt_one (by simpa only [abs_neg] using htail)]
    rw [htailSum]
    ring
  have hsinh : (∑' n, sinhTerm x n) = Real.sinh x := by
    simpa [sinhTerm] using (Real.hasSum_sinh x).tsum_eq
  rw [gap1 x, hsinh, hgeom]
  ring

theorem gap5 :
    ∀ x : ℝ, |x| < Real.pi / 2 →
      Real.tanh x =
        (∑' n, sinhTerm x n) * (∑' n, sechMaclaurinTerm x n) := by
  intro x hx
  have hsinh : (∑' n, sinhTerm x n) = Real.sinh x := by
    simpa [sinhTerm] using (Real.hasSum_sinh x).tsum_eq
  have hsech : (∑' n, sechMaclaurinTerm x n) = 1 / Real.cosh x := by
    simpa [sechMaclaurinTerm] using (sech_hasSum_taylor x hx).tsum_eq
  rw [Real.tanh_eq_sinh_div_cosh, hsinh, hsech]
  ring

theorem gap6 :
    ∀ x : ℝ, |x| < Real.pi / 2 →
      (∑' n, sinhTerm x n) * (∑' n, sechMaclaurinTerm x n) =
        ∑' k, tanhSeriesTerm x k := by
  intro x hx
  calc
    (∑' n, sinhTerm x n) * (∑' n, sechMaclaurinTerm x n) =
        Real.tanh x := (gap5 x hx).symm
    _ = ∑' k, tanhSeriesTerm x k :=
      (tanhSeriesTerm_hasSum x hx).tsum_eq.symm

theorem gap7 :
    ∀ x : ℝ, |x| < Real.pi / 2 →
      Real.tanh x = ∑' k, tanhSeriesTerm x k := by
  intro x hx
  exact (tanhSeriesTerm_hasSum x hx).tsum_eq.symm

theorem gap8 :
    ∀ x : ℝ, x ≠ 0 → |x| < 2 * Real.pi →
      x / (Real.exp x - 1) =
        1 - x / 2 + ∑' k, bernoulliEvenTerm x k := by
  exact bernoulliSeries_even_expansion

theorem gap9 :
    B 1 = 1 / 6 := by
  norm_num [B, bernoulliMagnitude]

theorem gap10 :
    B 2 = 1 / 30 := by
  have h : bernoulli 4 = (-1 / 30 : ℚ) := by native_decide
  rw [B, bernoulliMagnitude, h]
  norm_num

theorem gap11 :
    B 3 = 1 / 42 := by
  have h : bernoulli 6 = (1 / 42 : ℚ) := by native_decide
  rw [B, bernoulliMagnitude, h]
  norm_num

theorem gap12 :
    B 4 = 1 / 30 := by
  have h : bernoulli 8 = (-1 / 30 : ℚ) := by native_decide
  rw [B, bernoulliMagnitude, h]
  norm_num

theorem gap13 :
    B 5 = 5 / 66 := by
  have h : bernoulli 10 = (5 / 66 : ℚ) := by native_decide
  rw [B, bernoulliMagnitude, h]
  norm_num

theorem gap14 :
    ∀ x : ℝ, x ≠ 0 → |x| < 2 * Real.pi →
      (x / 2) * coth (x / 2) =
        1 + ∑' k, bernoulliEvenTerm x k := by
  intro x hx hbound
  have hy : x / 2 ≠ 0 := div_ne_zero hx (by norm_num)
  have hsinh : Real.sinh (x / 2) ≠ 0 := Real.sinh_ne_zero.mpr hy
  have hden : Real.exp x - 1 ≠ 0 := by
    intro hzero
    have : Real.exp x = 1 := sub_eq_zero.mp hzero
    exact hx (Real.exp_injective (by simpa using this))
  have hexpsq : Real.exp (x / 2) * Real.exp (x / 2) = Real.exp x := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hden2 : Real.exp (x / 2) ^ 2 - 1 ≠ 0 := by
    rw [pow_two, hexpsq]
    exact hden
  have hcoth :
      (x / 2) * coth (x / 2) = x / (Real.exp x - 1) + x / 2 := by
    unfold coth
    rw [Real.cosh_eq, Real.sinh_eq, Real.exp_neg]
    field_simp [Real.exp_ne_zero, hden, hsinh, hden2]
    nlinarith [hexpsq]
  rw [hcoth, gap8 x hx hbound]
  ring

theorem gap15 :
    ∀ x : ℝ, x ≠ 0 → |x| < Real.pi →
      x * coth x =
        1 + ∑' k,
          let n : ℕ := k + 1
          (-1 : ℝ) ^ (n + 1) * B n * (2 : ℝ) ^ (2 * n) *
            x ^ (2 * n) / (Nat.factorial (2 * n) : ℝ) := by
  intro x hx hbound
  have h2x : 2 * x ≠ 0 := mul_ne_zero (by norm_num) hx
  have hbound2 : |2 * x| < 2 * Real.pi := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    nlinarith
  have h := gap14 (2 * x) h2x hbound2
  calc
    x * coth x = (2 * x / 2) * coth (2 * x / 2) := by ring
    _ = 1 + ∑' k, bernoulliEvenTerm (2 * x) k := h
    _ = 1 + ∑' k,
        let n : ℕ := k + 1
        (-1 : ℝ) ^ (n + 1) * B n * (2 : ℝ) ^ (2 * n) *
          x ^ (2 * n) / (Nat.factorial (2 * n) : ℝ) := by
      congr 1
      apply tsum_congr
      intro k
      unfold bernoulliEvenTerm
      dsimp
      rw [mul_pow]
      ring

theorem gap16 :
    ∀ x : ℝ, x ≠ 0 → |x| < Real.pi →
      coth x = 1 / x + ∑' k, cothTailTerm x k := by
  intro x hx hbound
  let a : ℕ → ℝ := fun k =>
    let n : ℕ := k + 1
    (-1 : ℝ) ^ (n + 1) * B n * (2 : ℝ) ^ (2 * n) *
      x ^ (2 * n) / (Nat.factorial (2 * n) : ℝ)
  have hmain := gap15 x hx hbound
  change x * coth x = 1 + ∑' k, a k at hmain
  have hterm : ∀ k, cothTailTerm x k * x = a k := by
    intro k
    have hpow : x ^ (2 * (k + 1) - 1) * x = x ^ (2 * (k + 1)) := by
      rw [← pow_succ]
      congr 1 <;> omega
    unfold cothTailTerm a
    dsimp
    let c : ℝ := (-1 : ℝ) ^ (k + 1 + 1) * B (k + 1) *
      (2 : ℝ) ^ (2 * (k + 1))
    let d : ℝ := Nat.factorial (2 * (k + 1))
    change c * x ^ (2 * (k + 1) - 1) / d * x =
      c * x ^ (2 * (k + 1)) / d
    calc
      c * x ^ (2 * (k + 1) - 1) / d * x =
          c * (x ^ (2 * (k + 1) - 1) * x) / d := by ring
      _ = c * x ^ (2 * (k + 1)) / d := by rw [hpow]
  have hsum : (∑' k, cothTailTerm x k) * x = ∑' k, a k := by
    calc
      (∑' k, cothTailTerm x k) * x =
          ∑' k, cothTailTerm x k * x := by rw [tsum_mul_right]
      _ = ∑' k, a k := tsum_congr hterm
  field_simp [hx]
  nlinarith

theorem gap17 :
    ∀ x : ℝ, Real.tanh x = 2 * coth (2 * x) - coth x := by
  intro x
  by_cases hx : x = 0
  · subst x
    simp [coth]
  · have hsinh : Real.sinh x ≠ 0 := by
      intro hzero
      apply hx
      apply Real.sinh_injective
      simpa using hzero
    have hcosh : Real.cosh x ≠ 0 := (Real.cosh_pos x).ne'
    have hsinh2 : Real.sinh (2 * x) ≠ 0 := by
      rw [Real.sinh_two_mul]
      positivity
    rw [gap1 x]
    unfold coth
    rw [Real.sinh_two_mul, Real.cosh_two_mul]
    field_simp [hsinh, hcosh, hsinh2]
    nlinarith [Real.cosh_sq_sub_sinh_sq x]

theorem gap18 :
    ∀ x : ℝ, |x| < Real.pi / 2 →
      Real.tanh x = ∑' k, tanhSeriesTerm x k := by
  exact gap7

theorem gap19 :
    ∀ x : ℝ, |x| < Real.pi / 2 →
      Real.tanh x = ∑' k, tanhSeriesTerm x k := by
  exact gap7

end

end ProofGap.Exercise2892
