import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.PSeries
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise2856

noncomputable section

open Filter
open scoped BigOperators Topology

def oddProduct (n : ℕ) : ℝ :=
  ∏ k ∈ Finset.range n, (2 * k + 1 : ℕ)

def evenProduct (n : ℕ) : ℝ :=
  ∏ k ∈ Finset.range n, (2 * (k + 1) : ℕ)

def halfBinomialFalling (n : ℕ) : ℝ :=
  ∏ k ∈ Finset.range n, (-(1 / 2 : ℝ) - k)

def rawBinomialTerm (x : ℝ) (n : ℕ) : ℝ :=
  x * (halfBinomialFalling n / (Nat.factorial n : ℝ) * (-2 * x) ^ n)

def rootSeriesTerm (x : ℝ) (n : ℕ) : ℝ :=
  oddProduct n / (Nat.factorial n : ℝ) * x ^ (n + 1)

def rootSeriesTail (x : ℝ) (n : ℕ) : ℝ :=
  rootSeriesTerm x (n + 1)

def alternatingBoundaryTerm (n : ℕ) : ℝ :=
  let m := n + 1
  (-1 : ℝ) ^ (m + 1) * oddProduct m / evenProduct m

private theorem halfBinomialFalling_eq_smeval (n : ℕ) :
    halfBinomialFalling n =
      (descPochhammer ℤ n).smeval (-(1 / 2 : ℝ)) := by
  induction n with
  | zero =>
      simp [halfBinomialFalling, descPochhammer_zero]
  | succ n ih =>
      have hhalf :
          halfBinomialFalling (n + 1) =
            halfBinomialFalling n * (-(1 / 2 : ℝ) - n) := by
        simp [halfBinomialFalling, Finset.prod_range_succ]
      rw [hhalf, ih]
      simp [descPochhammer_succ_right, Polynomial.smeval_mul,
        Polynomial.smeval_natCast]

private theorem halfBinomialFalling_div_factorial (n : ℕ) :
    halfBinomialFalling n / (Nat.factorial n : ℝ) =
      Ring.choose (-(1 / 2 : ℝ)) n := by
  rw [Ring.choose_eq_smul]
  simp only [smul_eq_mul]
  rw [← halfBinomialFalling_eq_smeval]
  ring

private theorem halfBinomialFalling_formula (n : ℕ) :
    halfBinomialFalling n = oddProduct n / (-2 : ℝ) ^ n := by
  induction n with
  | zero =>
      norm_num [halfBinomialFalling, oddProduct]
  | succ n ih =>
      have hhalf :
          halfBinomialFalling (n + 1) =
            halfBinomialFalling n * (-(1 / 2 : ℝ) - n) := by
        simp [halfBinomialFalling, Finset.prod_range_succ]
      have hodd :
          oddProduct (n + 1) = oddProduct n * (2 * n + 1 : ℕ) := by
        simp [oddProduct, Finset.prod_range_succ]
      rw [hhalf, hodd, ih, pow_succ]
      push_cast
      ring

private theorem evenProduct_formula (n : ℕ) :
    evenProduct n = (2 : ℝ) ^ n * (Nat.factorial n : ℝ) := by
  induction n with
  | zero =>
      norm_num [evenProduct]
  | succ n ih =>
      have heven :
          evenProduct (n + 1) =
            evenProduct n * (2 * (n + 1) : ℕ) := by
        simp [evenProduct, Finset.prod_range_succ]
      rw [heven, ih, pow_succ, Nat.factorial_succ]
      push_cast
      ring

private theorem rawBinomialTerm_eq_rootSeriesTerm (x : ℝ) (n : ℕ) :
    rawBinomialTerm x n = rootSeriesTerm x n := by
  rw [rawBinomialTerm, rootSeriesTerm, halfBinomialFalling_formula,
    mul_pow, pow_succ]
  have hp : (-2 : ℝ) ^ n ≠ 0 := pow_ne_zero n (by norm_num)
  have hf : (Nat.factorial n : ℝ) ≠ 0 := by positivity
  field_simp [hp, hf]

private theorem binomialCore_hasSum (x : ℝ) (hx : |x| < 1 / 2) :
    HasSum
      (fun n : ℕ =>
        halfBinomialFalling n / (Nat.factorial n : ℝ) * (-2 * x) ^ n)
      (Real.rpow (1 - 2 * x) (-(1 / 2 : ℝ))) := by
  have hzabs : |-2 * x| < 1 := by
    rw [abs_mul]
    norm_num
    linarith
  have hz : -2 * x ∈ Metric.eball (0 : ℝ) 1 := by
    simp only [Metric.mem_eball, edist_dist, dist_zero_right,
      ENNReal.ofReal_lt_one]
    simpa [Real.norm_eq_abs] using hzabs
  have h :=
    (Real.one_add_rpow_hasFPowerSeriesOnBall_zero
      (a := -(1 / 2 : ℝ))).hasSum hz
  have hfun :
      (fun n : ℕ =>
        halfBinomialFalling n / (Nat.factorial n : ℝ) * (-2 * x) ^ n) =
        fun n : ℕ =>
          (binomialSeries ℝ (-(1 / 2 : ℝ)) n) (fun _ => -2 * x) := by
    funext n
    rw [halfBinomialFalling_div_factorial]
    rw [binomialSeries_apply]
    simp [smul_eq_mul, mul_comm]
  rw [hfun]
  change HasSum _ ((1 - 2 * x) ^ (-(1 / 2 : ℝ)))
  simpa [sub_eq_add_neg] using h

private theorem rootSeries_summable (x : ℝ) (hx : |x| < 1 / 2) :
    Summable (rootSeriesTerm x) := by
  have hcore := (binomialCore_hasSum x hx).mul_left x
  have hraw : Summable (rawBinomialTerm x) := by
    refine hcore.summable.congr ?_
    intro n
    simp only [rawBinomialTerm]
  exact hraw.congr (rawBinomialTerm_eq_rootSeriesTerm x)

private theorem boundaryTerm_identity (n : ℕ) :
    rootSeriesTail (-1 / 2) n =
      (1 / 2 : ℝ) * alternatingBoundaryTerm n := by
  rw [rootSeriesTail, rootSeriesTerm, alternatingBoundaryTerm]
  rw [evenProduct_formula, div_pow, pow_succ]
  have hp : (2 : ℝ) ^ (n + 1) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hf : (Nat.factorial (n + 1) : ℝ) ≠ 0 := by positivity
  field_simp [hp, hf]
  ring

theorem gap1 :
    ∀ x : ℝ, x < 1 / 2 →
      x / Real.sqrt (1 - 2 * x) =
        x * Real.rpow (1 - 2 * x) (-(1 / 2 : ℝ)) := by
  intro x hx
  have hpos : 0 < 1 - 2 * x := by linarith
  rw [div_eq_mul_inv, Real.sqrt_eq_rpow]
  change
    x * (((1 - 2 * x) ^ (1 / 2 : ℝ))⁻¹) =
      x * ((1 - 2 * x) ^ (-(1 / 2 : ℝ)))
  rw [Real.rpow_neg hpos.le]

theorem gap2
    (hrpow :
      ∀ x : ℝ, x < 1 / 2 →
        x / Real.sqrt (1 - 2 * x) =
          x * Real.rpow (1 - 2 * x) (-(1 / 2 : ℝ))) :
    ∀ x : ℝ, |x| < 1 / 2 →
      x / Real.sqrt (1 - 2 * x) = ∑' n, rawBinomialTerm x n := by
  intro x hx
  have hxlt : x < 1 / 2 := lt_of_le_of_lt (le_abs_self x) hx
  have hcore := (binomialCore_hasSum x hx).mul_left x
  calc
    x / Real.sqrt (1 - 2 * x) =
        x * Real.rpow (1 - 2 * x) (-(1 / 2 : ℝ)) :=
      hrpow x hxlt
    _ = ∑' n,
          x * (halfBinomialFalling n / (Nat.factorial n : ℝ) *
            (-2 * x) ^ n) :=
      hcore.tsum_eq.symm
    _ = ∑' n, rawBinomialTerm x n := by
      apply tsum_congr
      intro n
      simp only [rawBinomialTerm]

theorem gap3
    (hrpow :
      ∀ x : ℝ, x < 1 / 2 →
        x / Real.sqrt (1 - 2 * x) =
          x * Real.rpow (1 - 2 * x) (-(1 / 2 : ℝ)))
    (hbinomial :
      ∀ x : ℝ, |x| < 1 / 2 →
        x / Real.sqrt (1 - 2 * x) = ∑' n, rawBinomialTerm x n) :
    ∀ x : ℝ, |x| < 1 / 2 →
      x / Real.sqrt (1 - 2 * x) = ∑' n, rootSeriesTerm x n := by
  intro x hx
  exact (hbinomial x hx).trans
    (tsum_congr (rawBinomialTerm_eq_rootSeriesTerm x))

theorem gap4
    (hrpow :
      ∀ x : ℝ, x < 1 / 2 →
        x / Real.sqrt (1 - 2 * x) =
          x * Real.rpow (1 - 2 * x) (-(1 / 2 : ℝ)))
    (hbinomial :
      ∀ x : ℝ, |x| < 1 / 2 →
        x / Real.sqrt (1 - 2 * x) = ∑' n, rawBinomialTerm x n)
    (hsimplified :
      ∀ x : ℝ, |x| < 1 / 2 →
        x / Real.sqrt (1 - 2 * x) = ∑' n, rootSeriesTerm x n) :
    ∀ x : ℝ, |x| < 1 / 2 →
      x / Real.sqrt (1 - 2 * x) = x + ∑' n, rootSeriesTail x n := by
  intro x hx
  calc
    x / Real.sqrt (1 - 2 * x) = ∑' n, rootSeriesTerm x n :=
      hsimplified x hx
    _ = rootSeriesTerm x 0 + ∑' n, rootSeriesTerm x (n + 1) :=
      (rootSeries_summable x hx).tsum_eq_zero_add
    _ = x + ∑' n, rootSeriesTail x n := by
      simp [rootSeriesTerm, rootSeriesTail, oddProduct]

theorem gap5
    (hseries :
      ∀ x : ℝ, |x| < 1 / 2 →
        x / Real.sqrt (1 - 2 * x) = x + ∑' n, rootSeriesTail x n) :
    (-1 / 2 : ℝ) + ∑' n, rootSeriesTail (-1 / 2) n =
      (-1 / 2 : ℝ) + (1 / 2 : ℝ) * (∑' n, alternatingBoundaryTerm n) := by
  congr 1
  calc
    (∑' n, rootSeriesTail (-1 / 2) n) =
        ∑' n, (1 / 2 : ℝ) * alternatingBoundaryTerm n :=
      tsum_congr boundaryTerm_identity
    _ = (1 / 2 : ℝ) * (∑' n, alternatingBoundaryTerm n) :=
      tsum_mul_left

private def boundaryAmplitude (n : ℕ) : ℝ :=
  oddProduct n / evenProduct n

private theorem boundaryAmplitude_succ (n : ℕ) :
    boundaryAmplitude (n + 1) =
      boundaryAmplitude n *
        ((2 * (n : ℝ) + 1) / (2 * (n : ℝ) + 2)) := by
  have hodd :
      oddProduct (n + 1) = oddProduct n * (2 * n + 1 : ℕ) := by
    simp [oddProduct, Finset.prod_range_succ]
  have heven :
      evenProduct (n + 1) = evenProduct n * (2 * (n + 1) : ℕ) := by
    simp [evenProduct, Finset.prod_range_succ]
  have he : evenProduct n ≠ 0 := by
    unfold evenProduct
    positivity
  rw [boundaryAmplitude, hodd, heven, boundaryAmplitude]
  push_cast
  field_simp [he]

private theorem boundaryAmplitude_nonneg (n : ℕ) :
    0 ≤ boundaryAmplitude n := by
  unfold boundaryAmplitude oddProduct evenProduct
  positivity

private theorem boundaryAmplitude_antitone : Antitone boundaryAmplitude := by
  apply antitone_nat_of_succ_le
  intro n
  rw [boundaryAmplitude_succ]
  apply mul_le_of_le_one_right (boundaryAmplitude_nonneg n)
  rw [div_le_one (by positivity : (0 : ℝ) < 2 * (n : ℝ) + 2)]
  linarith

private theorem boundaryAmplitude_sq_le (n : ℕ) :
    boundaryAmplitude n ^ 2 ≤ 1 / ((n : ℝ) + 1) := by
  induction n with
  | zero =>
      norm_num [boundaryAmplitude, oddProduct, evenProduct]
  | succ n ih =>
      have hden1 : (0 : ℝ) < 2 * (n : ℝ) + 2 := by positivity
      have hden2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
      have hfactor :
          ((2 * (n : ℝ) + 1) / (2 * (n : ℝ) + 2)) ^ 2 ≤
            ((n : ℝ) + 1) / ((n : ℝ) + 2) := by
        rw [div_pow]
        rw [div_le_div_iff₀ (sq_pos_of_pos hden1) hden2]
        nlinarith [sq_nonneg (n : ℝ)]
      rw [boundaryAmplitude_succ, mul_pow]
      calc
        boundaryAmplitude n ^ 2 *
              ((2 * (n : ℝ) + 1) / (2 * (n : ℝ) + 2)) ^ 2 ≤
            (1 / ((n : ℝ) + 1)) *
              (((n : ℝ) + 1) / ((n : ℝ) + 2)) :=
          mul_le_mul ih hfactor (sq_nonneg _) (by positivity)
        _ = 1 / (((n + 1 : ℕ) : ℝ) + 1) := by
          push_cast
          field_simp
          ring

private theorem boundaryAmplitude_tendsto_zero :
    Tendsto boundaryAmplitude atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hinv := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hinv (ε ^ 2) (sq_pos_of_pos hε)
  refine ⟨N, fun n hn => ?_⟩
  have hsmall := hN n hn
  have hinvnonneg : 0 ≤ 1 / ((n : ℝ) + 1) := by positivity
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hinvnonneg] at hsmall
  have ha0 := boundaryAmplitude_nonneg n
  have hasq := boundaryAmplitude_sq_le n
  rw [Real.dist_eq, sub_zero, abs_of_nonneg ha0]
  nlinarith [sq_nonneg (boundaryAmplitude n + ε)]

private theorem boundaryAmplitude_lower (n : ℕ) :
    1 / ((n : ℝ) + 1) ≤ boundaryAmplitude n := by
  induction n with
  | zero =>
      norm_num [boundaryAmplitude, oddProduct, evenProduct]
  | succ n ih =>
      have hfactor0 :
          0 ≤ (2 * (n : ℝ) + 1) / (2 * (n : ℝ) + 2) := by positivity
      have hstep :
          1 / ((n : ℝ) + 2) ≤
            (1 / ((n : ℝ) + 1)) *
              ((2 * (n : ℝ) + 1) / (2 * (n : ℝ) + 2)) := by
        have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
        have hn2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
        have htwo : (0 : ℝ) < 2 * (n : ℝ) + 2 := by positivity
        field_simp
        nlinarith
      rw [boundaryAmplitude_succ]
      have hmul := mul_le_mul_of_nonneg_right ih hfactor0
      convert hstep.trans hmul using 1 <;> push_cast <;> ring

private theorem abs_alternatingBoundaryTerm (n : ℕ) :
    |alternatingBoundaryTerm n| = boundaryAmplitude (n + 1) := by
  rw [alternatingBoundaryTerm]
  rw [mul_div_assoc]
  change
    |(-1 : ℝ) ^ ((n + 1) + 1) * boundaryAmplitude (n + 1)| =
      boundaryAmplitude (n + 1)
  rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_nonneg (boundaryAmplitude_nonneg (n + 1))]

private theorem alternatingBoundaryTerm_not_summable :
    ¬ Summable alternatingBoundaryTerm := by
  intro hs
  have hamp : Summable (fun n : ℕ => boundaryAmplitude (n + 1)) := by
    simpa only [abs_alternatingBoundaryTerm] using hs.abs
  have hharmTail :
      Summable (fun n : ℕ => 1 / (((n + 2 : ℕ) : ℝ))) := by
    refine Summable.of_nonneg_of_le (fun n => by positivity) ?_ hamp
    intro n
    have h := boundaryAmplitude_lower (n + 1)
    push_cast at h
    convert h using 1 <;> norm_num [Nat.cast_add] <;> ring
  apply Real.not_summable_one_div_natCast
  exact (summable_nat_add_iff 2).1 (by
    simpa only [Nat.cast_add, Nat.cast_ofNat] using hharmTail)

private theorem alternatingBoundaryTerm_conditional_summable :
    Summable alternatingBoundaryTerm (SummationFilter.conditional ℕ) := by
  have ha : Antitone (fun n : ℕ => boundaryAmplitude (n + 1)) := by
    intro i j hij
    exact boundaryAmplitude_antitone (by omega)
  have ha0 :
      Tendsto (fun n : ℕ => boundaryAmplitude (n + 1)) atTop (𝓝 0) :=
    boundaryAmplitude_tendsto_zero.comp (Filter.tendsto_add_atTop_nat 1)
  obtain ⟨l, hl⟩ :=
    ha.tendsto_alternating_series_of_tendsto_zero ha0
  have hseq :
      (fun n : ℕ => (-1 : ℝ) ^ n * boundaryAmplitude (n + 1)) =
        alternatingBoundaryTerm := by
    funext n
    simp [alternatingBoundaryTerm, boundaryAmplitude, pow_add]
    ring
  rw [hseq] at hl
  refine ⟨l, ?_⟩
  rw [HasSum, SummationFilter.conditional_filter_eq_map_range,
    Filter.tendsto_map'_iff]
  simpa [Function.comp_def] using hl

theorem gap6
    (hboundary :
      (-1 / 2 : ℝ) + ∑' n, rootSeriesTail (-1 / 2) n =
        (-1 / 2 : ℝ) + (1 / 2 : ℝ) * (∑' n, alternatingBoundaryTerm n)) :
    Summable alternatingBoundaryTerm (SummationFilter.conditional ℕ) := by
  exact alternatingBoundaryTerm_conditional_summable

theorem gap7
    (hboundarySummable : Summable alternatingBoundaryTerm) :
    ∀ x : ℝ, x = 1 / 2 →
      Real.sqrt (1 - 2 * x) = 0 ∧
        ¬ ∃ y : ℝ, y * Real.sqrt (1 - 2 * x) = x := by
  intro x hx
  subst x
  constructor
  · norm_num
  · rintro ⟨y, hy⟩
    norm_num at hy

theorem gap8
    (hrpow :
      ∀ x : ℝ, x < 1 / 2 →
        x / Real.sqrt (1 - 2 * x) =
          x * Real.rpow (1 - 2 * x) (-(1 / 2 : ℝ)))
    (hseries :
      ∀ x : ℝ, |x| < 1 / 2 →
        x / Real.sqrt (1 - 2 * x) = x + ∑' n, rootSeriesTail x n)
    (hboundarySummable : Summable alternatingBoundaryTerm)
    (hsingular :
      ∀ x : ℝ, x = 1 / 2 →
        Real.sqrt (1 - 2 * x) = 0 ∧
          ¬ ∃ y : ℝ, y * Real.sqrt (1 - 2 * x) = x) :
    ∀ x : ℝ, |x| < 1 / 2 →
      x / Real.sqrt (1 - 2 * x) = x + ∑' n, rootSeriesTail x n := by
  exact hseries

end

end ProofGap.Exercise2856
