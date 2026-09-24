import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods

namespace ProofGap.Exercise2968

noncomputable section

open Filter
open scoped BigOperators

def denominator (q x : ℝ) : ℝ :=
  1 - 2 * q * Real.cos x + q ^ 2

def target (q x : ℝ) : ℝ :=
  (1 - q * Real.cos x) / denominator q x

def epos (x : ℝ) : ℂ :=
  Complex.exp (Complex.I * x)

def eneg (x : ℝ) : ℂ :=
  Complex.exp (-Complex.I * x)

def cosineSeries (q x : ℝ) : ℝ :=
  ∑' n : ℕ, q ^ n * Real.cos ((n : ℝ) * x)

def cosinePartial (q : ℝ) (N : ℕ) (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.range N, q ^ n * Real.cos ((n : ℝ) * x)

private theorem denominator_pos (q x : ℝ) (hq : |q| < 1) :
    0 < denominator q x := by
  rcases abs_lt.mp hq with ⟨hqlo, hqhi⟩
  have hc₁ := Real.neg_one_le_cos x
  have hc₂ := Real.cos_le_one x
  unfold denominator
  by_cases hq0 : 0 ≤ q
  · nlinarith [sq_nonneg (1 - q)]
  · have hqneg : q < 0 := lt_of_not_ge hq0
    nlinarith [sq_nonneg (1 + q)]

private theorem epos_add_eneg (x : ℝ) :
    epos x + eneg x = ((2 * Real.cos x : ℝ) : ℂ) := by
  unfold epos eneg
  rw [show Complex.I * (x : ℂ) = (x : ℂ) * Complex.I by ring]
  rw [show -Complex.I * (x : ℂ) = ((-x : ℝ) : ℂ) * Complex.I by
    norm_num
    ring]
  rw [Complex.exp_mul_I, Complex.exp_mul_I]
  simp
  ring

private theorem epos_mul_eneg (x : ℝ) : epos x * eneg x = 1 := by
  unfold epos eneg
  rw [← Complex.exp_add]
  rw [show Complex.I * (x : ℂ) + -Complex.I * (x : ℂ) = 0 by ring]
  exact Complex.exp_zero

private theorem complex_denominator_eq (q x : ℝ) :
    1 - (q : ℂ) * (epos x + eneg x) + (q : ℂ) ^ 2 =
      (denominator q x : ℂ) := by
  rw [epos_add_eneg]
  norm_num [denominator]
  ring

private theorem complex_factor_expand (q x : ℝ) :
    (1 - (q : ℂ) * epos x) * (1 - (q : ℂ) * eneg x) =
      1 - (q : ℂ) * (epos x + eneg x) + (q : ℂ) ^ 2 := by
  calc
    (1 - (q : ℂ) * epos x) * (1 - (q : ℂ) * eneg x) =
        1 - (q : ℂ) * (epos x + eneg x) +
          (q : ℂ) ^ 2 * (epos x * eneg x) := by ring
    _ = 1 - (q : ℂ) * (epos x + eneg x) + (q : ℂ) ^ 2 := by
      rw [epos_mul_eneg]
      ring

private theorem complex_factors_ne (q : ℝ) (hq : |q| < 1) (x : ℝ) :
    (1 - (q : ℂ) * epos x) ≠ 0 ∧ (1 - (q : ℂ) * eneg x) ≠ 0 := by
  have hcast : (denominator q x : ℂ) ≠ 0 := by
    intro hzero
    have hre := congrArg Complex.re hzero
    have hrzero : denominator q x = 0 := by simpa using hre
    exact (denominator_pos q x hq).ne' hrzero
  have hprod :
      (1 - (q : ℂ) * epos x) * (1 - (q : ℂ) * eneg x) ≠ 0 := by
    rw [complex_factor_expand, complex_denominator_eq]
    exact hcast
  constructor
  · intro he
    apply hprod
    rw [he, zero_mul]
  · intro hn
    apply hprod
    rw [hn, mul_zero]

private theorem norm_epos (x : ℝ) : ‖epos x‖ = 1 := by
  simp [epos, Complex.norm_exp]

private theorem norm_eneg (x : ℝ) : ‖eneg x‖ = 1 := by
  simp [eneg, Complex.norm_exp]

private theorem complex_epos_summable (q : ℝ) (hq : |q| < 1) (x : ℝ) :
    Summable (fun n : ℕ => (q : ℂ) ^ n * epos x ^ n) := by
  have hn : ‖(q : ℂ) * epos x‖ < 1 := by
    simpa [norm_mul, norm_epos, Real.norm_eq_abs] using hq
  simpa [mul_pow] using
    (summable_geometric_of_norm_lt_one hn)

private theorem complex_eneg_summable (q : ℝ) (hq : |q| < 1) (x : ℝ) :
    Summable (fun n : ℕ => (q : ℂ) ^ n * eneg x ^ n) := by
  have hn : ‖(q : ℂ) * eneg x‖ < 1 := by
    simpa [norm_mul, norm_eneg, Real.norm_eq_abs] using hq
  simpa [mul_pow] using
    (summable_geometric_of_norm_lt_one hn)

private theorem complex_epos_tsum (q : ℝ) (hq : |q| < 1) (x : ℝ) :
    (∑' n : ℕ, (q : ℂ) ^ n * epos x ^ n) =
      1 / (1 - (q : ℂ) * epos x) := by
  have hn : ‖(q : ℂ) * epos x‖ < 1 := by
    simpa [norm_mul, norm_epos, Real.norm_eq_abs] using hq
  calc
    (∑' n : ℕ, (q : ℂ) ^ n * epos x ^ n) =
        ∑' n : ℕ, ((q : ℂ) * epos x) ^ n := by
          apply tsum_congr
          intro n
          rw [mul_pow]
    _ = 1 / (1 - (q : ℂ) * epos x) := by
      simpa [one_div] using (hasSum_geometric_of_norm_lt_one hn).tsum_eq

private theorem complex_eneg_tsum (q : ℝ) (hq : |q| < 1) (x : ℝ) :
    (∑' n : ℕ, (q : ℂ) ^ n * eneg x ^ n) =
      1 / (1 - (q : ℂ) * eneg x) := by
  have hn : ‖(q : ℂ) * eneg x‖ < 1 := by
    simpa [norm_mul, norm_eneg, Real.norm_eq_abs] using hq
  calc
    (∑' n : ℕ, (q : ℂ) ^ n * eneg x ^ n) =
        ∑' n : ℕ, ((q : ℂ) * eneg x) ^ n := by
          apply tsum_congr
          intro n
          rw [mul_pow]
    _ = 1 / (1 - (q : ℂ) * eneg x) := by
      simpa [one_div] using (hasSum_geometric_of_norm_lt_one hn).tsum_eq

private theorem epos_pow_eq (x : ℝ) :
    ∀ n : ℕ, epos x ^ n = epos ((n : ℝ) * x)
  | 0 => by simp [epos]
  | n + 1 => by
      rw [pow_succ, epos_pow_eq x n]
      unfold epos
      rw [← Complex.exp_add]
      congr 1
      norm_num
      ring

private theorem eneg_pow_eq (x : ℝ) :
    ∀ n : ℕ, eneg x ^ n = eneg ((n : ℝ) * x)
  | 0 => by simp [eneg]
  | n + 1 => by
      rw [pow_succ, eneg_pow_eq x n]
      unfold eneg
      rw [← Complex.exp_add]
      congr 1
      norm_num
      ring

private theorem euler_cosine_term (q x : ℝ) (n : ℕ) :
    (1 / 2 : ℂ) *
        ((q : ℂ) ^ n * epos x ^ n + (q : ℂ) ^ n * eneg x ^ n) =
      ((q ^ n * Real.cos ((n : ℝ) * x) : ℝ) : ℂ) := by
  rw [epos_pow_eq, eneg_pow_eq]
  calc
    (1 / 2 : ℂ) *
        ((q : ℂ) ^ n * epos ((n : ℝ) * x) +
          (q : ℂ) ^ n * eneg ((n : ℝ) * x)) =
      (1 / 2 : ℂ) * (q : ℂ) ^ n *
        (epos ((n : ℝ) * x) + eneg ((n : ℝ) * x)) := by ring
    _ = ((q ^ n * Real.cos ((n : ℝ) * x) : ℝ) : ℂ) := by
      rw [epos_add_eneg]
      norm_num
      ring

private theorem geometric_summable (q : ℝ) (hq : |q| < 1) :
    Summable (fun n : ℕ => |q| ^ n) := by
  have hn : ‖(|q| : ℝ)‖ < 1 := by
    simpa [Real.norm_eq_abs, abs_of_nonneg (abs_nonneg q)] using hq
  exact summable_geometric_of_norm_lt_one hn

private theorem cosine_summable (q : ℝ) (hq : |q| < 1) (x : ℝ) :
    Summable (fun n : ℕ => q ^ n * Real.cos ((n : ℝ) * x)) := by
  have hg := geometric_summable q hq
  refine hg.of_norm_bounded ?_
  intro n
  rw [Real.norm_eq_abs, abs_mul, abs_pow]
  calc
    |q| ^ n * |Real.cos ((n : ℝ) * x)| ≤ |q| ^ n * 1 :=
      mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (pow_nonneg (abs_nonneg q) n)
    _ = |q| ^ n := mul_one _

private theorem cosineSeries_split_three (q : ℝ) (hq : |q| < 1) (x : ℝ) :
    cosineSeries q x =
      1 + q * Real.cos x + q ^ 2 * Real.cos (2 * x) +
        ∑' k : ℕ, q ^ (k + 3) * Real.cos ((k + 3 : ℝ) * x) := by
  have hs := (cosine_summable q hq x).sum_add_tsum_nat_add 3
  unfold cosineSeries
  simpa [Finset.sum_range_succ, add_comm, add_left_comm, add_assoc] using hs.symm

private theorem cosinePartial_dist_le (q : ℝ) (hq : |q| < 1) (N : ℕ) (x : ℝ) :
    dist (cosinePartial q N x) (cosineSeries q x) ≤
      (∑' n : ℕ, |q| ^ n) - ∑ n ∈ Finset.range N, |q| ^ n := by
  let f : ℕ → ℝ := fun n => q ^ n * Real.cos ((n : ℝ) * x)
  let g : ℕ → ℝ := fun n => |q| ^ n
  have hf : Summable f := by
    simpa [f] using cosine_summable q hq x
  have hg : Summable g := by
    simpa [g] using geometric_summable q hq
  have hfs := hf.sum_add_tsum_nat_add N
  have hgs := hg.sum_add_tsum_nat_add N
  have hgt : Summable (fun k : ℕ => g (k + N)) := by
    simpa [g, pow_add, mul_comm] using hg.mul_left (|q| ^ N)
  have hbound : ∀ k : ℕ, ‖f (k + N)‖ ≤ g (k + N) := by
    intro k
    simp only [f, g]
    rw [Real.norm_eq_abs, abs_mul, abs_pow]
    simpa using
      mul_le_mul_of_nonneg_left
        (Real.abs_cos_le_one ((k + N : ℕ) * x))
        (pow_nonneg (abs_nonneg q) (k + N))
  have hfnorm : Summable (fun k : ℕ => ‖f (k + N)‖) := by
    refine hgt.of_norm_bounded ?_
    intro k
    simpa using hbound k
  change dist (∑ n ∈ Finset.range N, f n) (∑' n : ℕ, f n) ≤
    (∑' n : ℕ, g n) - ∑ n ∈ Finset.range N, g n
  calc
    dist (∑ n ∈ Finset.range N, f n) (∑' n : ℕ, f n) =
        ‖∑' k : ℕ, f (k + N)‖ := by
          rw [← hfs]
          simp [Real.dist_eq]
    _ ≤ ∑' k : ℕ, ‖f (k + N)‖ :=
      norm_tsum_le_tsum_norm hfnorm
    _ ≤ ∑' k : ℕ, g (k + N) := by
      have hpartial (m : ℕ) :
          (∑ k ∈ Finset.range m, ‖f (k + N)‖) ≤
            ∑ k ∈ Finset.range m, g (k + N) := by
        exact Finset.sum_le_sum fun k _ => hbound k
      have hlim :
          Tendsto
            (fun m : ℕ =>
              (∑ k ∈ Finset.range m, g (k + N)) -
                ∑ k ∈ Finset.range m, ‖f (k + N)‖)
            atTop
            (nhds
              ((∑' k : ℕ, g (k + N)) -
                ∑' k : ℕ, ‖f (k + N)‖)) := by
        exact hgt.hasSum.tendsto_sum_nat.sub
          hfnorm.hasSum.tendsto_sum_nat
      have hnonneg :
          0 ≤ (∑' k : ℕ, g (k + N)) -
            ∑' k : ℕ, ‖f (k + N)‖ := by
        exact ge_of_tendsto hlim
          (Filter.Eventually.of_forall fun m =>
            sub_nonneg.mpr (hpartial m))
      exact sub_nonneg.mp hnonneg
    _ = (∑' n : ℕ, g n) - ∑ n ∈ Finset.range N, g n := by
      linarith

theorem gap1 (q : ℝ) (hq : |q| < 1) :
    ∀ x,
      (target q x : ℂ) =
        (1 - (q : ℂ) / 2 * (epos x + eneg x)) /
          (1 - (q : ℂ) * (epos x + eneg x) + (q : ℂ) ^ 2) := by
  intro x
  rw [epos_add_eneg]
  norm_num [target, denominator]
  ring

theorem gap2 (q : ℝ) (hq : |q| < 1) :
    ∀ x,
      (target q x : ℂ) =
        1 / 2 *
          ((2 - (q : ℂ) * epos x - (q : ℂ) * eneg x) /
            ((1 - (q : ℂ) * epos x) *
              (1 - (q : ℂ) * eneg x))) := by
  intro x
  rw [gap1 q hq x, complex_factor_expand]
  ring

theorem gap3 (q : ℝ) (hq : |q| < 1) :
    ∀ x,
      (target q x : ℂ) =
        1 / 2 *
          (1 / (1 - (q : ℂ) * epos x) +
            1 / (1 - (q : ℂ) * eneg x)) := by
  intro x
  rw [gap2 q hq x]
  obtain ⟨he, hn⟩ := complex_factors_ne q hq x
  field_simp [he, hn]
  ring

theorem gap4 (q : ℝ) (hq : |q| < 1) :
    ∀ x,
      (target q x : ℂ) =
        1 / 2 *
          ((∑' n : ℕ, (q : ℂ) ^ n * epos x ^ n) +
            ∑' n : ℕ, (q : ℂ) ^ n * eneg x ^ n) := by
  intro x
  rw [gap3 q hq x, complex_epos_tsum q hq x, complex_eneg_tsum q hq x]

theorem gap5 (q : ℝ) (hq : |q| < 1) :
    ∀ x,
      target q x =
        1 + q * Real.cos x + q ^ 2 * Real.cos (2 * x) +
          ∑' k : ℕ,
            q ^ (k + 3) * Real.cos ((k + 3 : ℝ) * x) := by
  intro x
  have hcomplex := gap4 q hq x
  have he := complex_epos_summable q hq x
  have hn := complex_eneg_summable q hq x
  have hc := cosine_summable q hq x
  have hseries : (target q x : ℂ) = (cosineSeries q x : ℂ) := by
    calc
      (target q x : ℂ) =
          1 / 2 *
            ((∑' n : ℕ, (q : ℂ) ^ n * epos x ^ n) +
              ∑' n : ℕ, (q : ℂ) ^ n * eneg x ^ n) := hcomplex
      _ = 1 / 2 *
            (∑' n : ℕ,
              ((q : ℂ) ^ n * epos x ^ n +
                (q : ℂ) ^ n * eneg x ^ n)) := by
            congr 1
            exact (he.hasSum.add hn.hasSum).tsum_eq.symm
      _ = ∑' n : ℕ,
            1 / 2 *
              ((q : ℂ) ^ n * epos x ^ n +
                (q : ℂ) ^ n * eneg x ^ n) := by
            have hab : Summable (fun n : ℕ =>
                (q : ℂ) ^ n * epos x ^ n +
                  (q : ℂ) ^ n * eneg x ^ n) := he.add hn
            exact (hab.hasSum.mul_left (1 / 2 : ℂ)).tsum_eq.symm
      _ = ∑' n : ℕ,
            ((q ^ n * Real.cos ((n : ℝ) * x) : ℝ) : ℂ) := by
            apply tsum_congr
            intro n
            exact euler_cosine_term q x n
      _ = (cosineSeries q x : ℂ) := by
            simpa [cosineSeries] using (Complex.ofRealCLM.map_tsum hc).symm
  have hreal : target q x = cosineSeries q x := by
    have hre := congrArg Complex.re hseries
    simpa using hre
  calc
    target q x = cosineSeries q x := hreal
    _ = 1 + q * Real.cos x + q ^ 2 * Real.cos (2 * x) +
          ∑' k : ℕ, q ^ (k + 3) * Real.cos ((k + 3 : ℝ) * x) :=
      cosineSeries_split_three q hq x

theorem gap6 (q : ℝ) (hq : |q| < 1) :
    ∀ x,
      1 + q * Real.cos x + q ^ 2 * Real.cos (2 * x) +
          (∑' k : ℕ,
            q ^ (k + 3) * Real.cos ((k + 3 : ℝ) * x)) =
        cosineSeries q x := by
  intro x
  exact (cosineSeries_split_three q hq x).symm

theorem gap7 (q : ℝ) (hq : |q| < 1) :
    ∀ x, target q x = cosineSeries q x := by
  intro x
  rw [gap5 q hq x, gap6 q hq x]

theorem gap8 (q : ℝ) (hq : |q| < 1) :
    TendstoUniformlyOn
      (cosinePartial q) (target q) atTop Set.univ := by
  have ht : target q = cosineSeries q := funext (gap7 q hq)
  rw [ht, Metric.tendstoUniformlyOn_iff]
  intro ε hε
  let g : ℕ → ℝ := fun n => |q| ^ n
  have hg : Summable g := by
    simpa [g] using geometric_summable q hq
  have hconv :
      Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, g n) atTop
        (nhds (∑' n : ℕ, g n)) :=
    hg.hasSum.tendsto_sum_nat
  have hconst :
      Tendsto (fun _ : ℕ => ∑' n : ℕ, g n) atTop
        (nhds (∑' n : ℕ, g n)) :=
    tendsto_const_nhds
  have hres :
      Tendsto
        (fun N : ℕ => (∑' n : ℕ, g n) - ∑ n ∈ Finset.range N, g n)
        atTop (nhds 0) := by
    simpa using hconst.sub hconv
  refine ((Metric.tendsto_nhds.1 hres) ε hε).mono ?_
  intro N hN x hx
  have hb := cosinePartial_dist_le q hq N x
  have hnonneg :
      0 ≤ (∑' n : ℕ, |q| ^ n) - ∑ n ∈ Finset.range N, |q| ^ n := by
    exact le_trans dist_nonneg (cosinePartial_dist_le q hq N 0)
  calc
    dist (cosineSeries q x) (cosinePartial q N x) =
        dist (cosinePartial q N x) (cosineSeries q x) := dist_comm _ _
    _ ≤ (∑' n : ℕ, |q| ^ n) - ∑ n ∈ Finset.range N, |q| ^ n := hb
    _ = dist
          ((∑' n : ℕ, g n) - ∑ n ∈ Finset.range N, g n) 0 := by
          simp [g, Real.dist_eq, abs_of_nonneg hnonneg]
    _ < ε := hN

end

end ProofGap.Exercise2968
