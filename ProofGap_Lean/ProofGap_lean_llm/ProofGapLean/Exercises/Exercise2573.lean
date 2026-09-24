import ProofGapLean.Prelude.Analysis
import Mathlib.Topology.Algebra.InfiniteSum.Basic

open scoped BigOperators

namespace ProofGap.Exercise2573

noncomputable section

def term (a : ℕ → ℝ) (n : ℕ) : ℝ := a n / (10 : ℝ) ^ n

def partialSum (a : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ i ∈ Finset.range N, term a i

def block (a : ℕ → ℝ) (n p : ℕ) : ℝ :=
  ∑ j ∈ Finset.range p, term a (n + j)

def absBlockBound (a : ℕ → ℝ) (n p : ℕ) : ℝ :=
  ∑ j ∈ Finset.range p, |a (n + j)| / (10 : ℝ) ^ (n + j)

def geometricBound (n p : ℕ) : ℝ :=
  (10 / (10 : ℝ) ^ n) *
    ∑ j ∈ Finset.range p, 1 / (10 : ℝ) ^ j

def infiniteBound (n : ℕ) : ℝ :=
  (100 / 9 : ℝ) / (10 : ℝ) ^ n

theorem gap1
    (a : ℕ → ℝ) (hdigit : ∀ n, |a n| < 10) :
    ∀ n p, |partialSum a (n + p) - partialSum a n| =
      |block a n p| := by
  intro n p
  simp only [partialSum, block]
  rw [Finset.sum_range_add]
  simp

theorem gap2
    (a : ℕ → ℝ)
    (hblock : ∀ n p, |partialSum a (n + p) - partialSum a n| =
      |block a n p|) :
    ∀ n p, |partialSum a (n + p) - partialSum a n| ≤
      absBlockBound a n p := by
  intro n p
  rw [hblock n p]
  simpa [block, absBlockBound, term, abs_div] using
    (Finset.abs_sum_le_sum_abs (fun j ↦ term a (n + j)) (Finset.range p))

theorem gap3
    (a : ℕ → ℝ) (hdigit : ∀ n, |a n| < 10)
    (htriangle : ∀ n p, |partialSum a (n + p) - partialSum a n| ≤
      absBlockBound a n p) :
    ∀ n p, |partialSum a (n + p) - partialSum a n| ≤
      geometricBound n p := by
  intro n p
  calc
    |partialSum a (n + p) - partialSum a n| ≤ absBlockBound a n p :=
      htriangle n p
    _ ≤ ∑ j ∈ Finset.range p, 10 / (10 : ℝ) ^ (n + j) := by
      apply Finset.sum_le_sum
      intro j hj
      exact div_le_div_of_nonneg_right (le_of_lt (hdigit (n + j))) (by positivity)
    _ = geometricBound n p := by
      unfold geometricBound
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [pow_add]
      field_simp

theorem gap4 :
    ∀ n p, geometricBound n p <
      (10 / (10 : ℝ) ^ n) * (10 / 9 : ℝ) := by
  intro n p
  unfold geometricBound
  apply mul_lt_mul_of_pos_left _ (by positivity)
  have hgeom := geom_sum_mul_neg (x := (1 / 10 : ℝ)) p
  have hp : 0 < ((10 : ℝ) ^ p)⁻¹ := by positivity
  simp only [one_div_pow] at hgeom
  norm_num at hgeom ⊢
  nlinarith

theorem gap5 :
    ∀ n, (10 / (10 : ℝ) ^ n) * (10 / 9 : ℝ) =
      infiniteBound n := by
  intro n
  unfold infiniteBound
  ring

theorem gap6
    (a : ℕ → ℝ)
    (hgeom : ∀ n p, |partialSum a (n + p) - partialSum a n| ≤
      geometricBound n p)
    (hfinite : ∀ n p, geometricBound n p <
      (10 / (10 : ℝ) ^ n) * (10 / 9 : ℝ))
    (hrewrite : ∀ n, (10 / (10 : ℝ) ^ n) * (10 / 9 : ℝ) =
      infiniteBound n) :
    ∀ n p, |partialSum a (n + p) - partialSum a n| <
      infiniteBound n := by
  intro n p
  calc
    |partialSum a (n + p) - partialSum a n| ≤ geometricBound n p := hgeom n p
    _ < (10 / (10 : ℝ) ^ n) * (10 / 9 : ℝ) := hfinite n p
    _ = infiniteBound n := hrewrite n

theorem gap7
    (a : ℕ → ℝ)
    (hbound : ∀ n p, |partialSum a (n + p) - partialSum a n| <
      infiniteBound n) :
    ∀ n p ε, ε > 0 → infiniteBound n < ε →
      |partialSum a (n + p) - partialSum a n| < ε := by
  intro n p ε hε hdecay
  exact (hbound n p).trans hdecay

theorem gap8 :
    ∀ ε : ℝ, ε > 0 → ∃ N : ℕ, ∀ n > N, infiniteBound n < ε := by
  have hpow : Tendsto (fun n : ℕ ↦ (1 / 10 : ℝ) ^ n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hlim : Tendsto infiniteBound atTop (nhds 0) := by
    simpa [infiniteBound, one_div_pow, div_eq_mul_inv] using
      (tendsto_const_nhds.mul hpow :
        Tendsto (fun n : ℕ ↦ (100 / 9 : ℝ) * (1 / 10 : ℝ) ^ n)
          atTop (nhds ((100 / 9 : ℝ) * 0)))
  intro ε hε
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hlim) ε hε
  refine ⟨N, fun n hn ↦ ?_⟩
  have := hN n (Nat.le_of_lt hn)
  have hinfinite : 0 < infiniteBound n := by
    unfold infiniteBound
    positivity
  simpa [Real.dist_eq, abs_of_pos hinfinite] using this

theorem gap9
    (a : ℕ → ℝ)
    (htransfer : ∀ n p ε, ε > 0 → infiniteBound n < ε →
      |partialSum a (n + p) - partialSum a n| < ε)
    (hdecay : ∀ ε : ℝ, ε > 0 →
      ∃ N : ℕ, ∀ n > N, infiniteBound n < ε) :
    ∀ ε : ℝ, ε > 0 → ∃ N : ℕ, ∀ n > N, ∀ p,
      |partialSum a (n + p) - partialSum a n| < ε := by
  intro ε hε
  obtain ⟨N, hN⟩ := hdecay ε hε
  refine ⟨N, fun n hn p ↦ ?_⟩
  exact htransfer n p ε hε (hN n hn)

theorem gap10
    (a : ℕ → ℝ)
    (hcauchy : ∀ ε : ℝ, ε > 0 → ∃ N : ℕ, ∀ n > N, ∀ p,
      |partialSum a (n + p) - partialSum a n| < ε) :
    CauchySeq (partialSum a) := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := hcauchy ε hε
  refine ⟨N + 1, fun m hm n hn ↦ ?_⟩
  by_cases hmn : n ≤ m
  · have h := hN n (by omega) (m - n)
    rw [Nat.add_sub_of_le hmn] at h
    simpa [Real.dist_eq] using h
  · have hmn' : m ≤ n := by omega
    have h := hN m (by omega) (n - m)
    rw [Nat.add_sub_of_le hmn'] at h
    simpa [Real.dist_eq, abs_sub_comm] using h

theorem gap11
    (a : ℕ → ℝ) (hdigit : ∀ n, |a n| < 10)
    (hcauchy : CauchySeq (partialSum a)) :
    Summable (term a) := by
  have hgeo : Summable (fun n : ℕ ↦ (1 / 10 : ℝ) ^ n) :=
    summable_geometric_of_norm_lt_one (by norm_num)
  have hmajorant : Summable (fun n : ℕ ↦ 10 * (1 / 10 : ℝ) ^ n) :=
    hgeo.mul_left 10
  apply Summable.of_norm_bounded hmajorant
  intro n
  calc
    ‖term a n‖ = |a n| / (10 : ℝ) ^ n := by
      simp [term, Real.norm_eq_abs, abs_div]
    _ ≤ 10 / (10 : ℝ) ^ n :=
      div_le_div_of_nonneg_right (le_of_lt (hdigit n)) (by positivity)
    _ = 10 * (1 / 10 : ℝ) ^ n := by
      rw [one_div_pow]
      ring

theorem gap12
    (a : ℕ → ℝ)
    (hsum : Summable (term a)) :
    Summable (term a) := hsum

end

end ProofGap.Exercise2573
