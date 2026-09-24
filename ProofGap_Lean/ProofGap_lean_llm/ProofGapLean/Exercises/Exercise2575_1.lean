import ProofGapLean.Prelude.Analysis
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

open scoped BigOperators

namespace ProofGap.Exercise2575_1

noncomputable section

def term (x : ℝ) (n : ℕ) : ℝ :=
  (Real.cos ((n : ℝ) * x) - Real.cos (((n : ℝ) + 1) * x)) / (n : ℝ)

def partialSum (x : ℝ) (N : ℕ) : ℝ :=
  ∑ j ∈ Finset.range N, term x (j + 1)

def block (x : ℝ) (n p : ℕ) : ℝ :=
  ∑ j ∈ Finset.range p, term x (n + j + 1)

def middleTerm (x : ℝ) (n p : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (p - 1),
    (1 / ((n + j + 1 : ℕ) : ℝ) - 1 / ((n + j + 2 : ℕ) : ℝ)) *
      Real.cos (((n + j + 2 : ℕ) : ℝ) * x)

def abelForm (x : ℝ) (n p : ℕ) : ℝ :=
  Real.cos (((n + 1 : ℕ) : ℝ) * x) / ((n + 1 : ℕ) : ℝ) -
    middleTerm x n p -
    Real.cos (((n + p + 1 : ℕ) : ℝ) * x) / ((n + p : ℕ) : ℝ)

def cauchyBound (n p : ℕ) : ℝ :=
  1 / ((n + 1 : ℕ) : ℝ) +
    (∑ j ∈ Finset.range (p - 1),
      (1 / ((n + j + 1 : ℕ) : ℝ) - 1 / ((n + j + 2 : ℕ) : ℝ))) +
    1 / ((n + p : ℕ) : ℝ)

theorem gap1 :
    ∀ x n p, partialSum x (n + p) - partialSum x n =
      block x n p := by
  intro x n p
  simp only [partialSum, block]
  rw [Finset.sum_range_add]
  simp

theorem gap2
    (hblock : ∀ x n p, partialSum x (n + p) - partialSum x n =
      block x n p) :
    ∀ x n p, 1 ≤ p →
      partialSum x (n + p) - partialSum x n = abelForm x n p := by
  intro x n p hp
  rw [hblock x n p]
  cases p with
  | zero => omega
  | succ q =>
      induction q with
      | zero =>
          simp [block, abelForm, middleTerm, term, Nat.cast_add]
          ring
      | succ q ih =>
          have hblockStep :
              block x n (Nat.succ (Nat.succ q)) =
                block x n (Nat.succ q) + term x (n + Nat.succ q + 1) := by
            simp [block, Finset.sum_range_succ]
          have habelStep :
              abelForm x n (Nat.succ (Nat.succ q)) =
                abelForm x n (Nat.succ q) + term x (n + Nat.succ q + 1) := by
            simp [abelForm, middleTerm, term, Finset.sum_range_succ, Nat.cast_add]
            ring
          rw [hblockStep, ih (by omega), habelStep]

theorem gap3
    (habel : ∀ x n p, 1 ≤ p →
      partialSum x (n + p) - partialSum x n = abelForm x n p) :
    ∀ x n p, 1 ≤ p →
      |partialSum x (n + p) - partialSum x n| ≤ cauchyBound n p := by
  intro x n p hp
  rw [habel x n p hp]
  have hcoeff (j : ℕ) :
      0 ≤ 1 / ((n + j + 1 : ℕ) : ℝ) - 1 / ((n + j + 2 : ℕ) : ℝ) := by
    apply sub_nonneg.mpr
    apply one_div_le_one_div_of_le (by positivity)
    norm_num
  have hmiddle :
      |middleTerm x n p| ≤
        ∑ j ∈ Finset.range (p - 1),
          (1 / ((n + j + 1 : ℕ) : ℝ) - 1 / ((n + j + 2 : ℕ) : ℝ)) := by
    unfold middleTerm
    calc
      |∑ j ∈ Finset.range (p - 1),
          (1 / ((n + j + 1 : ℕ) : ℝ) - 1 / ((n + j + 2 : ℕ) : ℝ)) *
            Real.cos (((n + j + 2 : ℕ) : ℝ) * x)| ≤
          ∑ j ∈ Finset.range (p - 1),
            |(1 / ((n + j + 1 : ℕ) : ℝ) - 1 / ((n + j + 2 : ℕ) : ℝ)) *
              Real.cos (((n + j + 2 : ℕ) : ℝ) * x)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ Finset.range (p - 1),
          (1 / ((n + j + 1 : ℕ) : ℝ) - 1 / ((n + j + 2 : ℕ) : ℝ)) := by
        apply Finset.sum_le_sum
        intro j hj
        rw [abs_mul, abs_of_nonneg (hcoeff j)]
        exact mul_le_of_le_one_right (hcoeff j) (Real.abs_cos_le_one _)
  have hleft :
      |Real.cos (((n + 1 : ℕ) : ℝ) * x) / ((n + 1 : ℕ) : ℝ)| ≤
        1 / ((n + 1 : ℕ) : ℝ) := by
    rw [abs_div, abs_of_pos (show (0 : ℝ) < ((n + 1 : ℕ) : ℝ) by positivity)]
    exact div_le_div_of_nonneg_right (Real.abs_cos_le_one _) (by positivity)
  have hright :
      |Real.cos (((n + p + 1 : ℕ) : ℝ) * x) / ((n + p : ℕ) : ℝ)| ≤
        1 / ((n + p : ℕ) : ℝ) := by
    have hden : (0 : ℝ) < ((n + p : ℕ) : ℝ) := by positivity
    rw [abs_div, abs_of_pos hden]
    exact div_le_div_of_nonneg_right (Real.abs_cos_le_one _) hden.le
  unfold abelForm cauchyBound
  calc
    |Real.cos (((n + 1 : ℕ) : ℝ) * x) / ((n + 1 : ℕ) : ℝ) -
        middleTerm x n p -
        Real.cos (((n + p + 1 : ℕ) : ℝ) * x) / ((n + p : ℕ) : ℝ)| ≤
      |Real.cos (((n + 1 : ℕ) : ℝ) * x) / ((n + 1 : ℕ) : ℝ) -
        middleTerm x n p| +
        |Real.cos (((n + p + 1 : ℕ) : ℝ) * x) / ((n + p : ℕ) : ℝ)| := abs_sub _ _
    _ ≤
      (|Real.cos (((n + 1 : ℕ) : ℝ) * x) / ((n + 1 : ℕ) : ℝ)| +
        |middleTerm x n p|) +
        |Real.cos (((n + p + 1 : ℕ) : ℝ) * x) / ((n + p : ℕ) : ℝ)| :=
      add_le_add (abs_sub _ _) le_rfl
    _ ≤
      (1 / ((n + 1 : ℕ) : ℝ) +
        (∑ j ∈ Finset.range (p - 1),
          (1 / ((n + j + 1 : ℕ) : ℝ) - 1 / ((n + j + 2 : ℕ) : ℝ)))) +
        1 / ((n + p : ℕ) : ℝ) :=
      add_le_add (add_le_add hleft hmiddle) hright

theorem gap4 :
    ∀ n p, 1 ≤ p → cauchyBound n p = 2 / ((n + 1 : ℕ) : ℝ) := by
  intro n p hp
  have htelescope := Finset.sum_range_sub'
    (fun j : ℕ ↦ 1 / ((n + j + 1 : ℕ) : ℝ)) (p - 1)
  have hsum :
      (∑ j ∈ Finset.range (p - 1),
        (1 / ((n + j + 1 : ℕ) : ℝ) - 1 / ((n + j + 2 : ℕ) : ℝ))) =
        1 / ((n + 1 : ℕ) : ℝ) - 1 / ((n + p : ℕ) : ℝ) := by
    simpa [Nat.add_assoc, Nat.sub_add_cancel hp] using htelescope
  unfold cauchyBound
  rw [hsum]
  ring

theorem gap5 :
    ∀ n : ℕ, 1 ≤ n → 2 / ((n + 1 : ℕ) : ℝ) < 2 / (n : ℝ) := by
  intro n hn
  apply div_lt_div_of_pos_left (by norm_num)
  · exact_mod_cast hn
  · exact_mod_cast Nat.lt_succ_self n

theorem gap6
    (hbound : ∀ x n p, 1 ≤ p →
      |partialSum x (n + p) - partialSum x n| ≤ cauchyBound n p)
    (htelescope : ∀ n p, 1 ≤ p →
      cauchyBound n p = 2 / ((n + 1 : ℕ) : ℝ))
    (hstrict : ∀ n : ℕ, 1 ≤ n →
      2 / ((n + 1 : ℕ) : ℝ) < 2 / (n : ℝ)) :
    ∀ x n p, 1 ≤ n → 1 ≤ p →
      |partialSum x (n + p) - partialSum x n| < 2 / (n : ℝ) := by
  intro x n p hn hp
  calc
    |partialSum x (n + p) - partialSum x n| ≤ cauchyBound n p := hbound x n p hp
    _ = 2 / ((n + 1 : ℕ) : ℝ) := htelescope n p hp
    _ < 2 / (n : ℝ) := hstrict n hn

theorem gap7
    (hbound : ∀ x n p, 1 ≤ n → 1 ≤ p →
      |partialSum x (n + p) - partialSum x n| < 2 / (n : ℝ)) :
    ∀ x ε, ε > 0 → ∃ N : ℕ, ∀ n > N, ∀ p ≥ 1,
      |partialSum x (n + p) - partialSum x n| < 2 / (n : ℝ) ∧
        2 / (n : ℝ) < ε := by
  intro x ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (2 / ε)
  refine ⟨N, fun n hn p hp ↦ ⟨hbound x n p (by omega) hp, ?_⟩⟩
  have hnpos : (0 : ℝ) < n := by
    exact_mod_cast (show 0 < n by omega)
  have hratio : 2 / ε < (n : ℝ) := hN.trans_le (by exact_mod_cast (Nat.le_of_lt hn))
  apply (div_lt_iff₀ hnpos).2
  have := (div_lt_iff₀ hε).1 hratio
  nlinarith

theorem gap8
    (hcauchy : ∀ x ε, ε > 0 → ∃ N : ℕ, ∀ n > N, ∀ p ≥ 1,
      |partialSum x (n + p) - partialSum x n| < 2 / (n : ℝ) ∧
        2 / (n : ℝ) < ε) :
    ∀ x, Summable (term x) (SummationFilter.conditional ℕ) := by
  intro x
  have hpartial : CauchySeq (partialSum x) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := hcauchy x ε hε
    refine ⟨N + 1, fun m hm n hn ↦ ?_⟩
    by_cases hmn : m = n
    · subst n
      simpa using hε
    · by_cases hlt : n < m
      · have hpair := hN n (by omega) (m - n) (by omega)
        have h := hpair.1.trans hpair.2
        rw [Nat.add_sub_of_le hlt.le] at h
        simpa [Real.dist_eq] using h
      · have hlt' : m < n := by omega
        have hpair := hN m (by omega) (n - m) (by omega)
        have h := hpair.1.trans hpair.2
        rw [Nat.add_sub_of_le hlt'.le] at h
        simpa [Real.dist_eq, abs_sub_comm] using h
  obtain ⟨s, hs⟩ := cauchySeq_tendsto_of_complete hpartial
  refine ⟨s, ?_⟩
  change Tendsto (fun u : Finset ℕ ↦ ∑ b ∈ u, term x b)
    (SummationFilter.conditional ℕ).filter (nhds s)
  rw [SummationFilter.conditional_filter_eq_map_range, Filter.tendsto_map'_iff]
  apply (Filter.tendsto_add_atTop_iff_nat 1).mp
  convert hs using 1
  funext n
  simp [Function.comp_def, partialSum, term, Finset.sum_range_succ', Nat.cast_add,
    add_assoc]

theorem gap9
    (hsum : ∀ x, Summable (term x) (SummationFilter.conditional ℕ)) :
    ∀ x, Summable (term x) (SummationFilter.conditional ℕ) := hsum

end

end ProofGap.Exercise2575_1
