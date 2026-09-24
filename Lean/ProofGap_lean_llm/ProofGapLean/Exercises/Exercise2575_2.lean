import ProofGapLean.Prelude.Analysis
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Lean.Elab.Tactic.Omega
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Defs.Filter
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

open scoped BigOperators

namespace ProofGap.Exercise2575_2

noncomputable section

def harmonic (n : ℕ) : ℝ := 1 / (n : ℝ)

def partialSum (N : ℕ) : ℝ :=
  ∑ j ∈ Finset.range N, harmonic (j + 1)

def block (n p : ℕ) : ℝ :=
  ∑ j ∈ Finset.range p, harmonic (n + j + 1)

def constantLower (n : ℕ) : ℝ :=
  ∑ _j ∈ Finset.range n, 1 / (2 * (n : ℝ))

theorem gap1 :
    ∀ ε₀ : ℝ, 0 < ε₀ → ε₀ < 1 / 2 →
      ∀ n : ℕ, 1 ≤ n → ∃ p : ℕ, p = n ∧
        |partialSum (n + p) - partialSum n| = block n p := by
  intro ε₀ hε₀ hε n hn
  refine ⟨n, rfl, ?_⟩
  have hdiff :
      partialSum (n + n) - partialSum n = block n n := by
    unfold partialSum block
    rw [Finset.sum_range_add]
    ring
  have hnonneg : 0 ≤ block n n := by
    unfold block harmonic
    positivity
  rw [hdiff, abs_of_nonneg hnonneg]

theorem gap2 :
    ∀ ε₀ : ℝ, 0 < ε₀ → ε₀ < 1 / 2 →
      ∀ n : ℕ, 1 ≤ n → ∃ p : ℕ, p = n ∧
        block n p ≥ constantLower n := by
  intro ε₀ hε₀ hε n hn
  refine ⟨n, rfl, ?_⟩
  unfold block constantLower
  apply Finset.sum_le_sum
  intro j hj
  simp only [Finset.mem_range] at hj
  unfold harmonic
  have hnatpos : 0 < n + j + 1 := by omega
  have hnat : n + j + 1 ≤ 2 * n := by omega
  have hpos : (0 : ℝ) < ((n + j + 1 : ℕ) : ℝ) := by
    exact_mod_cast hnatpos
  have hcast : ((n + j + 1 : ℕ) : ℝ) ≤ 2 * (n : ℝ) := by
    exact_mod_cast hnat
  simpa using (one_div_le_one_div_of_le hpos hcast)

theorem gap3 :
    ∀ ε₀ : ℝ, 0 < ε₀ → ε₀ < 1 / 2 →
      ∀ n : ℕ, 1 ≤ n → ∃ p : ℕ, p = n ∧
        constantLower n = 1 / 2 := by
  intro ε₀ hε₀ hε n hn
  refine ⟨n, rfl, ?_⟩
  have hnR : (n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hn)
  unfold constantLower
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  field_simp [hnR]

theorem gap4 :
    ∀ ε₀ : ℝ, 0 < ε₀ → ε₀ < 1 / 2 →
      ∀ n : ℕ, 1 ≤ n → ∃ p : ℕ, p = n ∧
        (1 / 2 : ℝ) > ε₀ := by
  intro ε₀ hε₀ hε n hn
  exact ⟨n, rfl, hε⟩

theorem gap5
    (hpartial : ∀ ε₀ : ℝ, 0 < ε₀ → ε₀ < 1 / 2 →
      ∀ n : ℕ, 1 ≤ n → ∃ p : ℕ, p = n ∧
        |partialSum (n + p) - partialSum n| = block n p)
    (hlower : ∀ ε₀ : ℝ, 0 < ε₀ → ε₀ < 1 / 2 →
      ∀ n : ℕ, 1 ≤ n → ∃ p : ℕ, p = n ∧
        block n p ≥ constantLower n)
    (hhalf : ∀ n : ℕ, 1 ≤ n → constantLower n = 1 / 2) :
    ∀ ε₀ : ℝ, 0 < ε₀ → ε₀ < 1 / 2 →
      ∀ n : ℕ, 1 ≤ n → ∃ p : ℕ, p = n ∧
        |partialSum (n + p) - partialSum n| > ε₀ := by
  intro ε₀ hε₀ hε n hn
  rcases hpartial ε₀ hε₀ hε n hn with ⟨p, hp, hpartial'⟩
  rcases hlower ε₀ hε₀ hε n hn with ⟨q, hq, hlower'⟩
  refine ⟨n, rfl, ?_⟩
  calc
    |partialSum (n + n) - partialSum n| = block n n := by
      simpa [hp] using hpartial'
    _ ≥ constantLower n := by
      simpa [hq] using hlower'
    _ = 1 / 2 := hhalf n hn
    _ > ε₀ := hε

theorem gap6
    (hnotCauchy : ∀ ε₀ : ℝ, 0 < ε₀ → ε₀ < 1 / 2 →
      ∀ n : ℕ, 1 ≤ n → ∃ p : ℕ, p = n ∧
        |partialSum (n + p) - partialSum n| > ε₀) :
    ¬ Summable harmonic := by
  intro hs
  let s : ℝ := ∑' k : ℕ, harmonic k
  have hfull :
      Tendsto (fun N : ℕ => Finset.sum (Finset.range N) harmonic)
        atTop (nhds s) := by
    dsimp [s]
    exact hs.hasSum.tendsto_sum_nat
  have heq (N : ℕ) :
      Finset.sum (Finset.range (N + 1)) harmonic = partialSum N := by
    unfold partialSum
    rw [Finset.sum_range_succ']
    simp [harmonic]
  rcases (Metric.tendsto_atTop.1 hfull) (1 / 8 : ℝ) (by norm_num) with
    ⟨N, hN⟩
  let n : ℕ := max N 1
  have hnN : N ≤ n := by simp [n]
  have hn1 : 1 ≤ n := by simp [n]
  have hnear1 : |partialSum n - s| < (1 / 8 : ℝ) := by
    have hmem := hN (n + 1) (by omega)
    rw [heq n] at hmem
    simpa only [Real.dist_eq] using hmem
  have hnear2 : |partialSum (n + n) - s| < (1 / 8 : ℝ) := by
    have hmem := hN (n + n + 1) (by omega)
    rw [heq (n + n)] at hmem
    simpa only [Real.dist_eq] using hmem
  rcases hnotCauchy (1 / 4 : ℝ) (by norm_num) (by norm_num) n hn1 with
    ⟨p, hp, hbad⟩
  have hbad_n : |partialSum (n + n) - partialSum n| > (1 / 4 : ℝ) := by
    simpa [hp] using hbad
  have htri :
      |partialSum (n + n) - partialSum n| ≤
        |partialSum (n + n) - s| + |partialSum n - s| := by
    calc
      |partialSum (n + n) - partialSum n| =
          |(partialSum (n + n) - s) + (s - partialSum n)| := by
            congr 1
            ring
      _ ≤ |partialSum (n + n) - s| + |s - partialSum n| :=
        abs_add_le _ _
      _ = |partialSum (n + n) - s| + |partialSum n - s| := by
        rw [abs_sub_comm s (partialSum n)]
  linarith

theorem gap7
    (hdiv : ¬ Summable harmonic) :
    ¬ Summable harmonic := by
  exact hdiv

end

end ProofGap.Exercise2575_2
