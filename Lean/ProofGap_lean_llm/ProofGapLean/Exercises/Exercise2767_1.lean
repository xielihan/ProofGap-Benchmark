import ProofGapLean.Prelude.Analysis
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Topology.Defs.Filter

namespace ProofGap.Exercise2767_1

noncomputable section

open scoped BigOperators

def partialSum (N : ℕ) (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.range (N + 1), x ^ n

def geometricSum (x : ℝ) : ℝ :=
  1 / (1 - x)

def UniformlyConvergesOn
    (u : ℕ → ℝ → ℝ) (F : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ n : ℕ, N < n → ∀ x ∈ s, |u n x - F x| < ε

theorem gap1 :
    ∀ (q x : ℝ) (n : ℕ), 0 < q → q < 1 → |x| < q → 1 ≤ n →
      |x ^ n| < q ^ n := by
  intro q x n hq hq1 hx hn
  cases n with
  | zero => simp at hn
  | succ n =>
      clear hn
      by_cases hx0 : x = 0
      · subst x
        simpa using pow_pos hq (Nat.succ n)
      · rw [abs_pow]
        have hxa : 0 < |x| := abs_pos.mpr hx0
        induction n with
        | zero => simpa using hx
        | succ n ih =>
            simpa only [pow_succ] using
              (lt_trans
                (mul_lt_mul_of_pos_right ih hxa)
                (mul_lt_mul_of_pos_left hx (pow_pos hq (Nat.succ n))))

theorem gap2 :
    ∀ q : ℝ, 0 < q → q < 1 → Summable (fun n : ℕ => q ^ n) := by
  intro q hq hq1
  apply summable_geometric_of_norm_lt_one
  simpa [Real.norm_eq_abs, abs_of_pos hq] using hq1

theorem gap3 :
    ∀ (q x : ℝ), 0 < q → q < 1 → |x| < q →
      Summable (fun n : ℕ => |x ^ n|) := by
  intro q x hq hq1 hx
  have hx1 : |x| < 1 := lt_trans hx hq1
  have hs : Summable (fun n : ℕ => (|x| : ℝ) ^ n) := by
    apply summable_geometric_of_norm_lt_one
    simpa [Real.norm_eq_abs] using hx1
  simpa [abs_pow] using hs

theorem gap4 :
    ∀ q : ℝ, 0 < q → q < 1 →
      UniformlyConvergesOn partialSum geometricSum {x : ℝ | |x| < q} := by
  intro q hq0 hq1
  intro ε hε
  have hdelta : 0 < ε * (1 - q) :=
    mul_pos hε (sub_pos.mpr hq1)
  have hlim : Tendsto (fun n : ℕ => q ^ n) atTop (nhds 0) :=
    (gap2 q hq0 hq1).tendsto_atTop_zero
  obtain ⟨N, hN⟩ :=
    (Metric.tendsto_atTop.1 hlim) (ε * (1 - q)) hdelta
  refine ⟨N, ?_⟩
  intro n hn x hx
  change |x| < q at hx
  have hqx : x < q := lt_of_le_of_lt (le_abs_self x) hx
  have hxden : 0 < 1 - x := sub_pos.mpr (lt_trans hqx hq1)
  have hxne : 1 - x ≠ 0 := ne_of_gt hxden
  have hpoly : ∀ m : ℕ,
      (∑ i ∈ Finset.range m, x ^ i) * (1 - x) = 1 - x ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        rw [Finset.sum_range_succ, add_mul, ih, pow_succ]
        ring
  have hpart :
      partialSum n x * (1 - x) = 1 - x ^ (n + 1) := by
    simpa [partialSum] using hpoly (n + 1)
  have herr :
      partialSum n x - geometricSum x =
        -(x ^ (n + 1) / (1 - x)) := by
    calc
      partialSum n x - geometricSum x =
          (partialSum n x * (1 - x) - 1) / (1 - x) := by
            unfold geometricSum
            field_simp [hxne]
            <;> ring
      _ = ((1 - x ^ (n + 1)) - 1) / (1 - x) := by
            rw [hpart]
      _ = -(x ^ (n + 1) / (1 - x)) := by ring
  have hone : 1 ≤ n + 1 := by
    simpa [Nat.succ_eq_add_one] using
      Nat.succ_le_succ (Nat.zero_le n)
  have hterm : |x ^ (n + 1)| < q ^ (n + 1) :=
    gap1 q x (n + 1) hq0 hq1 hx hone
  have hNle : N ≤ n + 1 :=
    le_trans (Nat.le_of_lt hn) (Nat.le_succ n)
  have hN' := hN (n + 1) hNle
  have hqpow : q ^ (n + 1) < ε * (1 - q) := by
    simpa [Real.dist_eq, abs_of_pos hq0] using hN'
  have hdencomp : 1 - q ≤ 1 - x :=
    sub_le_sub_left (le_of_lt hqx) 1
  rw [herr, abs_neg, abs_div, abs_of_pos hxden]
  apply (div_lt_iff₀ hxden).2
  calc
    |x ^ (n + 1)| < q ^ (n + 1) := hterm
    _ < ε * (1 - q) := hqpow
    _ ≤ ε * (1 - x) :=
      mul_le_mul_of_nonneg_left hdencomp (le_of_lt hε)

theorem gap5 :
    ∀ (q x : ℝ), 0 < q → q < 1 → |x| < q →
      Summable (fun n : ℕ => |x ^ n|) ∧
        UniformlyConvergesOn partialSum geometricSum {y : ℝ | |y| < q} := by
  intro q x hq0 hq1 hx
  exact ⟨gap3 q x hq0 hq1 hx, gap4 q hq0 hq1⟩

end

end ProofGap.Exercise2767_1
