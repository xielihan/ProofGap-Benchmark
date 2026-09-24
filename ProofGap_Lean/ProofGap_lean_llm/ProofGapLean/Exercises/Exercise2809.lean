import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

namespace ProofGap.Exercise2809

noncomputable section

open Filter
open scoped BigOperators Topology

def term (n : ℕ) (x : ℝ) : ℝ :=
  Real.arctan (x / (n : ℝ) ^ 2)

def derivativeTerm (n : ℕ) (x : ℝ) : ℝ :=
  (n : ℝ) ^ 2 / ((n : ℝ) ^ 4 + x ^ 2)

def seriesFunction (x : ℝ) : ℝ :=
  ∑' k : ℕ, term (k + 1) x

def SeriesUniformlyConvergesOn
    (u : ℕ → ℝ → ℝ) (s : Set ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ m ≥ N, ∀ x ∈ s,
    |(∑ k ∈ Finset.range (m + 1), u k x) - f x| < ε

private theorem abs_arctan_le_abs (y : ℝ) :
    |Real.arctan y| ≤ |y| := by
  have hnonneg : ∀ z : ℝ, 0 ≤ z → Real.arctan z ≤ z := by
    intro z hz
    calc
      Real.arctan z ≤ Real.tan (Real.arctan z) :=
        Real.le_tan (Real.arctan_nonneg.mpr hz)
          (Real.arctan_lt_pi_div_two z)
      _ = z := Real.tan_arctan z
  by_cases hy : 0 ≤ y
  · rw [abs_of_nonneg (Real.arctan_nonneg.mpr hy), abs_of_nonneg hy]
    exact hnonneg y hy
  · have hny : 0 ≤ -y := neg_nonneg.mpr (le_of_not_ge hy)
    rw [abs_of_nonpos (Real.arctan_le_zero.mpr (le_of_not_ge hy)),
      abs_of_nonpos (le_of_not_ge hy)]
    simpa using hnonneg (-y) hny

theorem gap1 :
    ∀ (x : ℝ) (n : ℕ), 1 ≤ n →
      deriv (term n) x =
        1 / (1 + (x / (n : ℝ) ^ 2) ^ 2) * (1 / (n : ℝ) ^ 2) := by
  intro x n hn
  simpa [term] using
    ((Real.hasDerivAt_arctan (x / (n : ℝ) ^ 2)).comp x
      ((hasDerivAt_id x).div_const ((n : ℝ) ^ 2))).deriv

theorem gap2 :
    ∀ (x : ℝ) (n : ℕ), 1 ≤ n →
      1 / (1 + (x / (n : ℝ) ^ 2) ^ 2) * (1 / (n : ℝ) ^ 2) =
        derivativeTerm n x := by
  intro x n hn
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  unfold derivativeTerm
  field_simp [hnpos.ne']

theorem gap3 :
    ∀ (x : ℝ) (n : ℕ), 1 ≤ n →
      derivativeTerm n x ≤ 1 / (n : ℝ) ^ 2 := by
  intro x n hn
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hsqpos : 0 < (n : ℝ) ^ 2 := sq_pos_of_pos hnpos
  have hdenpos : 0 < (n : ℝ) ^ 4 + x ^ 2 := by
    nlinarith [sq_nonneg x, sq_pos_of_pos hsqpos]
  unfold derivativeTerm
  apply (div_le_iff₀ hdenpos).2
  rw [one_div, inv_mul_eq_div]
  apply (le_div_iff₀ hsqpos).2
  nlinarith [sq_nonneg x, show (n : ℝ) ^ 4 = ((n : ℝ) ^ 2) ^ 2 by ring]

theorem gap4 :
    ∀ (x : ℝ) (n : ℕ), 1 ≤ n →
      deriv (term n) x ≤ 1 / (n : ℝ) ^ 2 := by
  intro x n hn
  rw [gap1 x n hn, gap2 x n hn]
  exact gap3 x n hn

theorem gap5 :
    Summable (fun k : ℕ => 1 / (((k + 1 : ℕ) : ℝ) ^ 2)) := by
  have hbase : Summable (fun k : ℕ => 1 / ((k : ℝ) ^ 2)) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  simpa using (summable_nat_add_iff 1).2 hbase

theorem gap6 :
    SeriesUniformlyConvergesOn
      (fun k x => derivativeTerm (k + 1) x)
      Set.univ
      (fun x => ∑' k : ℕ, derivativeTerm (k + 1) x) := by
  have huniform := tendstoUniformlyOn_tsum_nat gap5 (s := Set.univ)
    (fun k x hx => by
      have hnonneg : 0 ≤ derivativeTerm (k + 1) x := by
        unfold derivativeTerm
        positivity
      rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
      exact gap3 x (k + 1) (Nat.succ_le_succ (Nat.zero_le k)))
  unfold SeriesUniformlyConvergesOn
  intro ε hε
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
    ((Metric.tendstoUniformlyOn_iff.1 huniform) ε hε)
  refine ⟨N, ?_⟩
  intro m hm x hx
  have hm' : N ≤ m + 1 := hm.trans (Nat.le_succ m)
  simpa [Real.dist_eq, abs_sub_comm] using hN (m + 1) hm' x hx

theorem gap7 :
    ∀ (x : ℝ) (n : ℕ), 1 ≤ n →
      |term n x| ≤ |x| / (n : ℝ) ^ 2 := by
  intro x n hn
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  calc
    |term n x| = |Real.arctan (x / (n : ℝ) ^ 2)| := rfl
    _ ≤ |x / (n : ℝ) ^ 2| := abs_arctan_le_abs _
    _ = |x| / (n : ℝ) ^ 2 := by
      rw [abs_div, abs_of_pos (sq_pos_of_pos hnpos)]

theorem gap8 :
    ∀ x : ℝ, Summable (fun k : ℕ => term (k + 1) x) := by
  intro x
  have hmajor := gap5.mul_left |x|
  refine hmajor.of_norm_bounded ?_
  intro k
  rw [Real.norm_eq_abs]
  simpa [div_eq_mul_inv] using
    gap7 x (k + 1) (Nat.succ_le_succ (Nat.zero_le k))

theorem gap9 :
    ∀ x : ℝ,
      deriv seriesFunction x =
        ∑' k : ℕ, deriv (term (k + 1)) x := by
  have hdiff : ∀ k : ℕ, Differentiable ℝ (term (k + 1)) := by
    intro k x
    exact ((Real.hasDerivAt_arctan
      (x / (((k + 1 : ℕ) : ℝ) ^ 2))).comp x
        ((hasDerivAt_id x).div_const (((k + 1 : ℕ) : ℝ) ^ 2))).differentiableAt
  have hbound : ∀ k : ℕ, ∀ x : ℝ,
      ‖deriv (term (k + 1)) x‖ ≤
        1 / (((k + 1 : ℕ) : ℝ) ^ 2) := by
    intro k x
    rw [gap1 x (k + 1) (Nat.succ_le_succ (Nat.zero_le k)),
      gap2 x (k + 1) (Nat.succ_le_succ (Nat.zero_le k))]
    have hnonneg : 0 ≤ derivativeTerm (k + 1) x := by
      unfold derivativeTerm
      positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
    exact gap3 x (k + 1) (Nat.succ_le_succ (Nat.zero_le k))
  have hzero : Summable (fun k : ℕ => term (k + 1) 0) := by
    simp [term]
  intro x
  unfold seriesFunction
  exact deriv_tsum_apply (u := fun k : ℕ =>
      1 / (((k + 1 : ℕ) : ℝ) ^ 2))
    (g := fun k : ℕ => term (k + 1)) (y₀ := 0)
    gap5 hdiff hbound hzero x

theorem gap10 :
    ∀ x : ℝ,
      deriv seriesFunction x =
        ∑' k : ℕ, deriv (term (k + 1)) x := by
  exact gap9

end

end ProofGap.Exercise2809
