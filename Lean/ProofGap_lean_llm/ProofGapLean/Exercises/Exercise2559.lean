import ProofGapLean.Prelude.Sequences
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Lean.Elab.Tactic.Omega
import Mathlib.Topology.Defs.Filter
import Mathlib.Order.Filter.AtTopBot.Defs

namespace ProofGap.Exercise2559

noncomputable section

def evenTerm (n : ℕ) : ℝ := 1 / (2 * (n : ℝ))
def oddTerm (n : ℕ) : ℝ := 1 / (2 * (n : ℝ) - 1)

theorem gap1 :
    ∀ n : ℕ, 1 ≤ n → oddTerm n > evenTerm n := by
  intro n hn
  unfold oddTerm evenTerm
  have hn' : (1 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hn
  apply one_div_lt_one_div_of_lt
  · nlinarith
  · linarith

theorem gap2
    (hcompare : ∀ n : ℕ, 1 ≤ n → oddTerm n > evenTerm n) :
    ∀ n : ℕ, 1 ≤ n → evenTerm n > 0 := by
  intro n hn
  unfold evenTerm
  have hn' : (1 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hn
  apply one_div_pos.mpr
  nlinarith

theorem gap3
    (hcompare : ∀ n : ℕ, 1 ≤ n → oddTerm n > evenTerm n)
    (heven : ∀ n : ℕ, 1 ≤ n → evenTerm n > 0) :
    ∀ n : ℕ, 1 ≤ n → oddTerm n > 0 := by
  intro n hn
  exact lt_trans (heven n hn) (hcompare n hn)

theorem gap4
    (hcompare : ∀ n : ℕ, 1 ≤ n → oddTerm n > evenTerm n)
    (heven : ∀ n : ℕ, 1 ≤ n → evenTerm n > 0)
    (hodd : ∀ n : ℕ, 1 ≤ n → oddTerm n > 0) :
    ¬ Summable evenTerm := by
  intro hs
  let S : ℕ → ℝ := fun m => Finset.sum (Finset.range m) evenTerm
  have hrange :
      Filter.Tendsto (fun n : ℕ => Finset.range n)
        Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop.2 ?_
    intro s
    refine (Filter.eventually_ge_atTop
      (s.sup (fun k : ℕ => k) + 1)).mono ?_
    intro n hn
    intro k hk
    simp only [Finset.mem_range]
    have hk_le : k ≤ s.sup (fun j : ℕ => j) := by
      exact Finset.le_sup (s := s) (f := fun j : ℕ => j) hk
    omega
  have hfinite :
      Filter.Tendsto (fun s : Finset ℕ => s.sum evenTerm)
        Filter.atTop (nhds (tsum evenTerm)) := hs.hasSum
  have hS : Filter.Tendsto S Filter.atTop (nhds (tsum evenTerm)) := by
    simpa only [S, Function.comp_apply] using (hfinite.comp hrange)
  rcases (Metric.tendsto_atTop.1 hS) (1 / 16 : ℝ) (by norm_num) with ⟨N, hN⟩
  let M : ℕ := max N 1
  have hNM : N ≤ M := by
    simp [M]
  have hMone : 1 ≤ M := by
    simp [M]
  have hMpos : 0 < M := by
    omega
  have hcloseM : dist (S M) (tsum evenTerm) < (1 / 16 : ℝ) :=
    hN M hNM
  have hcloseM' : dist (tsum evenTerm) (S M) < (1 / 16 : ℝ) := by
    calc
      dist (tsum evenTerm) (S M) = dist (S M) (tsum evenTerm) := dist_comm _ _
      _ < (1 / 16 : ℝ) := hcloseM
  have hclose2M : dist (S (2 * M)) (tsum evenTerm) < (1 / 16 : ℝ) := by
    apply hN (2 * M)
    omega
  have hsmallDist : dist (S (2 * M)) (S M) < (1 / 8 : ℝ) := by
    calc
      dist (S (2 * M)) (S M) ≤
          dist (S (2 * M)) (tsum evenTerm) + dist (tsum evenTerm) (S M) :=
        dist_triangle _ _ _
      _ < (1 / 8 : ℝ) := by linarith
  have hsmall : abs (S (2 * M) - S M) < (1 / 8 : ℝ) := by
    simpa only [Real.dist_eq] using hsmallDist
  have hMr : (0 : ℝ) < (M : ℝ) := by
    exact_mod_cast hMpos
  have hMne : (M : ℝ) ≠ 0 := ne_of_gt hMr
  have hcard : (Finset.Ico M (2 * M)).card = M := by
    simp only [Nat.card_Ico]
    omega
  have hconst :
      Finset.sum (Finset.Ico M (2 * M))
          (fun _ => 1 / (4 * (M : ℝ))) = (1 : ℝ) / 4 := by
    simp only [Finset.sum_const, hcard, nsmul_eq_mul]
    field_simp [hMne]
  have hpoint :
      ∀ k ∈ Finset.Ico M (2 * M),
        1 / (4 * (M : ℝ)) ≤ evenTerm k := by
    intro k hk
    rcases Finset.mem_Ico.mp hk with ⟨hkLower, hkUpper⟩
    have hkposNat : 0 < k := by omega
    have hkpos : (0 : ℝ) < (k : ℝ) := by
      exact_mod_cast hkposNat
    have hkUpper' : (k : ℝ) < 2 * (M : ℝ) := by
      exact_mod_cast hkUpper
    unfold evenTerm
    apply le_of_lt
    apply one_div_lt_one_div_of_lt
    · nlinarith
    · nlinarith
  have hblock :
      (1 : ℝ) / 4 ≤ Finset.sum (Finset.Ico M (2 * M)) evenTerm := by
    calc
      (1 : ℝ) / 4 =
          Finset.sum (Finset.Ico M (2 * M))
            (fun _ => 1 / (4 * (M : ℝ))) := hconst.symm
      _ ≤ Finset.sum (Finset.Ico M (2 * M)) evenTerm := by
        refine Finset.sum_le_sum ?_
        intro k hk
        exact hpoint k hk
  have hsubset : Finset.range M ⊆ Finset.range (2 * M) := by
    intro k hk
    simp only [Finset.mem_range] at hk ⊢
    omega
  have hset :
      Finset.range (2 * M) \ Finset.range M = Finset.Ico M (2 * M) := by
    ext k
    simp only [Finset.mem_sdiff, Finset.mem_range, Finset.mem_Ico]
    omega
  have htailEq :
      S (2 * M) - S M = Finset.sum (Finset.Ico M (2 * M)) evenTerm := by
    simp only [S]
    rw [← Finset.sum_sdiff hsubset, hset]
    simp
  have hlower : (1 : ℝ) / 4 ≤ S (2 * M) - S M := by
    rw [htailEq]
    exact hblock
  have habsLower : (1 : ℝ) / 4 ≤ abs (S (2 * M) - S M) :=
    le_trans hlower (le_abs_self _)
  linarith

theorem gap5
    (hcompare : ∀ n : ℕ, 1 ≤ n → oddTerm n > evenTerm n)
    (heven : ∀ n : ℕ, 1 ≤ n → evenTerm n > 0)
    (hodd : ∀ n : ℕ, 1 ≤ n → oddTerm n > 0)
    (hdiv : ¬ Summable evenTerm) :
    ¬ Summable oddTerm := by
  intro hsodd
  have hsodd' : Summable (fun n : ℕ => oddTerm (n + 1)) := by
    rw [summable_nat_add_iff 1]
    exact hsodd
  have hseven' : Summable (fun n : ℕ => evenTerm (n + 1)) := by
    refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hsodd'
    · exact (heven (n + 1) (by omega)).le
    · exact (hcompare (n + 1) (by omega)).le
  apply hdiv
  rw [← summable_nat_add_iff 1]
  exact hseven'

end

end ProofGap.Exercise2559
