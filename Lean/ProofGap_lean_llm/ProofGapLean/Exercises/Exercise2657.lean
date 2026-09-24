import ProofGapLean.Prelude.Analysis
import Mathlib.Topology.Algebra.InfiniteSum.Basic

namespace ProofGap.Exercise2657

noncomputable section

open Filter
open scoped BigOperators

def blockSum (p : ℕ → ℕ) (a : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.Ico (p k) (p (k + 1)), a i

def delta (a : ℕ → ℝ) (n s : ℕ) : ℝ :=
  ∑ i ∈ Finset.Icc n (n + s), a i

def middleBlocks (p : ℕ → ℕ) (a : ℕ → ℝ) (r q : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc (r + 1) (r + q), blockSum p a k

def epsilonPart (m : ℕ) (ε : ℝ) : ℝ :=
  ε / (2 * m + 1)

def HasEndDecomposition
    (p : ℕ → ℕ) (a : ℕ → ℝ) (m N₁ n s : ℕ) (η : ℝ) : Prop :=
  ∃ B B' : ℝ, ∃ r q : ℕ,
    delta a n s = B + middleBlocks p a (N₁ + r) q + B' ∧
      |B| ≤ m * η ∧ |B'| ≤ m * η

private theorem exists_block_index
    (p : ℕ → ℕ) (hp : StrictMono p) {N n : ℕ} (hn : p N ≤ n) :
    ∃ k : ℕ, N ≤ k ∧ p k ≤ n ∧ n < p (k + 1) := by
  have hex : ∃ t : ℕ, n < p t := by
    refine ⟨n + 1, ?_⟩
    exact lt_of_lt_of_le (Nat.lt_succ_self n) (hp.id_le (n + 1))
  let t := Nat.find hex
  have ht : n < p t := Nat.find_spec hex
  have hNt : N < t := by
    by_contra h
    have htN : t ≤ N := Nat.le_of_not_gt h
    have hptN : p t ≤ p N := hp.monotone htN
    omega
  let k := t - 1
  have hkt : k < t := by
    dsimp [k]
    omega
  have hpk : p k ≤ n := Nat.le_of_not_gt (Nat.find_min hex hkt)
  refine ⟨k, ?_, hpk, ?_⟩
  · dsimp [k]
    omega
  · have hks : k + 1 = t := by
      dsimp [k]
      omega
    rwa [hks]

private theorem abs_sum_le_card_of_abs_le_one
    (a : ℕ → ℝ) (s : Finset ℕ)
    (hsmall : ∀ i ∈ s, |a i| ≤ 1) :
    |∑ i ∈ s, a i| ≤ (s.card : ℝ) := by
  calc
    |∑ i ∈ s, a i| ≤ ∑ i ∈ s, |a i| :=
      Finset.abs_sum_le_sum_abs a s
    _ ≤ ∑ _i ∈ s, (1 : ℝ) := Finset.sum_le_sum fun i hi => hsmall i hi
    _ = (s.card : ℝ) := by simp

private theorem sum_blocks_Icc
    (p : ℕ → ℕ) (a : ℕ → ℝ) (hp : Monotone p) (j q : ℕ) :
    (∑ k ∈ Finset.Icc (j + 1) (j + q), blockSum p a k) =
      ∑ i ∈ Finset.Ico (p (j + 1)) (p (j + q + 1)), a i := by
  induction q with
  | zero => simp
  | succ q ih =>
      rw [show j + (q + 1) = (j + q) + 1 by omega,
        Finset.sum_Icc_succ_top (by omega), ih, blockSum]
      rw [Finset.sum_Ico_consecutive]
      · exact hp (by omega)
      · exact hp (by omega)

theorem gap1
    (p : ℕ → ℕ) (m : ℕ)
    (hbound : ∀ n : ℕ, p (n + 1) - p n ≤ m) :
    ∀ n : ℕ, p (n + 1) - p n ≤ m := by
  exact hbound

theorem gap2 (m : ℕ) :
    ∀ ε : ℝ, 0 < ε → 0 < epsilonPart m ε := by
  intro ε hε
  unfold epsilonPart
  positivity

theorem gap3
    (a : ℕ → ℝ) (ha : Tendsto a atTop (nhds 0)) (m : ℕ) :
    ∀ ε : ℝ, 0 < ε →
      ∃ N' : ℕ, 1 ≤ N' ∧ ∀ n : ℕ, N' ≤ n →
        |a n| < epsilonPart m ε := by
  intro ε hε
  have hpart : 0 < epsilonPart m ε := gap2 m ε hε
  rcases (Metric.tendsto_atTop.1 ha _ hpart) with ⟨N, hN⟩
  refine ⟨max 1 N, le_max_left _ _, ?_⟩
  intro n hn
  have hdist := hN n (le_trans (le_max_right 1 N) hn)
  simpa [Real.dist_eq] using hdist

theorem gap4
    (A : ℕ → ℝ) (hA : Summable (fun n : ℕ => A (n + 1))) (m : ℕ) :
    ∀ ε : ℝ, 0 < ε →
      ∃ N₁ : ℕ, ∀ n : ℕ, N₁ ≤ n → ∀ q : ℕ,
        |∑ k ∈ Finset.Icc n (n + q), A k| < epsilonPart m ε := by
  intro ε hε
  have hpart : 0 < epsilonPart m ε := gap2 m ε hε
  have hAll : Summable A := (summable_nat_add_iff 1).1 hA
  have hpartial : Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n, A k)
      atTop (nhds (∑' k, A k)) := hAll.hasSum.tendsto_sum_nat
  rcases (Metric.cauchySeq_iff.1 hpartial.cauchySeq _ hpart) with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn q
  have hdist := hN (n + q + 1) (by omega) n hn
  have hsum :
      (∑ k ∈ Finset.Icc n (n + q), A k) =
        (∑ k ∈ Finset.range (n + q + 1), A k) -
          ∑ k ∈ Finset.range n, A k := by
    rw [← Finset.Ico_add_one_right_eq_Icc,
      Finset.sum_Ico_eq_sub A (by omega)]
  rw [hsum]
  simpa [Real.dist_eq, abs_sub_comm] using hdist

theorem gap5
    (p : ℕ → ℕ) (a : ℕ → ℝ) (m N₁ : ℕ)
    (hp : StrictMono p)
    (hlen : ∀ k : ℕ, p (k + 1) - p k ≤ m)
    (hsmall : ∀ i : ℕ, p N₁ ≤ i → |a i| < (1 : ℝ)) :
    ∀ n : ℕ, p N₁ ≤ n → ∀ s : ℕ,
      HasEndDecomposition p a m N₁ n s 1 := by
  intro n hn s
  have hblockBound (k : ℕ) (hk : N₁ ≤ k) (S : Finset ℕ)
      (hS : S ⊆ Finset.Ico (p k) (p (k + 1))) :
      |∑ i ∈ S, a i| ≤ (m : ℝ) := by
    calc
      |∑ i ∈ S, a i| ≤ (S.card : ℝ) := by
        apply abs_sum_le_card_of_abs_le_one
        intro i hi
        have hiBlock := Finset.mem_Ico.mp (hS hi)
        exact (hsmall i ((hp.monotone hk).trans hiBlock.1)).le
      _ ≤ ((Finset.Ico (p k) (p (k + 1))).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hS
      _ = (p (k + 1) - p k : ℕ) := by
        norm_cast
        exact Nat.card_Ico _ _
      _ ≤ (m : ℝ) := by exact_mod_cast hlen k
  obtain ⟨j, hjN, hpj, hnj⟩ := exists_block_index p hp hn
  have hendN : p N₁ ≤ n + s := hn.trans (Nat.le_add_right n s)
  obtain ⟨l, hlN, hpl, hel⟩ := exists_block_index p hp hendN
  have hjl : j ≤ l := by
    by_contra h
    have hlj : l < j := Nat.lt_of_not_ge h
    have hple : p (l + 1) ≤ p j := hp.monotone (by omega)
    omega
  let r := j - N₁
  have hr : N₁ + r = j := by
    dsimp [r]
    omega
  by_cases hjleq : j = l
  · subst l
    have hsubset : Finset.Icc n (n + s) ⊆
        Finset.Ico (p j) (p (j + 1)) := by
      intro i hi
      have hi' := Finset.mem_Icc.mp hi
      exact Finset.mem_Ico.mpr ⟨hpj.trans hi'.1, hi'.2.trans_lt hel⟩
    refine ⟨delta a n s, 0, r, 0, ?_, ?_, ?_⟩
    · simp [middleBlocks]
    · simpa using hblockBound j hjN (Finset.Icc n (n + s)) hsubset
    · simp
  · have hjl' : j < l := lt_of_le_of_ne hjl hjleq
    let q := l - j - 1
    have hq : j + q + 1 = l := by
      dsimp [q]
      omega
    let B : ℝ := ∑ i ∈ Finset.Ico n (p (j + 1)), a i
    let B' : ℝ := ∑ i ∈ Finset.Icc (p l) (n + s), a i
    have hmiddle : middleBlocks p a (N₁ + r) q =
        ∑ i ∈ Finset.Ico (p (j + 1)) (p l), a i := by
      unfold middleBlocks
      rw [hr]
      simpa [hq] using sum_blocks_Icc p a hp.monotone j q
    have heq : delta a n s = B + middleBlocks p a (N₁ + r) q + B' := by
      unfold delta B B'
      rw [hmiddle, ← Finset.Ico_add_one_right_eq_Icc,
        ← Finset.Ico_add_one_right_eq_Icc]
      rw [Finset.sum_Ico_consecutive a hnj.le (hp.monotone hjl')]
      simpa [Nat.succ_eq_add_one] using
        (Finset.sum_Ico_consecutive a
          (hnj.le.trans (hp.monotone hjl'))
          (hpl.trans (Nat.le_succ _))).symm
    have hleftSubset : Finset.Ico n (p (j + 1)) ⊆
        Finset.Ico (p j) (p (j + 1)) := by
      intro i hi
      have hi' := Finset.mem_Ico.mp hi
      exact Finset.mem_Ico.mpr ⟨hpj.trans hi'.1, hi'.2⟩
    have hrightSubset : Finset.Icc (p l) (n + s) ⊆
        Finset.Ico (p l) (p (l + 1)) := by
      intro i hi
      have hi' := Finset.mem_Icc.mp hi
      exact Finset.mem_Ico.mpr ⟨hi'.1, hi'.2.trans_lt hel⟩
    refine ⟨B, B', r, q, heq, ?_, ?_⟩
    · simpa [B] using hblockBound j hjN (Finset.Ico n (p (j + 1))) hleftSubset
    · simpa [B'] using hblockBound l hlN (Finset.Icc (p l) (n + s)) hrightSubset

theorem gap6
    (p : ℕ → ℕ) (a : ℕ → ℝ) (m N₁ n s : ℕ) (η : ℝ)
    (hdecomp : HasEndDecomposition p a m N₁ n s η) :
    ∃ B : ℝ, |B| ≤ m * η := by
  rcases hdecomp with ⟨B, B', r, q, heq, hB, hB'⟩
  exact ⟨B, hB⟩

theorem gap7
    (p : ℕ → ℕ) (m k : ℕ) (η : ℝ)
    (hη : 0 ≤ η)
    (hlen : p (k + 1) - p k ≤ m) :
    (p (k + 1) - p k : ℕ) * η ≤ m * η := by
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hlen) hη

theorem gap8
    (p : ℕ → ℕ) (a : ℕ → ℝ) (m N₁ n s : ℕ) (η : ℝ)
    (hdecomp : HasEndDecomposition p a m N₁ n s η) :
    ∃ B : ℝ, |B| ≤ m * η := by
  exact gap6 p a m N₁ n s η hdecomp

theorem gap9
    (p : ℕ → ℕ) (a : ℕ → ℝ) (m N₁ n s : ℕ) (η : ℝ)
    (hdecomp : HasEndDecomposition p a m N₁ n s η) :
    ∃ B' : ℝ, |B'| ≤ m * η := by
  rcases hdecomp with ⟨B, B', r, q, heq, hB, hB'⟩
  exact ⟨B', hB'⟩

theorem gap10
    (p : ℕ → ℕ) (m k : ℕ) (η : ℝ)
    (hη : 0 ≤ η)
    (hlen : p (k + 1) - p k ≤ m) :
    (p (k + 1) - p k : ℕ) * η ≤ m * η := by
  exact gap7 p m k η hη hlen

theorem gap11
    (p : ℕ → ℕ) (a : ℕ → ℝ) (m N₁ n s : ℕ) (η : ℝ)
    (hdecomp : HasEndDecomposition p a m N₁ n s η) :
    ∃ B' : ℝ, |B'| ≤ m * η := by
  exact gap9 p a m N₁ n s η hdecomp

theorem gap12
    (p : ℕ → ℕ) (a : ℕ → ℝ) (N₁ : ℕ) (η : ℝ)
    (hblockCauchy : ∀ r q : ℕ,
      |middleBlocks p a (N₁ + r) q| < η) :
    ∀ r q : ℕ, |middleBlocks p a (N₁ + r) q| < η := by
  exact hblockCauchy

theorem gap13
    (p : ℕ → ℕ) (a : ℕ → ℝ) (m N₁ n s : ℕ) (η : ℝ)
    (hdecomp : HasEndDecomposition p a m N₁ n s η) :
    ∃ B B' : ℝ, ∃ r q : ℕ,
      |delta a n s| ≤
        |B| + |middleBlocks p a (N₁ + r) q| + |B'| := by
  rcases hdecomp with ⟨B, B', r, q, heq, hB, hB'⟩
  refine ⟨B, B', r, q, ?_⟩
  rw [heq]
  calc
    |B + middleBlocks p a (N₁ + r) q + B'| ≤
        |B + middleBlocks p a (N₁ + r) q| + |B'| := abs_add_le _ _
    _ ≤ (|B| + |middleBlocks p a (N₁ + r) q|) + |B'| :=
      by
        simpa [add_comm, add_left_comm, add_assoc] using
          add_le_add_right (abs_add_le B (middleBlocks p a (N₁ + r) q)) |B'|

theorem gap14
    (p : ℕ → ℕ) (a : ℕ → ℝ) (m N₁ n s : ℕ) (η : ℝ)
    (hη : 0 < η)
    (hdecomp : HasEndDecomposition p a m N₁ n s η)
    (hmiddle : ∀ r q : ℕ, |middleBlocks p a (N₁ + r) q| < η) :
    |delta a n s| < (2 * m + 1) * η := by
  rcases hdecomp with ⟨B, B', r, q, heq, hB, hB'⟩
  rw [heq]
  have htri :
      |B + middleBlocks p a (N₁ + r) q + B'| ≤
        |B| + |middleBlocks p a (N₁ + r) q| + |B'| := by
    calc
      |B + middleBlocks p a (N₁ + r) q + B'| ≤
          |B + middleBlocks p a (N₁ + r) q| + |B'| := abs_add_le _ _
      _ ≤ (|B| + |middleBlocks p a (N₁ + r) q|) + |B'| :=
        by
          simpa [add_comm, add_left_comm, add_assoc] using
            add_le_add_right (abs_add_le B (middleBlocks p a (N₁ + r) q)) |B'|
  calc
    |B + middleBlocks p a (N₁ + r) q + B'| ≤
        |B| + |middleBlocks p a (N₁ + r) q| + |B'| := htri
    _ < m * η + η + m * η := by
      linarith [hmiddle r q]
    _ = (2 * m + 1) * η := by
      push_cast
      ring

theorem gap15 (m : ℕ) :
    ∀ ε : ℝ, (2 * m + 1) * epsilonPart m ε = ε := by
  intro ε
  unfold epsilonPart
  have hden : (2 * (m : ℝ) + 1) ≠ 0 := by positivity
  field_simp

theorem gap16
    (a : ℕ → ℝ) :
    (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ s : ℕ, |delta a n s| < ε) →
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ s : ℕ, |delta a n s| < ε := by
  exact id

theorem gap17
    (a : ℕ → ℝ)
    (hcauchy : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ s : ℕ, |delta a n s| < ε) :
    ProofGap.SeriesConverges (fun n : ℕ => a (n + 1)) := by
  let partialS : ℕ → ℝ := fun n => ∑ k ∈ Finset.range n, a (k + 1)
  have hpartial : CauchySeq partialS := by
    apply Metric.cauchySeq_iff.2
    intro ε hε
    rcases hcauchy ε hε with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro m hm n hn
    wlog hmn : m ≤ n generalizing m n
    · rw [dist_comm]
      exact this n hn m hm (le_of_not_ge hmn)
    by_cases heq : m = n
    · subst n
      simpa using hε
    have hmn' : m < n := lt_of_le_of_ne hmn heq
    have htail := hN (m + 1) (by omega) (n - m - 1)
    have hsum : partialS n - partialS m = delta a (m + 1) (n - m - 1) := by
      calc
        partialS n - partialS m =
            ∑ k ∈ Finset.Ico m n, a (k + 1) := by
          symm
          exact Finset.sum_Ico_eq_sub (fun k => a (k + 1)) hmn
        _ = ∑ k ∈ Finset.Ico (m + 1) (n + 1), a k := by
          simpa [Nat.add_comm] using Finset.sum_Ico_add a m n 1
        _ = ∑ k ∈ Finset.Icc (m + 1) n, a k := by
          rw [Finset.Ico_add_one_right_eq_Icc]
        _ = delta a (m + 1) (n - m - 1) := by
          unfold delta
          congr 3
          omega
    rw [Real.dist_eq, abs_sub_comm, hsum]
    exact htail
  rcases cauchySeq_tendsto_of_complete hpartial with ⟨s, hs⟩
  change Summable (fun n : ℕ => a (n + 1))
    (SummationFilter.conditional ℕ)
  refine ⟨s, ?_⟩
  rw [HasSum, SummationFilter.conditional_filter_eq_map_range,
    Filter.tendsto_map'_iff, Function.comp_def]
  exact hs

theorem gap18
    (a : ℕ → ℝ)
    (hsum : Summable (fun n : ℕ => a (n + 1))) :
    Summable (fun n : ℕ => a (n + 1)) := by
  exact hsum

end

end ProofGap.Exercise2657
