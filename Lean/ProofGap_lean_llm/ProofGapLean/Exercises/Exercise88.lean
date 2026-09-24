import ProofGapLean.Prelude.Sequences
import ProofGapLean.Prelude.Finite

open Filter Topology

namespace ProofGap.Exercise88

noncomputable section

def x (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 n, 1 / (k : ℝ)

def harmonicTail (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc (n + 1) (2 * n), 1 / (k : ℝ)

def constantTail (n : ℕ) : ℝ :=
  ∑ _k ∈ Finset.Icc (n + 1) (2 * n), 1 / (2 * n : ℝ)

def IsCauchy (u : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ m n : ℕ, N < n → N < m → |u n - u m| < ε

def Convergent (u : ℕ → ℝ) : Prop :=
  ∃ l : ℝ, Tendsto u atTop (𝓝 l)

/-- Exercise 88, gap 1; choose m=2n for each n. -/
theorem gap1 :
    ∀ n : ℕ, 0 < n →
      ∃ m : ℕ, m = 2 * n ∧ |x m - x n| = harmonicTail n := by
  intro n hn
  refine ⟨2 * n, rfl, ?_⟩
  have hnm : n < 2 * n := by omega
  have hdiff : x (2 * n) - x n = harmonicTail n := by
    unfold x harmonicTail
    simp_rw [← Finset.Ico_add_one_right_eq_Icc]
    have hconsecutive := Finset.sum_Ico_consecutive
      (fun k => 1 / (k : ℝ))
      (show 1 ≤ n + 1 by omega) (show n + 1 ≤ 2 * n + 1 by omega)
    linarith
  rw [hdiff, abs_of_pos]
  unfold harmonicTail
  have hs : n + 1 ∈ Finset.Icc (n + 1) (2 * n) :=
    Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩
  have hsingle :
      1 / ((n + 1 : ℕ) : ℝ) ≤
        ∑ k ∈ Finset.Icc (n + 1) (2 * n), 1 / (k : ℝ) := by
    exact Finset.single_le_sum
      (s := Finset.Icc (n + 1) (2 * n))
      (f := fun k : ℕ => 1 / (k : ℝ))
      (fun k hk => by
        have hkpos : 0 < k := by
          have := (Finset.mem_Icc.mp hk).1
          omega
        positivity) hs
  exact lt_of_lt_of_le (by positivity : 0 < 1 / ((n + 1 : ℕ) : ℝ))
    hsingle

/-- Exercise 88, gap 2; strictness fails at n=1. -/
theorem gap2 :
    ∀ n : ℕ, 1 < n → harmonicTail n > constantTail n := by
  intro n hn
  unfold harmonicTail constantTail
  let S := Finset.Icc (n + 1) (2 * n)
  let s := n + 1
  have hs : s ∈ S := by
    dsimp [s, S]
    exact Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩
  have hslt : 1 / (2 * n : ℝ) < 1 / (s : ℝ) := by
    have hsR : (0 : ℝ) < s := by positivity
    have hltR : (s : ℝ) < 2 * n := by
      dsimp [s]
      exact_mod_cast (by omega : n + 1 < 2 * n)
    exact one_div_lt_one_div_of_lt hsR hltR
  have herase :
      (∑ k ∈ S.erase s, 1 / (2 * n : ℝ)) ≤
        ∑ k ∈ S.erase s, 1 / (k : ℝ) := by
    apply Finset.sum_le_sum
    intro k hk
    have hkS : k ∈ S := Finset.mem_of_mem_erase hk
    have hkI : k ∈ Finset.Icc (n + 1) (2 * n) := by
      simpa [S] using hkS
    have hkpos : 0 < (k : ℝ) := by
      have : 0 < k :=
        lt_of_lt_of_le (by omega : 0 < n + 1) (Finset.mem_Icc.mp hkI).1
      exact_mod_cast this
    have hkle : k ≤ 2 * n := by
      exact (Finset.mem_Icc.mp hkI).2
    exact one_div_le_one_div_of_le hkpos (by exact_mod_cast hkle)
  change (∑ k ∈ S, 1 / (2 * n : ℝ)) < ∑ k ∈ S, 1 / (k : ℝ)
  calc
    (∑ k ∈ S, 1 / (2 * n : ℝ)) =
        1 / (2 * n : ℝ) + ∑ k ∈ S.erase s, 1 / (2 * n : ℝ) := by
          rw [add_comm, Finset.sum_erase_add _ _ hs]
    _ < 1 / (s : ℝ) + ∑ k ∈ S.erase s, 1 / (2 * n : ℝ) :=
      by simpa [add_comm] using
        add_lt_add_right hslt (∑ k ∈ S.erase s, 1 / (2 * n : ℝ))
    _ ≤ 1 / (s : ℝ) + ∑ k ∈ S.erase s, 1 / (k : ℝ) :=
      add_le_add (le_refl _) herase
    _ = ∑ k ∈ S, 1 / (k : ℝ) := by
      rw [add_comm, Finset.sum_erase_add _ _ hs]

/-- Exercise 88, gap 3. -/
theorem gap3 :
    ∀ n : ℕ, 0 < n → constantTail n = 1 / 2 := by
  intro n hn
  unfold constantTail
  have hcard : (Finset.Icc (n + 1) (2 * n)).card = n := by
    rw [Nat.card_Icc]
    omega
  rw [Finset.sum_const, hcard]
  simp only [nsmul_eq_mul]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  field_simp

/-- Exercise 88, gap 4; m depends on n. -/
theorem gap4 :
    ∀ n : ℕ, 1 < n →
      ∃ m : ℕ, n < m ∧ |x m - x n| > 1 / 2 := by
  intro n hn
  rcases gap1 n (by omega) with ⟨m, rfl, htail⟩
  refine ⟨2 * n, by omega, ?_⟩
  rw [htail]
  rw [← gap3 n (by omega)]
  exact gap2 n hn

/-- Exercise 88, gap 5. -/
theorem gap5 :
    ¬ IsCauchy x := by
  intro hc
  rcases hc (1 / 2) (by norm_num) with ⟨N, hN⟩
  let n := max (N + 1) 2
  have hNn : N < n := by
    dsimp [n]
    omega
  have hn : 1 < n := by
    dsimp [n]
    omega
  rcases gap4 n hn with ⟨m, hnm, hlarge⟩
  have hsmall := hN m n hNn (lt_trans hNn hnm)
  rw [abs_sub_comm] at hsmall
  linarith

/-- Exercise 88, gap 6. -/
theorem gap6 :
    ¬ Convergent x := by
  intro hconv
  rcases hconv with ⟨l, hl⟩
  apply gap5
  have hc : CauchySeq x := hl.cauchySeq
  rw [Metric.cauchySeq_iff] at hc
  intro ε hε
  rcases hc ε hε with ⟨N, hN⟩
  exact ⟨N, fun m n hn hm => by
    have hd := hN n (by omega) m (by omega)
    simpa [Real.dist_eq] using hd⟩

/-- Exercise 88, gap 7. -/
theorem gap7
    (h : ¬ Convergent x) :
    ¬ Convergent x := by
  exact h

end

end ProofGap.Exercise88
