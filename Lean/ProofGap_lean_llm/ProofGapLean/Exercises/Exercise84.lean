import ProofGapLean.Prelude.Full

open Filter Topology

namespace ProofGap.Exercise84

noncomputable section

def term (k : ℕ) : ℝ :=
  Real.cos (Nat.factorial k : ℝ) / ((k : ℝ) * ((k : ℝ) + 1))

def x (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 n, term k

def tail (n m : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc (n + 1) m, term k

def squareTail (n m : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc (n + 1) m, 1 / (k : ℝ) ^ 2

def telescopingTail (n m : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc (n + 1) m,
    (1 / ((k : ℝ) - 1) - 1 / (k : ℝ))

def IsCauchy (u : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ m n : ℕ, N < n → n < m → |u m - u n| < ε

def Convergent (u : ℕ → ℝ) : Prop :=
  ∃ l : ℝ, Tendsto u atTop (𝓝 l)

/-- Source: `proof_gap/exercise_84/1.txt`. -/
theorem gap1 :
    ∀ m n : ℕ, n < m → |x m - x n| = |tail n m| := by
  intro m n hnm
  congr 1
  unfold x tail
  simp_rw [← Finset.Ico_add_one_right_eq_Icc]
  have hconsecutive := Finset.sum_Ico_consecutive term
    (show 1 ≤ n + 1 by omega) (show n + 1 ≤ m + 1 by omega)
  linarith

/-- Source: `proof_gap/exercise_84/2.txt`. -/
theorem gap2 :
    ∀ m n : ℕ, n < m → |tail n m| < squareTail n m := by
  intro m n hnm
  have htriangle :
      |tail n m| ≤ ∑ k ∈ Finset.Icc (n + 1) m, |term k| := by
    unfold tail
    exact Finset.abs_sum_le_sum_abs _ _
  have hstrict :
      (∑ k ∈ Finset.Icc (n + 1) m, |term k|) <
        ∑ k ∈ Finset.Icc (n + 1) m, 1 / (k : ℝ) ^ 2 := by
    apply Finset.sum_lt_sum_of_nonempty
    · exact ⟨n + 1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩
    · intro k hk
      have hkpos : 0 < (k : ℝ) := by
        have : 0 < k := lt_of_lt_of_le (Nat.succ_pos n) (Finset.mem_Icc.mp hk).1
        exact_mod_cast this
      have hden : 0 < (k : ℝ) * ((k : ℝ) + 1) :=
        mul_pos hkpos (by linarith)
      have hcos : |Real.cos (Nat.factorial k : ℝ)| ≤ 1 :=
        Real.abs_cos_le_one _
      have hle :
          |term k| ≤ 1 / ((k : ℝ) * ((k : ℝ) + 1)) := by
        unfold term
        rw [abs_div, abs_of_pos hden]
        exact div_le_div_of_nonneg_right hcos hden.le
      have hlt :
          1 / ((k : ℝ) * ((k : ℝ) + 1)) < 1 / (k : ℝ) ^ 2 := by
        rw [div_lt_div_iff₀ hden (sq_pos_of_pos hkpos)]
        nlinarith
      exact lt_of_le_of_lt hle hlt
  exact lt_of_le_of_lt htriangle hstrict

/-- Source: `proof_gap/exercise_84/3.txt`. -/
theorem gap3 :
    ∀ m n : ℕ, n < m → |x m - x n| < squareTail n m := by
  intro m n hnm
  rw [gap1 m n hnm]
  exact gap2 m n hnm

/-- Source: `proof_gap/exercise_84/4.txt`; n>0 avoids the k=1 denominator. -/
theorem gap4 :
    ∀ m n : ℕ, 0 < n → n < m →
      squareTail n m < telescopingTail n m := by
  intro m n hn hnm
  unfold squareTail telescopingTail
  apply Finset.sum_lt_sum_of_nonempty
  · exact ⟨n + 1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩
  · intro k hk
    have hkNat : 2 ≤ k := by
      have := (Finset.mem_Icc.mp hk).1
      omega
    have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hkNat
    have hkpos : 0 < (k : ℝ) := by linarith
    have hkmpos : 0 < (k : ℝ) - 1 := by linarith
    field_simp
    nlinarith

/-- Source: `proof_gap/exercise_84/5.txt`; n>0 avoids division by zero. -/
theorem gap5 :
    ∀ m n : ℕ, 0 < n → n < m →
      telescopingTail n m = 1 / (n : ℝ) - 1 / (m : ℝ) := by
  intro m n hn hnm
  induction m with
  | zero => omega
  | succ m ih =>
      by_cases hbase : m = n
      · subst m
        unfold telescopingTail
        simp
      · have hnm' : n < m := by omega
        have hi := ih hnm'
        unfold telescopingTail at hi ⊢
        rw [Finset.sum_Icc_succ_top (by omega)]
        rw [hi]
        rw [Nat.cast_add]
        norm_num

/-- Source: `proof_gap/exercise_84/6.txt`; n>0 is restored. -/
theorem gap6 :
    ∀ m n : ℕ, 0 < n → n < m →
      1 / (n : ℝ) - 1 / (m : ℝ) < 1 / (n : ℝ) := by
  intro m n hn hnm
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast (lt_trans hn hnm)
  linarith [one_div_pos.mpr hmpos]

/-- Source: `proof_gap/exercise_84/7.txt`; n>0 is restored. -/
theorem gap7 :
    ∀ m n : ℕ, 0 < n → n < m →
      squareTail n m < 1 / (n : ℝ) := by
  intro m n hn hnm
  exact (gap4 m n hn hnm).trans <|
    (gap5 m n hn hnm).trans_lt (gap6 m n hn hnm)

/-- Source: `proof_gap/exercise_84/8.txt`; N depends on ε. -/
theorem gap8 :
    ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ m n : ℕ, N < n → n < m → |x m - x n| < ε := by
  intro ε hε
  have hinv :
      Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0) := by
    simpa [one_div] using
      (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hev : ∀ᶠ n : ℕ in atTop, 1 / (n : ℝ) < ε :=
    hinv.eventually (Iio_mem_nhds hε)
  rcases eventually_atTop.1 hev with ⟨N, hN⟩
  refine ⟨N + 1, ?_⟩
  intro m n hn hnm
  exact lt_trans (gap3 m n hnm)
    (lt_trans (gap7 m n (by omega) hnm) (hN n (by omega)))

/-- Source: `proof_gap/exercise_84/9.txt`. -/
theorem gap9 (h : IsCauchy x) : IsCauchy x := by
  exact h

/-- Source: `proof_gap/exercise_84/10.txt`. -/
theorem gap10 (h : IsCauchy x) : Convergent x := by
  have hcauchy : CauchySeq x := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    rcases h ε hε with ⟨N, hN⟩
    refine ⟨N + 1, ?_⟩
    intro m hm n hn
    by_cases hmn : m = n
    · subst m
      simpa using hε
    · rcases lt_or_gt_of_ne hmn with hlt | hgt
      · have htail := hN n m (by omega) hlt
        simpa [Real.dist_eq, abs_sub_comm] using htail
      · have htail := hN m n (by omega) hgt
        simpa [Real.dist_eq] using htail
  exact cauchySeq_tendsto_of_complete hcauchy

/-- Source: `proof_gap/exercise_84/11.txt`. -/
theorem gap11 (h : Convergent x) : Convergent x := by
  exact h

end

end ProofGap.Exercise84
