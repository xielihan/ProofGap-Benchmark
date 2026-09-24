import ProofGapLean.Prelude.Full

namespace ProofGap.Exercise96

noncomputable section

def x (n : ℕ) : ℝ :=
  (n : ℝ) ^ 2 / (2 : ℝ) ^ n

def values : Set ℝ :=
  {v | ∃ n : ℕ, 0 < n ∧ v = x n}

/-- Exercise 96, gap 1. -/
theorem gap1 :
    ∀ n : ℕ, n = 3 → n ^ 2 > 2 ^ n := by
  intro n hn
  subst n
  norm_num

private theorem square_le_two_pow_of_four_le :
    ∀ n : ℕ, 4 ≤ n → n ^ 2 ≤ 2 ^ n := by
  intro n hn
  induction n with
  | zero => omega
  | succ n ih =>
      by_cases hbase : n = 3
      · subst n
        norm_num
      · have hn4 : 4 ≤ n := by omega
        have hprev := ih hn4
        have hstep : (n + 1) ^ 2 ≤ 2 * n ^ 2 := by
          nlinarith [sq_nonneg (n - 1)]
        have hpow : 2 ^ (n + 1) = 2 * 2 ^ n := by
          rw [pow_succ]
          ring
        rw [hpow]
        exact le_trans hstep (Nat.mul_le_mul_left 2 hprev)

/-- Exercise 96, gap 2. -/
theorem gap2 :
    ∀ n : ℕ, n ≠ 3 → n ^ 2 ≤ 2 ^ n := by
  intro n hn
  by_cases hsmall : n < 4
  · interval_cases n
    · norm_num
    · norm_num
    · norm_num
    · exact (hn rfl).elim
  · exact square_le_two_pow_of_four_le n (by omega)

/-- Exercise 96, gap 3. -/
theorem gap3 :
    IsGreatest values (x 3) := by
  constructor
  · exact ⟨3, by omega, rfl⟩
  · intro v hv
    rcases hv with ⟨n, hn, rfl⟩
    by_cases h3 : n = 3
    · subst n
      exact le_rfl
    · have hnat := gap2 n h3
      have hreal : (n : ℝ) ^ 2 ≤ (2 : ℝ) ^ n := by exact_mod_cast hnat
      have hxle : x n ≤ 1 := by
        unfold x
        exact (div_le_one (by positivity)).mpr hreal
      have hx3 : (1 : ℝ) < x 3 := by norm_num [x]
      exact le_trans hxle (le_of_lt hx3)

/-- Exercise 96, gap 4. -/
theorem gap4 :
    x 3 = 9 / 8 := by
  norm_num [x]

/-- Exercise 96, gap 5. -/
theorem gap5 :
    IsGreatest values (9 / 8) := by
  rw [← gap4]
  exact gap3

end

end ProofGap.Exercise96
