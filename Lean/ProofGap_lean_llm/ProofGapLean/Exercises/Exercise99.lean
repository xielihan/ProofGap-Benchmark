import ProofGapLean.Prelude.Full

namespace ProofGap.Exercise99

def x (n : ℕ) : ℝ :=
  (n : ℝ) ^ 2 - 9 * n - 100

def values : Set ℝ :=
  {v | ∃ n : ℕ, 0 < n ∧ v = x n}

/-- Exercise 99, gap 1; n=0 is a counterexample. -/
theorem gap1 :
    ∀ n : ℕ, 0 < n → 9 * n ≤ n ^ 2 → n ≥ 9 := by
  intro n hn hquad
  by_contra hnot
  have hnlt : n < 9 := by omega
  interval_cases n <;> norm_num at hquad

/-- Exercise 99, gap 2. -/
theorem gap2 :
    ∀ n : ℕ, n ^ 2 - 9 * n < 0 → 0 < n := by
  intro n h
  omega

/-- Exercise 99, gap 3. -/
theorem gap3 :
    ∀ n : ℕ, n ^ 2 - 9 * n < 0 → n < 9 := by
  intro n h
  omega

/-- Exercise 99, gap 4. -/
theorem gap4 :
    ∀ n : ℕ, n ^ 2 - 9 * n < 0 → 0 < 9 := by
  intro n h
  omega

/-- Exercise 99, gap 5. -/
theorem gap5 :
    IsLeast values (x 4) := by
  constructor
  · exact ⟨4, by omega, rfl⟩
  · intro v hv
    rcases hv with ⟨n, hn, rfl⟩
    unfold x
    by_cases h : n ≤ 4
    · have hnR : (0 : ℝ) ≤ n := by positivity
      have h4R : (n : ℝ) ≤ 4 := by exact_mod_cast h
      have hprod : 0 ≤ ((n : ℝ) - 4) * ((n : ℝ) - 5) :=
        mul_nonneg_of_nonpos_of_nonpos
          (sub_nonpos.mpr h4R) (by linarith)
      norm_num
      nlinarith [hprod]
    · have h5 : 5 ≤ n := by omega
      have h5R : (5 : ℝ) ≤ n := by exact_mod_cast h5
      have hprod : 0 ≤ ((n : ℝ) - 4) * ((n : ℝ) - 5) :=
        mul_nonneg (by linarith) (by linarith)
      norm_num
      nlinarith [hprod]

/-- Exercise 99, gap 6. -/
theorem gap6 :
    x 4 = x 5 := by
  norm_num [x]

/-- Exercise 99, gap 7. -/
theorem gap7 :
    x 5 = -120 := by
  norm_num [x]

/-- Exercise 99, gap 8. -/
theorem gap8 :
    IsLeast values (-120) := by
  rw [← gap7, ← gap6]
  exact gap5

end ProofGap.Exercise99
