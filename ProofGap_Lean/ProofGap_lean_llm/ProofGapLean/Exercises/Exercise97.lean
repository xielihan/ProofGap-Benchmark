import ProofGapLean.Prelude.Elementary

namespace ProofGap.Exercise97

noncomputable section

def x (n : ℕ) : ℝ :=
  Real.sqrt n / (100 + n)

def fourthRoot (n : ℕ) : ℝ :=
  Real.sqrt (Real.sqrt n)

def reciprocalSquareForm (n : ℕ) : ℝ :=
  1 / ((fourthRoot n - 10 / fourthRoot n) ^ 2 + 20)

def values : Set ℝ :=
  {v | ∃ n : ℕ, 0 < n ∧ v = x n}

/-- Exercise 97, gap 1; the rewrite requires positive n. -/
theorem gap1 :
    ∀ n : ℕ, 0 < n → x n = reciprocalSquareForm n := by
  intro n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.2 hnR
  have ht : 0 < Real.sqrt (Real.sqrt n) := Real.sqrt_pos.2 hs
  have hs_sq : (Real.sqrt n) ^ 2 = (n : ℝ) := Real.sq_sqrt hnR.le
  have ht_sq : (Real.sqrt (Real.sqrt n)) ^ 2 = Real.sqrt n :=
    Real.sq_sqrt hs.le
  unfold x reciprocalSquareForm fourthRoot
  field_simp [ne_of_gt ht, ne_of_gt hs]
  rw [ht_sq]
  nlinarith [hs_sq]

/-- Exercise 97, gap 2. -/
theorem gap2 :
    ∀ n : ℕ, reciprocalSquareForm n ≤ 1 / 20 := by
  intro n
  unfold reciprocalSquareForm
  exact one_div_le_one_div_of_le (by norm_num)
    (by nlinarith [sq_nonneg (fourthRoot n - 10 / fourthRoot n)])

/-- Exercise 97, gap 3; use the positive-index sequence. -/
theorem gap3 :
    ∀ n : ℕ, 0 < n → x n ≤ 1 / 20 := by
  intro n hn
  rw [gap1 n hn]
  exact gap2 n

/-- Exercise 97, gap 4. -/
theorem gap4 :
    x 100 = 1 / 20 := by
  unfold x
  norm_num only [Nat.cast_ofNat]
  have hsqrt : Real.sqrt (100 : ℝ) = 10 := by
    rw [show (100 : ℝ) = 10 ^ 2 by norm_num]
    rw [Real.sqrt_sq_eq_abs]
    norm_num
  rw [hsqrt]
  norm_num

/-- Exercise 97, gap 5. -/
theorem gap5 :
    IsGreatest values (x 100) := by
  constructor
  · exact ⟨100, by omega, rfl⟩
  · intro v hv
    rcases hv with ⟨n, hn, rfl⟩
    rw [gap4]
    exact gap3 n hn

/-- Exercise 97, gap 6. -/
theorem gap6 :
    x 100 = 1 / 20 := by
  exact gap4

/-- Exercise 97, gap 7. -/
theorem gap7 :
    IsGreatest values (1 / 20) := by
  rw [← gap4]
  exact gap5

end

end ProofGap.Exercise97
