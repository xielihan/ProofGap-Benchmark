import ProofGapLean.Prelude.Full

open scoped Topology

/-!
# Exercise 42

Semantic formalization of Exercise 42, gaps 1,...,40.
The four sequences and their four cutoff functions are kept distinct.
-/

namespace ProofGap.Exercise42

noncomputable section

def seq1 (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ (n + 1) / (n : ℝ)

def seq2 (n : ℕ) : ℝ :=
  (2 * (n : ℝ)) / ((n : ℝ) ^ 3 + 1)

def seq3 (n : ℕ) : ℝ :=
  1 / (Nat.factorial n : ℝ)

def seq4 (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n * (0.999 : ℝ) ^ n

def N1 (ε : ℝ) : ℕ :=
  Nat.floor (1 / ε)

def N2 (ε : ℝ) : ℕ :=
  Nat.floor (Real.sqrt (2 / ε))

def N3 (ε : ℝ) : ℕ :=
  Nat.floor (Real.log (1 / ε) / Real.log 2) + 1

def N4 (ε : ℝ) : ℕ :=
  Nat.floor (2500 * (Real.log (1 / ε) / Real.log 10))

def HasCutoff (u : ℕ → ℝ) : Prop :=
  ∃ N : ℝ → ℕ, ∀ (n : ℕ) (ε : ℝ),
    0 < ε → N ε < n → |u n| < ε

def ConvergesToZero (u : ℕ → ℝ) : Prop :=
  Tendsto u atTop (𝓝 0)

def S1Abs : Prop :=
  ∀ n : ℕ, |seq1 n| = 1 / (n : ℝ)

def S1Transfer : Prop :=
  ∀ (n : ℕ) (ε : ℝ), 0 < ε →
    1 / (n : ℝ) < ε → |seq1 n| < ε

def S1Index : Prop :=
  ∀ (n : ℕ) (ε : ℝ), 0 < ε →
    (n : ℝ) > 1 / ε → 1 / (n : ℝ) < ε

def S1FromIndex : Prop :=
  ∀ (n : ℕ) (ε : ℝ), 0 < ε →
    (n : ℝ) > 1 / ε → |seq1 n| < ε

def S2Abs : Prop :=
  ∀ n : ℕ, |seq2 n| = (2 * (n : ℝ)) / ((n : ℝ) ^ 3 + 1)

def S2Bound : Prop :=
  ∀ n : ℕ, 0 < n →
    (2 * (n : ℝ)) / ((n : ℝ) ^ 3 + 1) <
      2 / (n : ℝ) ^ 2

def S2AbsBound : Prop :=
  ∀ n : ℕ, 0 < n → |seq2 n| < 2 / (n : ℝ) ^ 2

def S2Transfer : Prop :=
  ∀ (n : ℕ) (ε : ℝ), 0 < ε →
    2 / (n : ℝ) ^ 2 < ε → |seq2 n| < ε

def S2Index : Prop :=
  ∀ (n : ℕ) (ε : ℝ), 0 < ε →
    (n : ℝ) > Real.sqrt (2 / ε) →
    2 / (n : ℝ) ^ 2 < ε

def S2FromIndex : Prop :=
  ∀ (n : ℕ) (ε : ℝ), 0 < ε →
    (n : ℝ) > Real.sqrt (2 / ε) → |seq2 n| < ε

def S3Abs : Prop :=
  ∀ n : ℕ, |seq3 n| = 1 / (Nat.factorial n : ℝ)

def S3Bound : Prop :=
  ∀ n : ℕ,
    1 / (Nat.factorial n : ℝ) ≤ 1 / ((2 : ℝ) ^ (n - 1))

def S3AbsBound : Prop :=
  ∀ n : ℕ, |seq3 n| ≤ 1 / ((2 : ℝ) ^ (n - 1))

def S3Transfer : Prop :=
  ∀ (n : ℕ) (ε : ℝ), 0 < ε →
    1 / ((2 : ℝ) ^ (n - 1)) < ε → |seq3 n| < ε

def S3Index : Prop :=
  ∀ (n : ℕ) (ε : ℝ), 0 < ε →
    (n : ℝ) > 1 + Real.log (1 / ε) / Real.log 2 →
    1 / ((2 : ℝ) ^ (n - 1)) < ε

def S3FromIndex : Prop :=
  ∀ (n : ℕ) (ε : ℝ), 0 < ε →
    (n : ℝ) > 1 + Real.log (1 / ε) / Real.log 2 →
    |seq3 n| < ε

def S4Abs : Prop :=
  ∀ n : ℕ, |seq4 n| = (0.999 : ℝ) ^ n

def S4LogTransfer : Prop :=
  ∀ (n : ℕ) (ε : ℝ), 0 < ε →
    (n : ℝ) * Real.log 0.999 < Real.log ε →
    |seq4 n| < ε

def S4IndexLog : Prop :=
  ∀ (n : ℕ) (ε : ℝ), 0 < ε →
    (n : ℝ) > Real.log ε / Real.log 0.999 →
    (n : ℝ) * Real.log 0.999 < Real.log ε

def S4FromIndex : Prop :=
  ∀ (n : ℕ) (ε : ℝ), 0 < ε →
    (n : ℝ) > Real.log ε / Real.log 0.999 →
    |seq4 n| < ε

private theorem convergesToZero_of_hasCutoff {u : ℕ → ℝ}
    (h : HasCutoff u) : ConvergesToZero u := by
  unfold HasCutoff at h
  unfold ConvergesToZero
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := h
  refine ⟨N ε + 1, ?_⟩
  intro n hn
  simpa [Real.dist_eq] using
    hN n ε hε (lt_of_lt_of_le (Nat.lt_succ_self (N ε)) hn)

/-- Exercise 42, gap 1. -/
theorem gap1 : S1Abs := by
  intro n
  simp [seq1, abs_div, abs_pow]

/-- Exercise 42, gap 2. -/
theorem gap2 (h1 : S1Abs) : S1Transfer := by
  intro n ε hε hn
  rw [h1 n]
  exact hn

/-- Exercise 42, gap 3. -/
theorem gap3 (h2 : S1Transfer) : S1Index := by
  intro n ε hε hn
  have hnpos : 0 < (n : ℝ) :=
    (one_div_pos.mpr hε).trans hn
  apply (div_lt_iff₀ hnpos).2
  have hprod : 1 < (n : ℝ) * ε := (div_lt_iff₀ hε).mp hn
  simpa [mul_comm] using hprod

/-- Exercise 42, gap 4. -/
theorem gap4 (h2 : S1Transfer) (h3 : S1Index) : S1FromIndex := by
  intro n ε hε hn
  exact h2 n ε hε (h3 n ε hε hn)

/-- Exercise 42, gap 5. -/
theorem gap5 (h4 : S1FromIndex) : HasCutoff seq1 := by
  refine ⟨N1, ?_⟩
  intro n ε hε hn
  apply h4 n ε hε
  unfold N1 at hn
  have hsuc : Nat.floor (1 / ε) + 1 ≤ n := Nat.succ_le_iff.mpr hn
  have hcast :
      ((Nat.floor (1 / ε) : ℕ) : ℝ) + 1 ≤ (n : ℝ) := by
    exact_mod_cast hsuc
  exact (Nat.lt_floor_add_one (1 / ε)).trans_le hcast

/-- Exercise 42, gap 6. -/
theorem gap6 (h5 : HasCutoff seq1) : ConvergesToZero seq1 := by
  exact convergesToZero_of_hasCutoff h5

/-- Exercise 42, gap 7. -/
theorem gap7 : S2Abs := by
  intro n
  rw [abs_of_nonneg]
  · rfl
  · unfold seq2
    positivity

/-- Exercise 42, gap 8; restricted to positive indices. -/
theorem gap8 (h7 : S2Abs) : S2Bound := by
  intro n hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- Exercise 42, gap 9; restricted to positive indices. -/
theorem gap9 (h7 : S2Abs) (h8 : S2Bound) : S2AbsBound := by
  intro n hn
  rw [h7 n]
  exact h8 n hn

/-- Exercise 42, gap 10. -/
theorem gap10 (h9 : S2AbsBound) : S2Transfer := by
  intro n ε hε hn
  by_cases hzero : n = 0
  · subst n
    simp [seq2]
    exact hε
  · exact (h9 n (Nat.pos_of_ne_zero hzero)).trans hn

/-- Exercise 42, gap 11. -/
theorem gap11 (h10 : S2Transfer) : S2Index := by
  intro n ε hε hn
  have hq : 0 < 2 / ε := div_pos (by norm_num) hε
  have hsqrt : 0 ≤ Real.sqrt (2 / ε) := Real.sqrt_nonneg _
  have hnpos : 0 < (n : ℝ) := hsqrt.trans_lt hn
  have hsquare : (Real.sqrt (2 / ε)) ^ 2 = 2 / ε :=
    Real.sq_sqrt hq.le
  have hpow : 2 / ε < (n : ℝ) ^ 2 := by nlinarith
  apply (div_lt_iff₀ (sq_pos_of_pos hnpos)).2
  have hprod : 2 < (n : ℝ) ^ 2 * ε := (div_lt_iff₀ hε).mp hpow
  simpa [mul_comm] using hprod

/-- Exercise 42, gap 12. -/
theorem gap12 (h10 : S2Transfer) (h11 : S2Index) : S2FromIndex := by
  intro n ε hε hn
  exact h10 n ε hε (h11 n ε hε hn)

/-- Exercise 42, gap 13. -/
theorem gap13 (h12 : S2FromIndex) : HasCutoff seq2 := by
  refine ⟨N2, ?_⟩
  intro n ε hε hn
  apply h12 n ε hε
  unfold N2 at hn
  have hsuc :
      Nat.floor (Real.sqrt (2 / ε)) + 1 ≤ n :=
    Nat.succ_le_iff.mpr hn
  have hcast :
      ((Nat.floor (Real.sqrt (2 / ε)) : ℕ) : ℝ) + 1 ≤ (n : ℝ) := by
    exact_mod_cast hsuc
  exact (Nat.lt_floor_add_one (Real.sqrt (2 / ε))).trans_le hcast

/-- Exercise 42, gap 14. -/
theorem gap14 (h13 : HasCutoff seq2) : ConvergesToZero seq2 := by
  exact convergesToZero_of_hasCutoff h13

/-- Exercise 42, gap 15. -/
theorem gap15 : S3Abs := by
  intro n
  rw [abs_of_nonneg]
  · rfl
  · unfold seq3
    positivity

/-- Exercise 42, gap 16. -/
theorem gap16 (h15 : S3Abs) : S3Bound := by
  intro n
  cases n with
  | zero => norm_num
  | succ k =>
      simp only [Nat.succ_sub_one]
      apply one_div_le_one_div_of_le (by positivity)
      have hnat : 2 ^ k ≤ Nat.factorial (k + 1) := by
        simpa [Nat.add_comm] using (@Nat.factorial_mul_pow_le_factorial 1 k)
      exact_mod_cast hnat

/-- Exercise 42, gap 17. -/
theorem gap17 (h15 : S3Abs) (h16 : S3Bound) : S3AbsBound := by
  intro n
  rw [h15 n]
  exact h16 n

/-- Exercise 42, gap 18. -/
theorem gap18 (h17 : S3AbsBound) : S3Transfer := by
  intro n ε hε hn
  exact (h17 n).trans_lt hn

/-- Exercise 42, gap 19. -/
theorem gap19 (h18 : S3Transfer) : S3Index := by
  intro n ε hε hn
  change (n : ℝ) > 1 + Real.logb 2 (1 / ε) at hn
  cases n with
  | zero =>
      have hlog : Real.logb 2 (1 / ε) < (-1 : ℝ) := by
        norm_num at hn ⊢
        linarith
      have hpow : 1 / ε < (2 : ℝ) ^ (-1 : ℝ) :=
        (Real.logb_lt_iff_lt_rpow (by norm_num) (one_div_pos.mpr hε)).mp hlog
      rw [Real.rpow_neg_one] at hpow
      norm_num at hpow
      have hrecip : 1 / ε < 1 :=
        by simpa [one_div] using
          hpow.trans (by norm_num : (1 / 2 : ℝ) < 1)
      have : 1 < ε := by
        simpa using (div_lt_iff₀ hε).mp hrecip
      simpa using this
  | succ k =>
      have hlog : Real.logb 2 (1 / ε) < (k : ℝ) := by
        norm_num at hn ⊢
        linarith
      have hpow : 1 / ε < (2 : ℝ) ^ k := by
        have hrpow : 1 / ε < (2 : ℝ) ^ (k : ℝ) :=
          (Real.logb_lt_iff_lt_rpow (by norm_num) (one_div_pos.mpr hε)).mp hlog
        simpa [Real.rpow_natCast] using hrpow
      apply (div_lt_iff₀ (by positivity : 0 < (2 : ℝ) ^ k)).2
      have hprod : 1 < (2 : ℝ) ^ k * ε :=
        (div_lt_iff₀ hε).mp hpow
      simpa [mul_comm] using hprod

/-- Exercise 42, gap 20. -/
theorem gap20 (h18 : S3Transfer) (h19 : S3Index) : S3FromIndex := by
  intro n ε hε hn
  exact h18 n ε hε (h19 n ε hε hn)

/-- Exercise 42, gap 21. -/
theorem gap21 (h20 : S3FromIndex) : HasCutoff seq3 := by
  refine ⟨N3, ?_⟩
  intro n ε hε hn
  apply h20 n ε hε
  unfold N3 at hn
  have hsuc :
      (Nat.floor (Real.log (1 / ε) / Real.log 2) + 1) + 1 ≤ n :=
    Nat.succ_le_iff.mpr hn
  have hcast :
      ((Nat.floor (Real.log (1 / ε) / Real.log 2) : ℕ) : ℝ) + 2 ≤
        (n : ℝ) := by
    exact_mod_cast hsuc
  have hfloor :
      Real.log (1 / ε) / Real.log 2 <
        ((Nat.floor (Real.log (1 / ε) / Real.log 2) : ℕ) : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  linarith

/-- Exercise 42, gap 22. -/
theorem gap22 (h21 : HasCutoff seq3) : ConvergesToZero seq3 := by
  exact convergesToZero_of_hasCutoff h21

/-- Exercise 42, gap 23. -/
theorem gap23 : S4Abs := by
  intro n
  simp [seq4, abs_mul, abs_pow, abs_of_pos (by norm_num : (0 : ℝ) < 0.999)]

/-- Exercise 42, gap 24. -/
theorem gap24 (h23 : S4Abs) : S4LogTransfer := by
  intro n ε hε hn
  rw [h23 n]
  apply (Real.log_lt_log_iff (by positivity) hε).mp
  rw [Real.log_pow]
  exact hn

/-- Exercise 42, gap 25. -/
theorem gap25 (h24 : S4LogTransfer) : S4IndexLog := by
  intro n ε hε hn
  have hlog : Real.log (0.999 : ℝ) < 0 :=
    Real.log_neg (by norm_num) (by norm_num)
  exact (div_lt_iff_of_neg hlog).mp hn

/-- Exercise 42, gap 26. -/
theorem gap26 (h24 : S4LogTransfer) (h25 : S4IndexLog) : S4FromIndex := by
  intro n ε hε hn
  exact h24 n ε hε (h25 n ε hε hn)

/-- Exercise 42, gap 27. -/
theorem gap27 (h26 : S4FromIndex) : HasCutoff seq4 := by
  refine ⟨fun ε => Nat.floor (Real.log ε / Real.log 0.999), ?_⟩
  intro n ε hε hn
  apply h26 n ε hε
  have hsuc :
      Nat.floor (Real.log ε / Real.log 0.999) + 1 ≤ n :=
    Nat.succ_le_iff.mpr hn
  have hcast :
      ((Nat.floor (Real.log ε / Real.log 0.999) : ℕ) : ℝ) + 1 ≤
        (n : ℝ) := by
    exact_mod_cast hsuc
  exact (Nat.lt_floor_add_one _).trans_le hcast

/-- Exercise 42, gap 28. -/
theorem gap28 (h27 : HasCutoff seq4) : ConvergesToZero seq4 := by
  exact convergesToZero_of_hasCutoff h27

/-- Exercise 42, gap 29; uses the cutoff for sequence (1). -/
theorem gap29 : N1 (0.1 : ℝ) = 10 := by
  norm_num [N1]

/-- Exercise 42, gap 30; uses the cutoff for sequence (1). -/
theorem gap30 : N1 (0.01 : ℝ) = 100 := by
  norm_num [N1]

/-- Exercise 42, gap 31; uses the cutoff for sequence (1). -/
theorem gap31 : N1 (0.001 : ℝ) = 1000 := by
  norm_num [N1]

/-- Exercise 42, gap 32; uses the cutoff for sequence (2). -/
theorem gap32 : N2 (0.1 : ℝ) = 4 := by
  norm_num [N2]
  change Nat.floor (Real.sqrt ((20 : ℕ) : ℝ)) = 4
  rw [Real.nat_floor_real_sqrt_eq_nat_sqrt]
  native_decide

/-- Exercise 42, gap 33; uses the cutoff for sequence (2). -/
theorem gap33 : N2 (0.01 : ℝ) = 14 := by
  norm_num [N2]
  change Nat.floor (Real.sqrt ((200 : ℕ) : ℝ)) = 14
  rw [Real.nat_floor_real_sqrt_eq_nat_sqrt]
  native_decide

/-- Exercise 42, gap 34; uses the cutoff for sequence (2). -/
theorem gap34 : N2 (0.001 : ℝ) = 44 := by
  norm_num [N2]
  change Nat.floor (Real.sqrt ((2000 : ℕ) : ℝ)) = 44
  rw [Real.nat_floor_real_sqrt_eq_nat_sqrt]
  native_decide

/-- Exercise 42, gap 35; uses the cutoff for sequence (3). -/
theorem gap35 : N3 (0.1 : ℝ) = 4 := by
  norm_num [N3]
  change Nat.floor (Real.logb ((2 : ℕ) : ℝ) ((10 : ℕ) : ℝ)) + 1 = 4
  rw [Real.natFloor_logb_natCast]
  native_decide

/-- Exercise 42, gap 36; uses the cutoff for sequence (3). -/
theorem gap36 : N3 (0.01 : ℝ) = 7 := by
  norm_num [N3]
  change Nat.floor (Real.logb ((2 : ℕ) : ℝ) ((100 : ℕ) : ℝ)) + 1 = 7
  rw [Real.natFloor_logb_natCast]
  native_decide

/-- Exercise 42, gap 37; uses the cutoff for sequence (3). -/
theorem gap37 : N3 (0.001 : ℝ) = 10 := by
  norm_num [N3]
  change Nat.floor (Real.logb ((2 : ℕ) : ℝ) ((1000 : ℕ) : ℝ)) + 1 = 10
  rw [Real.natFloor_logb_natCast]
  native_decide

/-- Exercise 42, gap 38; uses the cutoff for sequence (4). -/
theorem gap38 : N4 (0.1 : ℝ) = 2500 := by
  norm_num [N4]

/-- Exercise 42, gap 39; uses the cutoff for sequence (4). -/
theorem gap39 : N4 (0.01 : ℝ) = 5000 := by
  norm_num [N4]
  have hlog : Real.log (100 : ℝ) = 2 * Real.log 10 := by
    rw [show (100 : ℝ) = 10 ^ 2 by norm_num, Real.log_pow]
    norm_num
  rw [hlog]
  have hne : Real.log (10 : ℝ) ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one (by norm_num) (by norm_num)
  field_simp [hne]
  norm_num

/-- Exercise 42, gap 40; uses the cutoff for sequence (4). -/
theorem gap40 : N4 (0.001 : ℝ) = 7500 := by
  norm_num [N4]
  have hlog : Real.log (1000 : ℝ) = 3 * Real.log 10 := by
    rw [show (1000 : ℝ) = 10 ^ 3 by norm_num, Real.log_pow]
    norm_num
  rw [hlog]
  have hne : Real.log (10 : ℝ) ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one (by norm_num) (by norm_num)
  field_simp [hne]
  norm_num

end

end ProofGap.Exercise42
