import ProofGapLean.Prelude.Discrete

/-!
# Exercise 8

Semantic formalization of Exercise 8, gaps 1,...,13.
Factorials are cast to `ℝ`, because the comparison is against powers of a
rational/real average.
-/

namespace ProofGap.Exercise8

noncomputable section

def factorialReal (n : ℕ) : ℝ :=
  (n.factorial : ℝ)

def averagePower (n : ℕ) : ℝ :=
  (((n : ℝ) + 1) / 2) ^ n

def FactorialBound (n : ℕ) : Prop :=
  factorialReal n < averagePower n

def BaseAverageValue : Prop :=
  ∀ n : ℕ, n = 2 → (((2 : ℝ) + 1) / 2) ^ 2 = 9 / 4

def BaseStrictInequality : Prop :=
  ∀ n : ℕ, n = 2 → (9 / 4 : ℝ) > 2

def TwoFactorial : Prop :=
  ∀ n : ℕ, n = 2 → (2 : ℝ) = factorialReal 2

def BaseFactorialBound : Prop :=
  ∀ n : ℕ, n = 2 → (((2 : ℝ) + 1) / 2) ^ 2 > factorialReal 2

def MultiplyInductionBound : Prop :=
  ∀ k : ℕ, 0 < k → FactorialBound k →
    factorialReal (k + 1) <
      (((k : ℝ) + 1) / 2) ^ k * ((k : ℝ) + 1)

def RearrangeIntermediateBound : Prop :=
  ∀ k : ℕ, 0 < k → FactorialBound k →
    (((k : ℝ) + 1) / 2) ^ k * ((k : ℝ) + 1) =
      2 * (((k : ℝ) + 1) / 2) ^ (k + 1)

def IntermediateFactorialBound : Prop :=
  ∀ k : ℕ, 0 < k → FactorialBound k →
    factorialReal (k + 1) <
      2 * (((k : ℝ) + 1) / 2) ^ (k + 1)

def RatioRewrite : Prop :=
  ∀ k : ℕ, 0 < k → FactorialBound k →
    (((k : ℝ) + 2) / ((k : ℝ) + 1)) ^ (k + 1) =
      (1 + 1 / ((k : ℝ) + 1)) ^ (k + 1)

def RatioGreaterThanTwo : Prop :=
  ∀ k : ℕ, 0 < k → FactorialBound k →
    (1 + 1 / ((k : ℝ) + 1)) ^ (k + 1) > 2

def RewrittenRatioGreaterThanTwo : Prop :=
  ∀ k : ℕ, 0 < k → FactorialBound k →
    (((k : ℝ) + 2) / ((k : ℝ) + 1)) ^ (k + 1) > 2

def InductionStep : Prop :=
  ∀ k : ℕ, 0 < k → FactorialBound k → FactorialBound (k + 1)

def FinalBound : Prop :=
  ∀ n : ℕ, 0 < n → 1 < n → FactorialBound n

/-- Exercise 8, gap 1. -/
theorem gap1 : BaseAverageValue := by
  intro n hn
  norm_num

/-- Exercise 8, gap 2. -/
theorem gap2
    (h1 : BaseAverageValue) :
    BaseStrictInequality := by
  intro n hn
  norm_num

/-- Exercise 8, gap 3. -/
theorem gap3
    (h1 : BaseAverageValue)
    (h2 : BaseStrictInequality) :
    TwoFactorial := by
  intro n hn
  norm_num [factorialReal]

/-- Exercise 8, gap 4. -/
theorem gap4
    (h1 : BaseAverageValue)
    (h2 : BaseStrictInequality)
    (h3 : TwoFactorial) :
    BaseFactorialBound := by
  intro n hn
  norm_num [factorialReal]

/-- Exercise 8, gap 5. -/
theorem gap5
    (h1 : BaseAverageValue)
    (h2 : BaseStrictInequality)
    (h3 : TwoFactorial)
    (h4 : BaseFactorialBound) :
    MultiplyInductionBound := by
  intro k hk hbound
  unfold FactorialBound averagePower factorialReal at *
  calc
    (((k + 1).factorial : ℕ) : ℝ) =
        ((k : ℝ) + 1) * (k.factorial : ℝ) := by
      rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    _ < ((k : ℝ) + 1) * (((k : ℝ) + 1) / 2) ^ k :=
      mul_lt_mul_of_pos_left hbound (by positivity)
    _ = (((k : ℝ) + 1) / 2) ^ k * ((k : ℝ) + 1) := by ring

/-- Exercise 8, gap 6. -/
theorem gap6
    (h1 : BaseAverageValue)
    (h2 : BaseStrictInequality)
    (h3 : TwoFactorial)
    (h4 : BaseFactorialBound)
    (h5 : MultiplyInductionBound) :
    RearrangeIntermediateBound := by
  intro k hk hbound
  rw [pow_succ]
  ring

/-- Exercise 8, gap 7. -/
theorem gap7
    (h1 : BaseAverageValue)
    (h2 : BaseStrictInequality)
    (h3 : TwoFactorial)
    (h4 : BaseFactorialBound)
    (h5 : MultiplyInductionBound)
    (h6 : RearrangeIntermediateBound) :
    IntermediateFactorialBound := by
  intro k hk hbound
  exact (h5 k hk hbound).trans_eq (h6 k hk hbound)

/-- Exercise 8, gap 8. -/
theorem gap8
    (h1 : BaseAverageValue)
    (h2 : BaseStrictInequality)
    (h3 : TwoFactorial)
    (h4 : BaseFactorialBound)
    (h5 : MultiplyInductionBound)
    (h6 : RearrangeIntermediateBound)
    (h7 : IntermediateFactorialBound) :
    RatioRewrite := by
  intro k hk hbound
  congr 1
  field_simp
  ring

/-- Exercise 8, gap 9. -/
theorem gap9
    (h1 : BaseAverageValue)
    (h2 : BaseStrictInequality)
    (h3 : TwoFactorial)
    (h4 : BaseFactorialBound)
    (h5 : MultiplyInductionBound)
    (h6 : RearrangeIntermediateBound)
    (h7 : IntermediateFactorialBound)
    (h8 : RatioRewrite) :
    RatioGreaterThanTwo := by
  intro k hk hbound
  let x : ℝ := 1 / ((k : ℝ) + 1)
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have hx : 0 < x := by
    dsimp [x]
    positivity
  have hxinv : ((k : ℝ) + 1) * x = 1 := by
    dsimp [x]
    field_simp
  have hbern : 1 + (k : ℝ) * x ≤ (1 + x) ^ k := by
    exact one_add_mul_le_pow (by linarith [hx]) k
  have hkx2 : 0 < (k : ℝ) * x ^ 2 := mul_pos hkR (sq_pos_of_pos hx)
  have hstrict : 2 < (1 + (k : ℝ) * x) * (1 + x) := by
    nlinarith [hxinv, hkx2]
  change 2 < (1 + x) ^ (k + 1)
  rw [pow_succ]
  exact hstrict.trans_le
    (mul_le_mul_of_nonneg_right hbern (by positivity))

/-- Exercise 8, gap 10. -/
theorem gap10
    (h1 : BaseAverageValue)
    (h2 : BaseStrictInequality)
    (h3 : TwoFactorial)
    (h4 : BaseFactorialBound)
    (h5 : MultiplyInductionBound)
    (h6 : RearrangeIntermediateBound)
    (h7 : IntermediateFactorialBound)
    (h8 : RatioRewrite)
    (h9 : RatioGreaterThanTwo) :
    RewrittenRatioGreaterThanTwo := by
  intro k hk hbound
  rw [h8 k hk hbound]
  exact h9 k hk hbound

/-- Exercise 8, gap 11. -/
theorem gap11
    (h1 : BaseAverageValue)
    (h2 : BaseStrictInequality)
    (h3 : TwoFactorial)
    (h4 : BaseFactorialBound)
    (h5 : MultiplyInductionBound)
    (h6 : RearrangeIntermediateBound)
    (h7 : IntermediateFactorialBound)
    (h8 : RatioRewrite)
    (h9 : RatioGreaterThanTwo)
    (h10 : RewrittenRatioGreaterThanTwo) :
    InductionStep := by
  intro k hk hbound
  have hmid := h7 k hk hbound
  have hratio := h10 k hk hbound
  have hpowpos : 0 < (((k : ℝ) + 1) / 2) ^ (k + 1) := by
    positivity
  unfold FactorialBound averagePower
  calc
    factorialReal (k + 1) <
        2 * (((k : ℝ) + 1) / 2) ^ (k + 1) := hmid
    _ < (((k : ℝ) + 2) / ((k : ℝ) + 1)) ^ (k + 1) *
        (((k : ℝ) + 1) / 2) ^ (k + 1) :=
      mul_lt_mul_of_pos_right hratio hpowpos
    _ = ((((k + 1 : ℕ) : ℝ) + 1) / 2) ^ (k + 1) := by
      rw [← mul_pow]
      congr 1
      field_simp
      norm_num
      ring

/-- Exercise 8, gap 12. -/
theorem gap12
    (h1 : BaseAverageValue)
    (h2 : BaseStrictInequality)
    (h3 : TwoFactorial)
    (h4 : BaseFactorialBound)
    (h5 : MultiplyInductionBound)
    (h6 : RearrangeIntermediateBound)
    (h7 : IntermediateFactorialBound)
    (h8 : RatioRewrite)
    (h9 : RatioGreaterThanTwo)
    (h10 : RewrittenRatioGreaterThanTwo)
    (h11 : InductionStep) :
    FinalBound := by
  intro n
  induction n with
  | zero =>
      intro hn hn1
      omega
  | succ k ih =>
      intro hn hn1
      by_cases hk : k = 1
      · subst k
        exact h4 2 rfl
      · exact h11 k (by omega) (ih (by omega) (by omega))

/--
Exercise 8, gap 13.

The goal duplicates gap 12 and is kept as a separate dataset item.
-/
theorem gap13
    (h1 : BaseAverageValue)
    (h2 : BaseStrictInequality)
    (h3 : TwoFactorial)
    (h4 : BaseFactorialBound)
    (h5 : MultiplyInductionBound)
    (h6 : RearrangeIntermediateBound)
    (h7 : IntermediateFactorialBound)
    (h8 : RatioRewrite)
    (h9 : RatioGreaterThanTwo)
    (h10 : RewrittenRatioGreaterThanTwo)
    (h11 : InductionStep)
    (h12 : FinalBound) :
    FinalBound := by
  exact h12

end

end ProofGap.Exercise8
