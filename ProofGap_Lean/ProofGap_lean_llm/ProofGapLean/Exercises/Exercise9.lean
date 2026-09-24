import ProofGapLean.Prelude.Discrete

/-!
# Exercise 9

Semantic formalization of Exercise 9, gaps 1,...,11.
The products and factorials are natural-number expressions.
-/

namespace ProofGap.Exercise9

def evenFactorialProduct (n : ℕ) : ℕ :=
  ∏ i ∈ Finset.Icc 1 n, (2 * i).factorial

def factorialPower (n : ℕ) : ℕ :=
  ((n + 1).factorial) ^ n

def MainBound (n : ℕ) : Prop :=
  evenFactorialProduct n > factorialPower n

def tailProduct (k : ℕ) : ℕ :=
  ∏ j ∈ Finset.Icc (k + 2) (2 * k + 2), j

def BaseProductValue : Prop :=
  ∀ n : ℕ, n = 2 → Nat.factorial 2 * Nat.factorial 4 = 48

def BasePowerValue : Prop :=
  ∀ n : ℕ, n = 2 → ((2 + 1).factorial) ^ 2 = 36

def BaseStrictBound : Prop :=
  ∀ n : ℕ, n = 2 →
    Nat.factorial 2 * Nat.factorial 4 > ((2 + 1).factorial) ^ 2

def AppendEvenFactorial : Prop :=
  ∀ k : ℕ, 1 < k → MainBound k →
    evenFactorialProduct (k + 1) >
      ((k + 1).factorial) ^ k * (2 * k + 2).factorial

def SplitLargeFactorial : Prop :=
  ∀ k : ℕ, 1 < k → MainBound k →
    ((k + 1).factorial) ^ k * (2 * k + 2).factorial =
      ((k + 1).factorial) ^ (k + 1) * tailProduct k

def SubstituteFactorialSplit : Prop :=
  ∀ k : ℕ, 1 < k → MainBound k →
    evenFactorialProduct (k + 1) >
      ((k + 1).factorial) ^ (k + 1) * tailProduct k

def LowerBoundTailProduct : Prop :=
  ∀ k : ℕ, 1 < k → MainBound k →
    ((k + 1).factorial) ^ (k + 1) * tailProduct k >
      ((k + 1).factorial) ^ (k + 1) * (k + 2) ^ (k + 1)

def CombineFactorialAndPower : Prop :=
  ∀ k : ℕ, 1 < k → MainBound k →
    ((k + 1).factorial) ^ (k + 1) * (k + 2) ^ (k + 1) =
      ((k + 2).factorial) ^ (k + 1)

def InductionStep : Prop :=
  ∀ k : ℕ, 1 < k → MainBound k → MainBound (k + 1)

def CorrectedFinalBound : Prop :=
  ∀ n : ℕ, 1 < n → MainBound n

/-- Exercise 9, gap 1. -/
theorem gap1 : BaseProductValue := by
  intro n hn
  norm_num [Nat.factorial]

/-- Exercise 9, gap 2. -/
theorem gap2
    (h1 : BaseProductValue) :
    BasePowerValue := by
  intro n hn
  norm_num [Nat.factorial]

/-- Exercise 9, gap 3. -/
theorem gap3
    (h1 : BaseProductValue)
    (h2 : BasePowerValue) :
    BaseStrictBound := by
  intro n hn
  norm_num [Nat.factorial]

/-- Exercise 9, gap 4. -/
theorem gap4
    (h1 : BaseProductValue)
    (h2 : BasePowerValue)
    (h3 : BaseStrictBound) :
    AppendEvenFactorial := by
  intro k hk hbound
  have hfacpos : 0 < (2 * k + 2).factorial := Nat.factorial_pos _
  have hmul :
      evenFactorialProduct k * (2 * k + 2).factorial >
        ((k + 1).factorial) ^ k * (2 * k + 2).factorial :=
    (Nat.mul_lt_mul_right hfacpos).2 hbound
  unfold evenFactorialProduct
  rw [Finset.prod_Icc_succ_top (by omega)]
  simpa [Nat.mul_add, Nat.add_assoc] using hmul

/-- Exercise 9, gap 5. -/
theorem gap5
    (h1 : BaseProductValue)
    (h2 : BasePowerValue)
    (h3 : BaseStrictBound)
    (h4 : AppendEvenFactorial) :
    SplitLargeFactorial := by
  intro k hk hbound
  have hsplit :
      (2 * k + 2).factorial = (k + 1).factorial * tailProduct k := by
    calc
      (2 * k + 2).factorial =
          ∏ j ∈ Finset.Ico 1 ((2 * k + 2) + 1), j :=
        (Finset.prod_Ico_id_eq_factorial (2 * k + 2)).symm
      _ = (∏ j ∈ Finset.Ico 1 ((k + 1) + 1), j) *
          ∏ j ∈ Finset.Ico ((k + 1) + 1) ((2 * k + 2) + 1), j := by
        symm
        exact Finset.prod_Ico_consecutive (fun j : ℕ => j) (by omega) (by omega)
      _ = (k + 1).factorial * tailProduct k := by
        rw [Finset.prod_Ico_id_eq_factorial]
        unfold tailProduct
        rw [Finset.Ico_add_one_right_eq_Icc]
  rw [hsplit, pow_succ]
  ac_rfl

/-- Exercise 9, gap 6. -/
theorem gap6
    (h1 : BaseProductValue)
    (h2 : BasePowerValue)
    (h3 : BaseStrictBound)
    (h4 : AppendEvenFactorial)
    (h5 : SplitLargeFactorial) :
    SubstituteFactorialSplit := by
  intro k hk hbound
  rw [← h5 k hk hbound]
  exact h4 k hk hbound

/-- Exercise 9, gap 7. -/
theorem gap7
    (h1 : BaseProductValue)
    (h2 : BasePowerValue)
    (h3 : BaseStrictBound)
    (h4 : AppendEvenFactorial)
    (h5 : SplitLargeFactorial)
    (h6 : SubstituteFactorialSplit) :
    LowerBoundTailProduct := by
  intro k hk hbound
  have htail : (k + 2) ^ (k + 1) < tailProduct k := by
    unfold tailProduct
    calc
      (k + 2) ^ (k + 1) =
          ∏ j ∈ Finset.Icc (k + 2) (2 * k + 2), (k + 2) := by
        rw [Finset.prod_const]
        congr 1
        simp
        omega
      _ < ∏ j ∈ Finset.Icc (k + 2) (2 * k + 2), j := by
        apply Finset.prod_lt_prod
        · intro j hj
          omega
        · intro j hj
          exact (Finset.mem_Icc.mp hj).1
        · refine ⟨k + 3, ?_, by omega⟩
          simp only [Finset.mem_Icc]
          omega
  exact (Nat.mul_lt_mul_left (pow_pos (Nat.factorial_pos _) _)).2 htail

/-- Exercise 9, gap 8. -/
theorem gap8
    (h1 : BaseProductValue)
    (h2 : BasePowerValue)
    (h3 : BaseStrictBound)
    (h4 : AppendEvenFactorial)
    (h5 : SplitLargeFactorial)
    (h6 : SubstituteFactorialSplit)
    (h7 : LowerBoundTailProduct) :
    CombineFactorialAndPower := by
  intro k hk hbound
  rw [← mul_pow]
  simp only [Nat.factorial_succ]
  ring

/-- Exercise 9, gap 9. -/
theorem gap9
    (h1 : BaseProductValue)
    (h2 : BasePowerValue)
    (h3 : BaseStrictBound)
    (h4 : AppendEvenFactorial)
    (h5 : SplitLargeFactorial)
    (h6 : SubstituteFactorialSplit)
    (h7 : LowerBoundTailProduct)
    (h8 : CombineFactorialAndPower) :
    InductionStep := by
  intro k hk hbound
  unfold MainBound factorialPower
  rw [← h8 k hk hbound]
  exact (h7 k hk hbound).trans (h6 k hk hbound)

/--
Exercise 9, gap 10.

The source quantifies over every `n`, but its strict inequality is false at
`n=0` and `n=1`.  The missing condition `1 < n`, already present throughout
the induction step, is restored.
-/
theorem gap10
    (h1 : BaseProductValue)
    (h2 : BasePowerValue)
    (h3 : BaseStrictBound)
    (h4 : AppendEvenFactorial)
    (h5 : SplitLargeFactorial)
    (h6 : SubstituteFactorialSplit)
    (h7 : LowerBoundTailProduct)
    (h8 : CombineFactorialAndPower)
    (h9 : InductionStep) :
    CorrectedFinalBound := by
  intro n
  induction n with
  | zero =>
      intro hn
      omega
  | succ k ih =>
      intro hn
      by_cases hk : k = 1
      · subst k
        exact h3 2 rfl
      · exact h9 k (by omega) (ih (by omega))

/--
Exercise 9, gap 11.

This repeats the corrected final result from gap 10.
-/
theorem gap11
    (h1 : BaseProductValue)
    (h2 : BasePowerValue)
    (h3 : BaseStrictBound)
    (h4 : AppendEvenFactorial)
    (h5 : SplitLargeFactorial)
    (h6 : SubstituteFactorialSplit)
    (h7 : LowerBoundTailProduct)
    (h8 : CombineFactorialAndPower)
    (h9 : InductionStep)
    (h10 : CorrectedFinalBound) :
    CorrectedFinalBound := by
  exact h10

end ProofGap.Exercise9
