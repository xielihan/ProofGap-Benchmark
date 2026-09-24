import ProofGapLean.Prelude.Elementary

namespace ProofGap.Exercise202

noncomputable section

def f (a t : ℝ) : ℝ := Real.rpow a t
def ConstantDifference (x : ℕ → ℝ) (d : ℝ) : Prop :=
  ∀ n : ℕ, 0 < n → x n - x (n - 1) = d
def y (a : ℝ) (x : ℕ → ℝ) (n : ℕ) : ℝ := f a (x n)

/-- Exercise 202, gap 1; restore n>0. -/
theorem gap1 (x : ℕ → ℝ) (d : ℝ) (h : ConstantDifference x d) :
    ∀ n : ℕ, 0 < n → x n - x (n - 1) = d := by
  exact h

/-- Exercise 202, gap 2; restore n>0 and a>0. -/
theorem gap2 (a : ℝ) (x : ℕ → ℝ) (ha : 0 < a) :
    ∀ n : ℕ, 0 < n →
      y a x n / y a x (n - 1) =
        Real.rpow a (x n) / Real.rpow a (x (n - 1)) := by
  intro n _
  rfl

/-- Exercise 202, gap 3. -/
theorem gap3 (a : ℝ) (x : ℕ → ℝ) (ha : 0 < a) :
    ∀ n : ℕ, 0 < n →
      Real.rpow a (x n) / Real.rpow a (x (n - 1)) =
        Real.rpow a (x n - x (n - 1)) := by
  intro n _
  exact (Real.rpow_sub ha _ _).symm

/-- Exercise 202, gap 4. -/
theorem gap4 (a d : ℝ) (x : ℕ → ℝ) (h : ConstantDifference x d) :
    ∀ n : ℕ, 0 < n →
      Real.rpow a (x n - x (n - 1)) = Real.rpow a d := by
  intro n hn
  rw [h n hn]

/-- Exercise 202, gap 5. -/
theorem gap5 (a d : ℝ) (x : ℕ → ℝ) (ha : 0 < a)
    (h : ConstantDifference x d) :
    ∀ n : ℕ, 0 < n → y a x n / y a x (n - 1) = Real.rpow a d := by
  intro n hn
  rw [gap2 a x ha n hn, gap3 a x ha n hn, gap4 a d x h n hn]

/-- Exercise 202, gap 6. -/
theorem gap6 (a d : ℝ) (x : ℕ → ℝ) (ha : 0 < a)
    (h : ConstantDifference x d) :
    ∀ n : ℕ, 0 < n → y a x n / y a x (n - 1) = Real.rpow a d := by
  exact gap5 a d x ha h

/-- Exercise 202, gap 7. -/
theorem gap7 (a d : ℝ) (x : ℕ → ℝ) (ha : 0 < a)
    (h : ConstantDifference x d) :
    ∀ n : ℕ, 0 < n → y a x n / y a x (n - 1) = Real.rpow a d := by
  exact gap5 a d x ha h

end

end ProofGap.Exercise202
