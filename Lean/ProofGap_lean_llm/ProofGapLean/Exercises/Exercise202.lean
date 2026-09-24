import ProofGapLean.Prelude.Elementary

namespace ProofGap.Exercise202

noncomputable section

def f (a t : ℝ) : ℝ := Real.rpow a t
def ConstantDifference (x : ℕ → ℝ) (d : ℝ) : Prop :=
  ∀ n : ℕ, 0 < n → x n - x (n - 1) = d
def y (a : ℝ) (x : ℕ → ℝ) (n : ℕ) : ℝ := f a (x n)

/-- Source: `proof_gap/exercise_202/1.txt`; restore n>0. -/
theorem gap1 (x : ℕ → ℝ) (d : ℝ) (h : ConstantDifference x d) :
    ∀ n : ℕ, 0 < n → x n - x (n - 1) = d := by
  exact h

/-- Source: `proof_gap/exercise_202/2.txt`; restore n>0 and a>0. -/
theorem gap2 (a : ℝ) (x : ℕ → ℝ) (ha : 0 < a) :
    ∀ n : ℕ, 0 < n →
      y a x n / y a x (n - 1) =
        Real.rpow a (x n) / Real.rpow a (x (n - 1)) := by
  intro n _
  rfl

/-- Source: `proof_gap/exercise_202/3.txt`. -/
theorem gap3 (a : ℝ) (x : ℕ → ℝ) (ha : 0 < a) :
    ∀ n : ℕ, 0 < n →
      Real.rpow a (x n) / Real.rpow a (x (n - 1)) =
        Real.rpow a (x n - x (n - 1)) := by
  intro n _
  exact (Real.rpow_sub ha _ _).symm

/-- Source: `proof_gap/exercise_202/4.txt`. -/
theorem gap4 (a d : ℝ) (x : ℕ → ℝ) (h : ConstantDifference x d) :
    ∀ n : ℕ, 0 < n →
      Real.rpow a (x n - x (n - 1)) = Real.rpow a d := by
  intro n hn
  rw [h n hn]

/-- Source: `proof_gap/exercise_202/5.txt`. -/
theorem gap5 (a d : ℝ) (x : ℕ → ℝ) (ha : 0 < a)
    (h : ConstantDifference x d) :
    ∀ n : ℕ, 0 < n → y a x n / y a x (n - 1) = Real.rpow a d := by
  intro n hn
  rw [gap2 a x ha n hn, gap3 a x ha n hn, gap4 a d x h n hn]

/-- Source: `proof_gap/exercise_202/6.txt`. -/
theorem gap6 (a d : ℝ) (x : ℕ → ℝ) (ha : 0 < a)
    (h : ConstantDifference x d) :
    ∀ n : ℕ, 0 < n → y a x n / y a x (n - 1) = Real.rpow a d := by
  exact gap5 a d x ha h

/-- Source: `proof_gap/exercise_202/7.txt`. -/
theorem gap7 (a d : ℝ) (x : ℕ → ℝ) (ha : 0 < a)
    (h : ConstantDifference x d) :
    ∀ n : ℕ, 0 < n → y a x n / y a x (n - 1) = Real.rpow a d := by
  exact gap5 a d x ha h

end

end ProofGap.Exercise202
