import ProofGapLean.Prelude.Core
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

namespace ProofGap.Exercise201

def affine (a b t : ℝ) : ℝ := a * t + b
def ArithmeticSeq (x : ℕ → ℝ) (d : ℝ) : Prop :=
  ∀ n : ℕ, x n = x 1 + ((n - 1 : ℕ) : ℝ) * d
def y (a b : ℝ) (x : ℕ → ℝ) (n : ℕ) : ℝ := affine a b (x n)

/-- Exercise 201, gap 1. -/
theorem gap1 (x : ℕ → ℝ) (d : ℝ) (h : ArithmeticSeq x d) :
    ∀ n, x n = x 1 + ((n - 1 : ℕ) : ℝ) * d := by
  exact h

/-- Exercise 201, gap 2; n must be positive before n-1. -/
theorem gap2 (a b : ℝ) (x : ℕ → ℝ) :
    ∀ n : ℕ, 0 < n →
      y a b x n - y a b x (n - 1) =
        (a * x n + b) - (a * x (n - 1) + b) := by
  intro n _
  rfl

/-- Exercise 201, gap 3; n≥2 is required for n-2. -/
theorem gap3 (a b d : ℝ) (x : ℕ → ℝ) (h : ArithmeticSeq x d) :
    ∀ n : ℕ, 2 ≤ n →
      y a b x n - y a b x (n - 1) =
        (a * (x 1 + ((n - 1 : ℕ) : ℝ) * d) + b) -
        (a * (x 1 + ((n - 2 : ℕ) : ℝ) * d) + b) := by
  intro n hn
  unfold y affine
  rw [h n, h (n - 1)]
  congr 2

/-- Exercise 201, gap 4; n≥2 prevents natural underflow. -/
theorem gap4 (a b d : ℝ) (x : ℕ → ℝ) :
    ∀ n : ℕ, 2 ≤ n →
      (a * (x 1 + ((n - 1 : ℕ) : ℝ) * d) + b) -
        (a * (x 1 + ((n - 2 : ℕ) : ℝ) * d) + b) = a * d := by
  intro n hn
  have hsub : n - 1 = (n - 2) + 1 := by omega
  rw [hsub, Nat.cast_add, Nat.cast_one]
  ring

/-- Exercise 201, gap 5. -/
theorem gap5 (a b d : ℝ) (x : ℕ → ℝ) (h : ArithmeticSeq x d) :
    ∀ n : ℕ, 2 ≤ n → y a b x n - y a b x (n - 1) = a * d := by
  intro n hn
  calc
    y a b x n - y a b x (n - 1) =
        (a * (x 1 + ((n - 1 : ℕ) : ℝ) * d) + b) -
          (a * (x 1 + ((n - 2 : ℕ) : ℝ) * d) + b) :=
      gap3 a b d x h n hn
    _ = a * d := gap4 a b d x n hn

/-- Exercise 201, gap 6. -/
theorem gap6 (a b d : ℝ) (x : ℕ → ℝ) (h : ArithmeticSeq x d) :
    ∀ n : ℕ, 2 ≤ n → y a b x n - y a b x (n - 1) = a * d := by
  exact gap5 a b d x h

/-- Exercise 201, gap 7. -/
theorem gap7 (a b d : ℝ) (x : ℕ → ℝ) (h : ArithmeticSeq x d) :
    ∀ n : ℕ, 2 ≤ n → y a b x n - y a b x (n - 1) = a * d := by
  exact gap5 a b d x h

end ProofGap.Exercise201
