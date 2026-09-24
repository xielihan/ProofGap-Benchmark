import ProofGapLean.Prelude.Elementary

/-!
# Exercise 21 (part 1)

Semantic formalization of `proof_gap/exercise_21_1/{1,...,13}.txt`.
Both source proofs of the reverse triangle inequality are retained.
-/

namespace ProofGap.Exercise21_1

def P1 : Prop :=
  ∀ x y : ℝ, |x - y| = |x + -y|

def P2 : Prop :=
  ∀ x y : ℝ, |x + -y| ≥ |x| - |-y|

def P3 : Prop :=
  ∀ x y : ℝ, |x| - |-y| = |x| - |y|

def P4 : Prop :=
  ∀ x y : ℝ, |x - y| ≥ |x| - |y|

def P5 : Prop :=
  ∀ x y : ℝ, |x - y| = |y - x|

def P6 : Prop :=
  ∀ y x : ℝ, |y - x| ≥ |y| - |x|

def P7 : Prop :=
  ∀ y x : ℝ, |y| - |x| = -(|x| - |y|)

def P8 : Prop :=
  ∀ x y : ℝ, |x - y| ≥ -(|x| - |y|)

def ReverseTriangle : Prop :=
  ∀ x y : ℝ, |x - y| ≥ abs (|x| - |y|)

def SquareComparisonExpanded : Prop :=
  ∀ x y : ℝ,
    x ^ 2 - 2 * x * y + y ^ 2 ≥
      x ^ 2 - 2 * |x * y| + y ^ 2

def SquareComparison : Prop :=
  ∀ x y : ℝ, (x - y) ^ 2 ≥ (|x| - |y|) ^ 2

/-- Source: `proof_gap/exercise_21_1/1.txt`. -/
theorem gap1 : P1 := by
  intro x y
  rw [sub_eq_add_neg]

/-- Source: `proof_gap/exercise_21_1/2.txt`. -/
theorem gap2 (h1 : P1) : P2 := by
  intro x y
  have htri := abs_add_le (x + -y) y
  have hsum : x + -y + y = x := by ring
  rw [hsum] at htri
  rw [abs_neg]
  linarith

/-- Source: `proof_gap/exercise_21_1/3.txt`. -/
theorem gap3 (h1 : P1) (h2 : P2) : P3 := by
  intro x y
  rw [abs_neg]

/-- Source: `proof_gap/exercise_21_1/4.txt`. -/
theorem gap4 (h1 : P1) (h2 : P2) (h3 : P3) : P4 := by
  intro x y
  calc
    |x - y| = |x + -y| := h1 x y
    _ ≥ |x| - |-y| := h2 x y
    _ = |x| - |y| := h3 x y

/-- Source: `proof_gap/exercise_21_1/5.txt`. -/
theorem gap5 (h4 : P4) : P5 := by
  intro x y
  exact abs_sub_comm x y

/-- Source: `proof_gap/exercise_21_1/6.txt`. -/
theorem gap6 (h4 : P4) (h5 : P5) : P6 := by
  intro y x
  exact h4 y x

/-- Source: `proof_gap/exercise_21_1/7.txt`. -/
theorem gap7 (h6 : P6) : P7 := by
  intro y x
  ring

/-- Source: `proof_gap/exercise_21_1/8.txt`. -/
theorem gap8 (h5 : P5) (h6 : P6) (h7 : P7) : P8 := by
  intro x y
  calc
    |x - y| = |y - x| := h5 x y
    _ ≥ |y| - |x| := h6 y x
    _ = -(|x| - |y|) := h7 y x

/-- Source: `proof_gap/exercise_21_1/9.txt`. -/
theorem gap9 (h4 : P4) (h8 : P8) : ReverseTriangle := by
  intro x y
  by_cases hnonneg : 0 ≤ |x| - |y|
  · rw [abs_of_nonneg hnonneg]
    exact h4 x y
  · rw [abs_of_neg (lt_of_not_ge hnonneg)]
    exact h8 x y

/-- Source: `proof_gap/exercise_21_1/10.txt`. -/
theorem gap10 (h9 : ReverseTriangle) : SquareComparisonExpanded := by
  intro x y
  nlinarith [le_abs_self (x * y)]

/-- Source: `proof_gap/exercise_21_1/11.txt`. -/
theorem gap11
    (h10 : SquareComparisonExpanded) :
    SquareComparison := by
  intro x y
  have h := h10 x y
  rw [abs_mul] at h
  nlinarith [sq_abs x, sq_abs y]

/-- Source: `proof_gap/exercise_21_1/12.txt`. -/
theorem gap12
    (h11 : SquareComparison) :
    ReverseTriangle := by
  intro x y
  have hsq :
      abs (|x| - |y|) ^ 2 ≤ abs (x - y) ^ 2 := by
    simpa only [sq_abs] using h11 x y
  exact (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).mp hsq

/-- Source: `proof_gap/exercise_21_1/13.txt`. -/
theorem gap13
    (h12 : ReverseTriangle) :
    ReverseTriangle := by
  exact h12

end ProofGap.Exercise21_1
