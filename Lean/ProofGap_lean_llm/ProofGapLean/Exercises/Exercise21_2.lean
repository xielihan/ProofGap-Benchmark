import ProofGapLean.Prelude.Elementary

/-!
# Exercise 21 (part 2)

Semantic formalization of `proof_gap/exercise_21_2/{1,...,7}.txt`.
The source's informal ellipses `x₁ + ... + xₙ` are represented by finite lists
of real numbers.
-/

namespace ProofGap.Exercise21_2

def sumAbs (xs : List ℝ) : ℝ :=
  (xs.map fun x => |x|).sum

def InitialReverseStep : Prop :=
  ∀ (x : ℝ) (xs : List ℝ),
    |x + xs.sum| ≥ |x| - |xs.sum|

def HeadTailTriangleStep : Prop :=
  ∀ (x : ℝ) (xs : List ℝ),
    |x + xs.sum| ≤ |x| + |xs.sum|

def TwoTermTriangleStep : Prop :=
  ∀ (x₁ x₂ : ℝ) (xs : List ℝ),
    |x₁| + |x₂ + xs.sum| ≤ |x₁| + |x₂| + |xs.sum|

def FiniteTriangle : Prop :=
  ∀ xs : List ℝ, |xs.sum| ≤ sumAbs xs

def FinalInequality : Prop :=
  ∀ (x : ℝ) (xs : List ℝ),
    |x + xs.sum| ≥ |x| - sumAbs xs

/-- Source: `proof_gap/exercise_21_2/1.txt`. -/
theorem gap1 : InitialReverseStep := by
  intro x xs
  have htri := abs_add_le (x + xs.sum) (-xs.sum)
  have hsum : x + xs.sum + -xs.sum = x := by ring
  rw [hsum, abs_neg] at htri
  linarith

/-- Source: `proof_gap/exercise_21_2/2.txt`. -/
theorem gap2
    (h1 : InitialReverseStep) :
    HeadTailTriangleStep := by
  intro x xs
  exact abs_add_le x xs.sum

/-- Source: `proof_gap/exercise_21_2/3.txt`. -/
theorem gap3
    (h2 : HeadTailTriangleStep) :
    TwoTermTriangleStep := by
  intro x₁ x₂ xs
  linarith [h2 x₂ xs]

/-- Source: `proof_gap/exercise_21_2/4.txt`. -/
theorem gap4
    (h2 : HeadTailTriangleStep)
    (h3 : TwoTermTriangleStep) :
    FiniteTriangle := by
  intro xs
  induction xs with
  | nil =>
      simp [sumAbs]
  | cons x xs ih =>
      simp only [List.sum_cons, sumAbs, List.map_cons]
      apply (h2 x xs).trans
      simpa [add_comm] using add_le_add_left ih |x|

/-- Source: `proof_gap/exercise_21_2/5.txt`. -/
theorem gap5
    (h4 : FiniteTriangle) :
    FiniteTriangle := by
  exact h4

/-- Source: `proof_gap/exercise_21_2/6.txt`. -/
theorem gap6
    (h1 : InitialReverseStep)
    (h5 : FiniteTriangle) :
    FinalInequality := by
  intro x xs
  linarith [h1 x xs, h5 xs]

/-- Source: `proof_gap/exercise_21_2/7.txt`. -/
theorem gap7
    (h6 : FinalInequality) :
    FinalInequality := by
  exact h6

end ProofGap.Exercise21_2
