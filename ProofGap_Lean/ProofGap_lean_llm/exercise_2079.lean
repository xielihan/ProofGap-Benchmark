import Mathlib

set_option linter.style.longLine false

open scoped BigOperators Topology

noncomputable section

def AntiderivSet (f : ℝ -> ℝ) : Set (ℝ -> ℝ) :=
  {F | ∀ x : ℝ, deriv F x = f x}

def antiderivExprSet (g : ℝ -> ℝ) : Set (ℝ -> ℝ) :=
  {F | ∃ C : ℝ, ∀ x : ℝ, F x = g x + C}

-- exercise: exercise_2079

-- gap 1: expand (x - sin x)^3.
theorem proof_gap_exercise_2079_1 :
    AntiderivSet (fun x : ℝ => (x - Real.sin x) ^ 3) =
      AntiderivSet (fun x : ℝ => x ^ 3 - 3 * x ^ 2 * Real.sin x + 3 * x * (Real.sin x) ^ 2 - (Real.sin x) ^ 3) := by
  sorry

-- gap 2: split the expanded integral into four terms using d(cos x) and sin^2 x = (1 - cos 2x)/2.
theorem proof_gap_exercise_2079_2
    (h1 : AntiderivSet (fun x : ℝ => (x - Real.sin x) ^ 3) =
      AntiderivSet (fun x : ℝ => x ^ 3 - 3 * x ^ 2 * Real.sin x + 3 * x * (Real.sin x) ^ 2 - (Real.sin x) ^ 3)) :
    AntiderivSet (fun x : ℝ => (x - Real.sin x) ^ 3) =
      {F | ∃ G H K : ℝ -> ℝ,
        G ∈ AntiderivSet (fun x : ℝ => x ^ 2 * deriv (fun y : ℝ => Real.cos y) x) ∧
        H ∈ AntiderivSet (fun x : ℝ => x * (1 - Real.cos (2 * x))) ∧
        K ∈ AntiderivSet (fun x : ℝ => (1 - (Real.cos x) ^ 2) * deriv (fun y : ℝ => Real.cos y) x) ∧
        ∀ x : ℝ, F x = x ^ 4 / 4 + 3 * G x + (3 / 2 : ℝ) * H x + K x} := by
  sorry

-- gap 3: first integration-by-parts simplification.
theorem proof_gap_exercise_2079_3 :
    AntiderivSet (fun x : ℝ => (x - Real.sin x) ^ 3) =
      {F | ∃ G H : ℝ -> ℝ,
        G ∈ AntiderivSet (fun x : ℝ => x * Real.cos x) ∧
        H ∈ AntiderivSet (fun x : ℝ => x * deriv (fun y : ℝ => Real.sin (2 * y)) x) ∧
        ∀ x : ℝ, F x =
          x ^ 4 / 4 + 3 * x ^ 2 * Real.cos x - 6 * G x +
          (3 / 4 : ℝ) * x ^ 2 - (3 / 4 : ℝ) * H x +
          Real.cos x - (1 / 3 : ℝ) * (Real.cos x) ^ 3} := by
  sorry

-- gap 4: integrate by parts in the x cos x and x d(sin 2x) terms.
theorem proof_gap_exercise_2079_4 :
    AntiderivSet (fun x : ℝ => (x - Real.sin x) ^ 3) =
      {F | ∃ G H : ℝ -> ℝ,
        G ∈ AntiderivSet (fun x : ℝ => x * deriv (fun y : ℝ => Real.sin y) x) ∧
        H ∈ AntiderivSet (fun x : ℝ => Real.sin (2 * x)) ∧
        ∀ x : ℝ, F x =
          x ^ 4 / 4 + (3 * x ^ 2) / 4 + 3 * x ^ 2 * Real.cos x -
          6 * G x - (3 / 4 : ℝ) * x * Real.sin (2 * x) +
          (3 / 4 : ℝ) * H x + Real.cos x - (1 / 3 : ℝ) * (Real.cos x) ^ 3} := by
  sorry

-- gap 5: antiderivative of x d(sin x).
theorem proof_gap_exercise_2079_5 :
    (fun x : ℝ => x * Real.sin x + Real.cos x) ∈
      AntiderivSet (fun x : ℝ => x * deriv (fun y : ℝ => Real.sin y) x) := by
  sorry

-- gap 6: antiderivative of sin(2x).
theorem proof_gap_exercise_2079_6 :
    (fun x : ℝ => -(1 / 2 : ℝ) * Real.cos (2 * x)) ∈
      AntiderivSet (fun x : ℝ => Real.sin (2 * x)) := by
  sorry

-- gap 7: collect the penultimate expression with arbitrary constant.
theorem proof_gap_exercise_2079_7 :
    AntiderivSet (fun x : ℝ => (x - Real.sin x) ^ 3) =
      antiderivExprSet (fun x : ℝ =>
        x ^ 4 / 4 + (3 * x ^ 2) / 4 + 3 * x ^ 2 * Real.cos x -
        6 * x * Real.sin x - 6 * Real.cos x -
        (3 / 4 : ℝ) * x * Real.sin (2 * x) + Real.cos x -
        (3 / 8 : ℝ) * Real.cos (2 * x) - (1 / 3 : ℝ) * (Real.cos x) ^ 3) := by
  sorry

-- gap 8: regroup the final expression.
theorem proof_gap_exercise_2079_8 :
    AntiderivSet (fun x : ℝ => (x - Real.sin x) ^ 3) =
      antiderivExprSet (fun x : ℝ =>
        x ^ 4 / 4 + (3 * x ^ 2) / 4 + 3 * x ^ 2 * Real.cos x -
        x * (6 * Real.sin x + (3 / 4 : ℝ) * Real.sin (2 * x)) -
        (5 * Real.cos x + (3 / 8 : ℝ) * Real.cos (2 * x)) -
        (1 / 3 : ℝ) * (Real.cos x) ^ 3) := by
  sorry

end
