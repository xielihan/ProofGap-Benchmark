import Mathlib

set_option linter.style.longLine false

open scoped BigOperators Topology Nat

open Filter

local notation:70 x " /. " y => ((x : ℝ) / (y : ℝ))

open scoped RealInnerProductSpace

noncomputable def lpFunDeri {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] (f g : E -> ℝ) : E -> ℝ :=
  fun x => (inner ℝ (gradient f x) (gradient g x)) /. (‖gradient g x‖ ^ 2)

def lpLeftDifferentiable (f : ℝ -> ℝ) : Prop :=
  ∀ x, DifferentiableWithinAt ℝ f (Set.Iio x) x

def lpRightDifferentiable (f : ℝ -> ℝ) : Prop :=
  ∀ x, DifferentiableWithinAt ℝ f (Set.Ioi x) x

def lpLeftDifferentiableOn (f : ℝ -> ℝ) (s : Set ℝ) : Prop :=
  ∀ x ∈ s, DifferentiableWithinAt ℝ f (s ∩ Set.Iio x) x

def lpRightDifferentiableOn (f : ℝ -> ℝ) (s : Set ℝ) : Prop :=
  ∀ x ∈ s, DifferentiableWithinAt ℝ f (s ∩ Set.Ioi x) x

def lpMaximumPoints {α β : Type*} [Preorder β] (f : α -> β) : Set α :=
  {x | ∀ y, f y ≤ f x}

def lpMinimumPoints {α β : Type*} [Preorder β] (f : α -> β) : Set α :=
  {x | ∀ y, f x ≤ f y}

def lpMaximumPointsOn {α β : Type*} [Preorder β] (f : α -> β) (s : Set α) : Set α :=
  {x | x ∈ s ∧ ∀ y ∈ s, f y ≤ f x}

def lpMinimumPointsOn {α β : Type*} [Preorder β] (f : α -> β) (s : Set α) : Set α :=
  {x | x ∈ s ∧ ∀ y ∈ s, f x ≤ f y}

noncomputable def lpRadiusOfConvergence {𝕜 : Type*} [NormedField 𝕜] (a : ℕ -> 𝕜) : ENNReal :=
  ⨆ (r : NNReal), ⨆ (_h : Summable (fun n : ℕ => ‖a n‖ * (r : ℝ) ^ n)), (r : ENNReal)

-- exercise: exercise_2859

theorem proof_gap_exercise_2859_1
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (((6 - (5 * x)) - (x ^ (2 : ℕ))) ≠ 0)) → ((f x) = ((12 - (5 * x)) /. ((6 - (5 * x)) - (x ^ (2 : ℕ))))))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| < 1)) → ((f x) = ((1 /. (1 - x)) + (6 /. (6 + x)))))) := by
  sorry

theorem proof_gap_exercise_2859_2
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (((6 - (5 * x)) - (x ^ (2 : ℕ))) ≠ 0)) → ((f x) = ((12 - (5 * x)) /. ((6 - (5 * x)) - (x ^ (2 : ℕ))))))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| < 1)) → ((f x) = ((1 /. (1 - x)) + (6 /. (6 + x)))))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| < 1)) → ((f x) = ((1 /. (1 - x)) + (1 /. (1 + (x /. 6))))))) := by
  sorry

theorem proof_gap_exercise_2859_3
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (((6 - (5 * x)) - (x ^ (2 : ℕ))) ≠ 0)) → ((f x) = ((12 - (5 * x)) /. ((6 - (5 * x)) - (x ^ (2 : ℕ))))))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| < 1)) → ((f x) = ((1 /. (1 - x)) + (6 /. (6 + x)))))))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| < 1)) → ((f x) = ((1 /. (1 - x)) + (1 /. (1 + (x /. 6))))))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| < 1)) → ((1 /. (1 - x)) = (∑' n, if (0 : ℕ) ≤ n then (x ^ n) else 0)))) := by
  sorry

theorem proof_gap_exercise_2859_4
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (((6 - (5 * x)) - (x ^ (2 : ℕ))) ≠ 0)) → ((f x) = ((12 - (5 * x)) /. ((6 - (5 * x)) - (x ^ (2 : ℕ))))))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| < 1)) → ((f x) = ((1 /. (1 - x)) + (6 /. (6 + x)))))))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| < 1)) → ((f x) = ((1 /. (1 - x)) + (1 /. (1 + (x /. 6))))))))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| < 1)) → ((1 /. (1 - x)) = (∑' n, if (0 : ℕ) ≤ n then (x ^ n) else 0)))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| < 1)) → ((1 /. (1 + (x /. 6))) = (∑' n, if (0 : ℕ) ≤ n then (((-(1 /. 6)) ^ n) * (x ^ n)) else 0)))) := by
  sorry

theorem proof_gap_exercise_2859_5
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (((6 - (5 * x)) - (x ^ (2 : ℕ))) ≠ 0)) → ((f x) = ((12 - (5 * x)) /. ((6 - (5 * x)) - (x ^ (2 : ℕ))))))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| < 1)) → ((f x) = ((1 /. (1 - x)) + (6 /. (6 + x)))))))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| < 1)) → ((f x) = ((1 /. (1 - x)) + (1 /. (1 + (x /. 6))))))))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| < 1)) → ((1 /. (1 - x)) = (∑' n, if (0 : ℕ) ≤ n then (x ^ n) else 0)))))
  (h5 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| < 1)) → ((1 /. (1 + (x /. 6))) = (∑' n, if (0 : ℕ) ≤ n then (((-(1 /. 6)) ^ n) * (x ^ n)) else 0)))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| < 1)) → ((f x) = ((∑' n, if (0 : ℕ) ≤ n then (x ^ n) else 0) + (∑' n, if (0 : ℕ) ≤ n then (((-(1 /. 6)) ^ n) * (x ^ n)) else 0))))) := by
  sorry

theorem proof_gap_exercise_2859_6
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (((6 - (5 * x)) - (x ^ (2 : ℕ))) ≠ 0)) → ((f x) = ((12 - (5 * x)) /. ((6 - (5 * x)) - (x ^ (2 : ℕ))))))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| < 1)) → ((f x) = ((1 /. (1 - x)) + (6 /. (6 + x)))))))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| < 1)) → ((f x) = ((1 /. (1 - x)) + (1 /. (1 + (x /. 6))))))))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| < 1)) → ((1 /. (1 - x)) = (∑' n, if (0 : ℕ) ≤ n then (x ^ n) else 0)))))
  (h5 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| < 1)) → ((1 /. (1 + (x /. 6))) = (∑' n, if (0 : ℕ) ≤ n then (((-(1 /. 6)) ^ n) * (x ^ n)) else 0)))))
  (h6 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| < 1)) → ((f x) = ((∑' n, if (0 : ℕ) ≤ n then (x ^ n) else 0) + (∑' n, if (0 : ℕ) ≤ n then (((-(1 /. 6)) ^ n) * (x ^ n)) else 0))))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| < 1)) → ((f x) = (∑' n, if (0 : ℕ) ≤ n then ((1 + (((-(1 : ℤ)) ^ n) /. ((6 : ℕ) ^ n))) * (x ^ n)) else 0)))) := by
  sorry

theorem proof_gap_exercise_2859_7
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (((6 - (5 * x)) - (x ^ (2 : ℕ))) ≠ 0)) → ((f x) = ((12 - (5 * x)) /. ((6 - (5 * x)) - (x ^ (2 : ℕ))))))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| < 1)) → ((f x) = ((1 /. (1 - x)) + (6 /. (6 + x)))))))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| < 1)) → ((f x) = ((1 /. (1 - x)) + (1 /. (1 + (x /. 6))))))))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| < 1)) → ((1 /. (1 - x)) = (∑' n, if (0 : ℕ) ≤ n then (x ^ n) else 0)))))
  (h5 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| < 1)) → ((1 /. (1 + (x /. 6))) = (∑' n, if (0 : ℕ) ≤ n then (((-(1 /. 6)) ^ n) * (x ^ n)) else 0)))))
  (h6 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| < 1)) → ((f x) = ((∑' n, if (0 : ℕ) ≤ n then (x ^ n) else 0) + (∑' n, if (0 : ℕ) ≤ n then (((-(1 /. 6)) ^ n) * (x ^ n)) else 0))))))
  (h7 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| < 1)) → ((f x) = (∑' n, if (0 : ℕ) ≤ n then ((1 + (((-(1 : ℤ)) ^ n) /. ((6 : ℕ) ^ n))) * (x ^ n)) else 0)))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| < 1)) → ((f x) = (∑' n, if (0 : ℕ) ≤ n then ((1 + (((-(1 : ℤ)) ^ n) /. ((6 : ℕ) ^ n))) * (x ^ n)) else 0)))) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| < 1)) → ((f x) = (∑' n, if (0 : ℕ) ≤ n then ((1 + (((-(1 : ℤ)) ^ n) /. ((6 : ℕ) ^ n))) * (x ^ n)) else 0)))) := by
  sorry
