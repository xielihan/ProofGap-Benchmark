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

-- exercise: exercise_2717

theorem proof_gap_exercise_2717_1
  (u : (ℝ × ℕ -> ℝ))
  (A : (Set ℝ))
  (C : (Set ℝ))
  (h1 : A ⊆ (Set.univ : Set ℝ))
  (h2 : C ⊆ (Set.univ : Set ℝ))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ (-(1 : ℝ)))) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ≥ 1)) → ((u (x, n)) = ((((-(1 : ℤ)) ^ n) /. ((2 * n) - 1)) * (((1 - x) /. (1 + x)) ^ n))))))))
  : Tendsto (fun n : ℕ => (|(((Real.rpow (-(1 : ℝ)) n) /. ((2 * n) - 1)))| /. |(((Real.rpow (-(1 : ℝ)) (n + 1)) /. ((2 * n) + 1)))|)) atTop (𝓝 1) := by
  sorry

theorem proof_gap_exercise_2717_2
  (u : (ℝ × ℕ -> ℝ))
  (A : (Set ℝ))
  (C : (Set ℝ))
  (h1 : A ⊆ (Set.univ : Set ℝ))
  (h2 : C ⊆ (Set.univ : Set ℝ))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ (-(1 : ℝ)))) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ≥ 1)) → ((u (x, n)) = ((((-(1 : ℤ)) ^ n) /. ((2 * n) - 1)) * (((1 - x) /. (1 + x)) ^ n))))))))
  (h4 : Tendsto (fun n : ℕ => (|(((Real.rpow (-(1 : ℝ)) n) /. ((2 * n) - 1)))| /. |(((Real.rpow (-(1 : ℝ)) (n + 1)) /. ((2 * n) + 1)))|)) atTop (𝓝 1))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ (-(1 : ℝ)))) → ((|(((1 - x) /. (1 + x)))| < 1) ↔ (((1 - x) ^ (2 : ℕ)) < ((1 + x) ^ (2 : ℕ)))))) := by
  sorry

theorem proof_gap_exercise_2717_3
  (u : (ℝ × ℕ -> ℝ))
  (A : (Set ℝ))
  (C : (Set ℝ))
  (h1 : A ⊆ (Set.univ : Set ℝ))
  (h2 : C ⊆ (Set.univ : Set ℝ))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ (-(1 : ℝ)))) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ≥ 1)) → ((u (x, n)) = ((((-(1 : ℤ)) ^ n) /. ((2 * n) - 1)) * (((1 - x) /. (1 + x)) ^ n))))))))
  (h4 : Tendsto (fun n : ℕ => (|(((Real.rpow (-(1 : ℝ)) n) /. ((2 * n) - 1)))| /. |(((Real.rpow (-(1 : ℝ)) (n + 1)) /. ((2 * n) + 1)))|)) atTop (𝓝 1))
  (h5 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ (-(1 : ℝ)))) → ((|(((1 - x) /. (1 + x)))| < 1) ↔ (((1 - x) ^ (2 : ℕ)) < ((1 + x) ^ (2 : ℕ)))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((((1 - x) ^ (2 : ℕ)) < ((1 + x) ^ (2 : ℕ))) ↔ (x > 0)))) := by
  sorry

theorem proof_gap_exercise_2717_4
  (u : (ℝ × ℕ -> ℝ))
  (A : (Set ℝ))
  (C : (Set ℝ))
  (h1 : A ⊆ (Set.univ : Set ℝ))
  (h2 : C ⊆ (Set.univ : Set ℝ))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ (-(1 : ℝ)))) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ≥ 1)) → ((u (x, n)) = ((((-(1 : ℤ)) ^ n) /. ((2 * n) - 1)) * (((1 - x) /. (1 + x)) ^ n))))))))
  (h4 : Tendsto (fun n : ℕ => (|(((Real.rpow (-(1 : ℝ)) n) /. ((2 * n) - 1)))| /. |(((Real.rpow (-(1 : ℝ)) (n + 1)) /. ((2 * n) + 1)))|)) atTop (𝓝 1))
  (h5 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ (-(1 : ℝ)))) → ((|(((1 - x) /. (1 + x)))| < 1) ↔ (((1 - x) ^ (2 : ℕ)) < ((1 + x) ^ (2 : ℕ)))))))
  (h6 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((((1 - x) ^ (2 : ℕ)) < ((1 + x) ^ (2 : ℕ))) ↔ (x > 0)))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((u (x, n)))‖ else 0)))) := by
  sorry

theorem proof_gap_exercise_2717_5
  (u : (ℝ × ℕ -> ℝ))
  (A : (Set ℝ))
  (C : (Set ℝ))
  (h1 : A ⊆ (Set.univ : Set ℝ))
  (h2 : C ⊆ (Set.univ : Set ℝ))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ (-(1 : ℝ)))) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ≥ 1)) → ((u (x, n)) = ((((-(1 : ℤ)) ^ n) /. ((2 * n) - 1)) * (((1 - x) /. (1 + x)) ^ n))))))))
  (h4 : Tendsto (fun n : ℕ => (|(((Real.rpow (-(1 : ℝ)) n) /. ((2 * n) - 1)))| /. |(((Real.rpow (-(1 : ℝ)) (n + 1)) /. ((2 * n) + 1)))|)) atTop (𝓝 1))
  (h5 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ (-(1 : ℝ)))) → ((|(((1 - x) /. (1 + x)))| < 1) ↔ (((1 - x) ^ (2 : ℕ)) < ((1 + x) ^ (2 : ℕ)))))))
  (h6 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((((1 - x) ^ (2 : ℕ)) < ((1 + x) ^ (2 : ℕ))) ↔ (x > 0)))))
  (h7 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((u (x, n)))‖ else 0)))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x = 0)) → ((∑' n, if (1 : ℕ) ≤ n then (u (x, n)) else 0) = (∑' n, if (1 : ℕ) ≤ n then (((-(1 : ℤ)) ^ n) /. ((2 * n) - 1)) else 0)))) := by
  sorry

theorem proof_gap_exercise_2717_6
  (u : (ℝ × ℕ -> ℝ))
  (A : (Set ℝ))
  (C : (Set ℝ))
  (h1 : A ⊆ (Set.univ : Set ℝ))
  (h2 : C ⊆ (Set.univ : Set ℝ))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ (-(1 : ℝ)))) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ≥ 1)) → ((u (x, n)) = ((((-(1 : ℤ)) ^ n) /. ((2 * n) - 1)) * (((1 - x) /. (1 + x)) ^ n))))))))
  (h4 : Tendsto (fun n : ℕ => (|(((Real.rpow (-(1 : ℝ)) n) /. ((2 * n) - 1)))| /. |(((Real.rpow (-(1 : ℝ)) (n + 1)) /. ((2 * n) + 1)))|)) atTop (𝓝 1))
  (h5 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ (-(1 : ℝ)))) → ((|(((1 - x) /. (1 + x)))| < 1) ↔ (((1 - x) ^ (2 : ℕ)) < ((1 + x) ^ (2 : ℕ)))))))
  (h6 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((((1 - x) ^ (2 : ℕ)) < ((1 + x) ^ (2 : ℕ))) ↔ (x > 0)))))
  (h7 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((u (x, n)))‖ else 0)))))
  (h8 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x = 0)) → ((∑' n, if (1 : ℕ) ≤ n then (u (x, n)) else 0) = (∑' n, if (1 : ℕ) ≤ n then (((-(1 : ℤ)) ^ n) /. ((2 * n) - 1)) else 0)))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x = 0)) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (u (x, n)) else 0) ∧ ¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((u (x, n)))‖ else 0)))) := by
  sorry

theorem proof_gap_exercise_2717_7
  (u : (ℝ × ℕ -> ℝ))
  (A : (Set ℝ))
  (C : (Set ℝ))
  (h1 : A ⊆ (Set.univ : Set ℝ))
  (h2 : C ⊆ (Set.univ : Set ℝ))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ (-(1 : ℝ)))) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ≥ 1)) → ((u (x, n)) = ((((-(1 : ℤ)) ^ n) /. ((2 * n) - 1)) * (((1 - x) /. (1 + x)) ^ n))))))))
  (h4 : Tendsto (fun n : ℕ => (|(((Real.rpow (-(1 : ℝ)) n) /. ((2 * n) - 1)))| /. |(((Real.rpow (-(1 : ℝ)) (n + 1)) /. ((2 * n) + 1)))|)) atTop (𝓝 1))
  (h5 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ (-(1 : ℝ)))) → ((|(((1 - x) /. (1 + x)))| < 1) ↔ (((1 - x) ^ (2 : ℕ)) < ((1 + x) ^ (2 : ℕ)))))))
  (h6 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((((1 - x) ^ (2 : ℕ)) < ((1 + x) ^ (2 : ℕ))) ↔ (x > 0)))))
  (h7 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((u (x, n)))‖ else 0)))))
  (h8 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x = 0)) → ((∑' n, if (1 : ℕ) ≤ n then (u (x, n)) else 0) = (∑' n, if (1 : ℕ) ≤ n then (((-(1 : ℤ)) ^ n) /. ((2 * n) - 1)) else 0)))))
  (h9 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x = 0)) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (u (x, n)) else 0) ∧ ¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((u (x, n)))‖ else 0)))))
  : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (x < 0)) ∧ (x ≠ (-(1 : ℝ)))) → (Not (Tendsto (fun n : ℕ => (u (x, n))) atTop (𝓝 0))))) := by
  sorry

theorem proof_gap_exercise_2717_8
  (u : (ℝ × ℕ -> ℝ))
  (A : (Set ℝ))
  (C : (Set ℝ))
  (h1 : A ⊆ (Set.univ : Set ℝ))
  (h2 : C ⊆ (Set.univ : Set ℝ))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ (-(1 : ℝ)))) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ≥ 1)) → ((u (x, n)) = ((((-(1 : ℤ)) ^ n) /. ((2 * n) - 1)) * (((1 - x) /. (1 + x)) ^ n))))))))
  (h4 : Tendsto (fun n : ℕ => (|(((Real.rpow (-(1 : ℝ)) n) /. ((2 * n) - 1)))| /. |(((Real.rpow (-(1 : ℝ)) (n + 1)) /. ((2 * n) + 1)))|)) atTop (𝓝 1))
  (h5 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ (-(1 : ℝ)))) → ((|(((1 - x) /. (1 + x)))| < 1) ↔ (((1 - x) ^ (2 : ℕ)) < ((1 + x) ^ (2 : ℕ)))))))
  (h6 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((((1 - x) ^ (2 : ℕ)) < ((1 + x) ^ (2 : ℕ))) ↔ (x > 0)))))
  (h7 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((u (x, n)))‖ else 0)))))
  (h8 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x = 0)) → ((∑' n, if (1 : ℕ) ≤ n then (u (x, n)) else 0) = (∑' n, if (1 : ℕ) ≤ n then (((-(1 : ℤ)) ^ n) /. ((2 * n) - 1)) else 0)))))
  (h9 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x = 0)) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (u (x, n)) else 0) ∧ ¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((u (x, n)))‖ else 0)))))
  (h10 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (x < 0)) ∧ (x ≠ (-(1 : ℝ)))) → (Not (Tendsto (fun n : ℕ => (u (x, n))) atTop (𝓝 0))))))
  : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (x < 0)) ∧ (x ≠ (-(1 : ℝ)))) → (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (u (x, n)) else 0)))) := by
  sorry

theorem proof_gap_exercise_2717_9
  (u : (ℝ × ℕ -> ℝ))
  (A : (Set ℝ))
  (C : (Set ℝ))
  (h1 : A ⊆ (Set.univ : Set ℝ))
  (h2 : C ⊆ (Set.univ : Set ℝ))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ (-(1 : ℝ)))) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ≥ 1)) → ((u (x, n)) = ((((-(1 : ℤ)) ^ n) /. ((2 * n) - 1)) * (((1 - x) /. (1 + x)) ^ n))))))))
  (h4 : Tendsto (fun n : ℕ => (|(((Real.rpow (-(1 : ℝ)) n) /. ((2 * n) - 1)))| /. |(((Real.rpow (-(1 : ℝ)) (n + 1)) /. ((2 * n) + 1)))|)) atTop (𝓝 1))
  (h5 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ (-(1 : ℝ)))) → ((|(((1 - x) /. (1 + x)))| < 1) ↔ (((1 - x) ^ (2 : ℕ)) < ((1 + x) ^ (2 : ℕ)))))))
  (h6 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((((1 - x) ^ (2 : ℕ)) < ((1 + x) ^ (2 : ℕ))) ↔ (x > 0)))))
  (h7 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((u (x, n)))‖ else 0)))))
  (h8 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x = 0)) → ((∑' n, if (1 : ℕ) ≤ n then (u (x, n)) else 0) = (∑' n, if (1 : ℕ) ≤ n then (((-(1 : ℤ)) ^ n) /. ((2 * n) - 1)) else 0)))))
  (h9 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x = 0)) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (u (x, n)) else 0) ∧ ¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((u (x, n)))‖ else 0)))))
  (h10 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (x < 0)) ∧ (x ≠ (-(1 : ℝ)))) → (Not (Tendsto (fun n : ℕ => (u (x, n))) atTop (𝓝 0))))))
  (h11 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (x < 0)) ∧ (x ≠ (-(1 : ℝ)))) → (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (u (x, n)) else 0)))))
  : ((A = ({x | (x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)})) ∧ (C = ({x | x = 0}))) → ((A = ({x | (x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ (-(1 : ℝ))) ∧ (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((u (x, n)))‖ else 0))})) ∧ (C = ({x | (x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ (-(1 : ℝ))) ∧ (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (u (x, n)) else 0) ∧ ¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((u (x, n)))‖ else 0))}))) := by
  sorry
