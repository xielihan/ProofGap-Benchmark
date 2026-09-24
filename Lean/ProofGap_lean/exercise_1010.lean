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

-- exercise: exercise_1010

theorem proof_gap_exercise_1010_1
  (f : (ℝ -> ℝ))
  (x_0 : ℝ)
  (a : ℝ)
  (b : ℝ)
  (h1 : x_0 ∈ (Set.univ : Set ℝ))
  (h2 : a ∈ (Set.univ : Set ℝ))
  (h3 : b ∈ (Set.univ : Set ℝ))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (if (x ≤ x_0) then (x ^ (2 : ℕ)) else (if (x > x_0) then ((a * x) + b) else ((a * x) + b)))))))
  : (f x_0) = (x_0 ^ (2 : ℕ)) := by
  sorry

theorem proof_gap_exercise_1010_2
  (f : (ℝ -> ℝ))
  (x_0 : ℝ)
  (a : ℝ)
  (b : ℝ)
  (h1 : x_0 ∈ (Set.univ : Set ℝ))
  (h2 : a ∈ (Set.univ : Set ℝ))
  (h3 : b ∈ (Set.univ : Set ℝ))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (if (x ≤ x_0) then (x ^ (2 : ℕ)) else (if (x > x_0) then ((a * x) + b) else ((a * x) + b)))))))
  (h5 : (f x_0) = (x_0 ^ (2 : ℕ)))
  : Tendsto (fun x : ℝ => (f x)) (𝓝[<] x_0) (𝓝 (x_0 ^ (2 : ℕ))) := by
  sorry

theorem proof_gap_exercise_1010_3
  (f : (ℝ -> ℝ))
  (x_0 : ℝ)
  (a : ℝ)
  (b : ℝ)
  (h1 : x_0 ∈ (Set.univ : Set ℝ))
  (h2 : a ∈ (Set.univ : Set ℝ))
  (h3 : b ∈ (Set.univ : Set ℝ))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (if (x ≤ x_0) then (x ^ (2 : ℕ)) else (if (x > x_0) then ((a * x) + b) else ((a * x) + b)))))))
  (h5 : (f x_0) = (x_0 ^ (2 : ℕ)))
  (h6 : Tendsto (fun x : ℝ => (f x)) (𝓝[<] x_0) (𝓝 (x_0 ^ (2 : ℕ))))
  : Tendsto (fun x : ℝ => (f x)) (𝓝[<] x_0) (𝓝 (f x_0)) := by
  sorry

theorem proof_gap_exercise_1010_4
  (f : (ℝ -> ℝ))
  (x_0 : ℝ)
  (a : ℝ)
  (b : ℝ)
  (h1 : x_0 ∈ (Set.univ : Set ℝ))
  (h2 : a ∈ (Set.univ : Set ℝ))
  (h3 : b ∈ (Set.univ : Set ℝ))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (if (x ≤ x_0) then (x ^ (2 : ℕ)) else (if (x > x_0) then ((a * x) + b) else ((a * x) + b)))))))
  (h5 : (f x_0) = (x_0 ^ (2 : ℕ)))
  (h6 : Tendsto (fun x : ℝ => (f x)) (𝓝[<] x_0) (𝓝 (x_0 ^ (2 : ℕ))))
  (h7 : Tendsto (fun x : ℝ => (f x)) (𝓝[<] x_0) (𝓝 (f x_0)))
  : Tendsto (fun x : ℝ => (f x)) (𝓝[>] x_0) (𝓝 ((a * x_0) + b)) := by
  sorry

theorem proof_gap_exercise_1010_5
  (f : (ℝ -> ℝ))
  (x_0 : ℝ)
  (a : ℝ)
  (b : ℝ)
  (h1 : x_0 ∈ (Set.univ : Set ℝ))
  (h2 : a ∈ (Set.univ : Set ℝ))
  (h3 : b ∈ (Set.univ : Set ℝ))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (if (x ≤ x_0) then (x ^ (2 : ℕ)) else (if (x > x_0) then ((a * x) + b) else ((a * x) + b)))))))
  (h5 : (f x_0) = (x_0 ^ (2 : ℕ)))
  (h6 : Tendsto (fun x : ℝ => (f x)) (𝓝[<] x_0) (𝓝 (x_0 ^ (2 : ℕ))))
  (h7 : Tendsto (fun x : ℝ => (f x)) (𝓝[<] x_0) (𝓝 (f x_0)))
  (h8 : Tendsto (fun x : ℝ => (f x)) (𝓝[>] x_0) (𝓝 ((a * x_0) + b)))
  : ((x_0 ^ (2 : ℕ)) = ((a * x_0) + b)) → (ContinuousAt f x_0) := by
  sorry

theorem proof_gap_exercise_1010_6
  (f : (ℝ -> ℝ))
  (x_0 : ℝ)
  (a : ℝ)
  (b : ℝ)
  (h1 : x_0 ∈ (Set.univ : Set ℝ))
  (h2 : a ∈ (Set.univ : Set ℝ))
  (h3 : b ∈ (Set.univ : Set ℝ))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (if (x ≤ x_0) then (x ^ (2 : ℕ)) else (if (x > x_0) then ((a * x) + b) else ((a * x) + b)))))))
  (h5 : (f x_0) = (x_0 ^ (2 : ℕ)))
  (h6 : Tendsto (fun x : ℝ => (f x)) (𝓝[<] x_0) (𝓝 (x_0 ^ (2 : ℕ))))
  (h7 : Tendsto (fun x : ℝ => (f x)) (𝓝[<] x_0) (𝓝 (f x_0)))
  (h8 : Tendsto (fun x : ℝ => (f x)) (𝓝[>] x_0) (𝓝 ((a * x_0) + b)))
  (h9 : ((x_0 ^ (2 : ℕ)) = ((a * x_0) + b)) → (ContinuousAt f x_0))
  : (iteratedDeriv 1 (fun t => f t) x_0) = (2 * x_0) := by
  sorry

theorem proof_gap_exercise_1010_7
  (f : (ℝ -> ℝ))
  (x_0 : ℝ)
  (a : ℝ)
  (b : ℝ)
  (h1 : x_0 ∈ (Set.univ : Set ℝ))
  (h2 : a ∈ (Set.univ : Set ℝ))
  (h3 : b ∈ (Set.univ : Set ℝ))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (if (x ≤ x_0) then (x ^ (2 : ℕ)) else (if (x > x_0) then ((a * x) + b) else ((a * x) + b)))))))
  (h5 : (f x_0) = (x_0 ^ (2 : ℕ)))
  (h6 : Tendsto (fun x : ℝ => (f x)) (𝓝[<] x_0) (𝓝 (x_0 ^ (2 : ℕ))))
  (h7 : Tendsto (fun x : ℝ => (f x)) (𝓝[<] x_0) (𝓝 (f x_0)))
  (h8 : Tendsto (fun x : ℝ => (f x)) (𝓝[>] x_0) (𝓝 ((a * x_0) + b)))
  (h9 : ((x_0 ^ (2 : ℕ)) = ((a * x_0) + b)) → (ContinuousAt f x_0))
  (h10 : (iteratedDeriv 1 (fun t => f t) x_0) = (2 * x_0))
  : (iteratedDeriv 1 (fun t => f t) x_0) = a := by
  sorry

theorem proof_gap_exercise_1010_8
  (f : (ℝ -> ℝ))
  (x_0 : ℝ)
  (a : ℝ)
  (b : ℝ)
  (h1 : x_0 ∈ (Set.univ : Set ℝ))
  (h2 : a ∈ (Set.univ : Set ℝ))
  (h3 : b ∈ (Set.univ : Set ℝ))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (if (x ≤ x_0) then (x ^ (2 : ℕ)) else (if (x > x_0) then ((a * x) + b) else ((a * x) + b)))))))
  (h5 : (f x_0) = (x_0 ^ (2 : ℕ)))
  (h6 : Tendsto (fun x : ℝ => (f x)) (𝓝[<] x_0) (𝓝 (x_0 ^ (2 : ℕ))))
  (h7 : Tendsto (fun x : ℝ => (f x)) (𝓝[<] x_0) (𝓝 (f x_0)))
  (h8 : Tendsto (fun x : ℝ => (f x)) (𝓝[>] x_0) (𝓝 ((a * x_0) + b)))
  (h9 : ((x_0 ^ (2 : ℕ)) = ((a * x_0) + b)) → (ContinuousAt f x_0))
  (h10 : (iteratedDeriv 1 (fun t => f t) x_0) = (2 * x_0))
  (h11 : (iteratedDeriv 1 (fun t => f t) x_0) = a)
  : (a = (2 * x_0)) → (DifferentiableAt ℝ f x_0) := by
  sorry

theorem proof_gap_exercise_1010_9
  (f : (ℝ -> ℝ))
  (x_0 : ℝ)
  (a : ℝ)
  (b : ℝ)
  (h1 : x_0 ∈ (Set.univ : Set ℝ))
  (h2 : a ∈ (Set.univ : Set ℝ))
  (h3 : b ∈ (Set.univ : Set ℝ))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (if (x ≤ x_0) then (x ^ (2 : ℕ)) else (if (x > x_0) then ((a * x) + b) else ((a * x) + b)))))))
  (h5 : (f x_0) = (x_0 ^ (2 : ℕ)))
  (h6 : Tendsto (fun x : ℝ => (f x)) (𝓝[<] x_0) (𝓝 (x_0 ^ (2 : ℕ))))
  (h7 : Tendsto (fun x : ℝ => (f x)) (𝓝[<] x_0) (𝓝 (f x_0)))
  (h8 : Tendsto (fun x : ℝ => (f x)) (𝓝[>] x_0) (𝓝 ((a * x_0) + b)))
  (h9 : ((x_0 ^ (2 : ℕ)) = ((a * x_0) + b)) → (ContinuousAt f x_0))
  (h10 : (iteratedDeriv 1 (fun t => f t) x_0) = (2 * x_0))
  (h11 : (iteratedDeriv 1 (fun t => f t) x_0) = a)
  (h12 : (a = (2 * x_0)) → (DifferentiableAt ℝ f x_0))
  : (x_0 ^ (2 : ℕ)) = ((2 * (x_0 ^ (2 : ℕ))) + b) := by
  sorry

theorem proof_gap_exercise_1010_10
  (f : (ℝ -> ℝ))
  (x_0 : ℝ)
  (a : ℝ)
  (b : ℝ)
  (h1 : x_0 ∈ (Set.univ : Set ℝ))
  (h2 : a ∈ (Set.univ : Set ℝ))
  (h3 : b ∈ (Set.univ : Set ℝ))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (if (x ≤ x_0) then (x ^ (2 : ℕ)) else (if (x > x_0) then ((a * x) + b) else ((a * x) + b)))))))
  (h5 : (f x_0) = (x_0 ^ (2 : ℕ)))
  (h6 : Tendsto (fun x : ℝ => (f x)) (𝓝[<] x_0) (𝓝 (x_0 ^ (2 : ℕ))))
  (h7 : Tendsto (fun x : ℝ => (f x)) (𝓝[<] x_0) (𝓝 (f x_0)))
  (h8 : Tendsto (fun x : ℝ => (f x)) (𝓝[>] x_0) (𝓝 ((a * x_0) + b)))
  (h9 : ((x_0 ^ (2 : ℕ)) = ((a * x_0) + b)) → (ContinuousAt f x_0))
  (h10 : (iteratedDeriv 1 (fun t => f t) x_0) = (2 * x_0))
  (h11 : (iteratedDeriv 1 (fun t => f t) x_0) = a)
  (h12 : (a = (2 * x_0)) → (DifferentiableAt ℝ f x_0))
  (h13 : (x_0 ^ (2 : ℕ)) = ((2 * (x_0 ^ (2 : ℕ))) + b))
  : b = (-(x_0 ^ (2 : ℕ))) := by
  sorry

theorem proof_gap_exercise_1010_11
  (f : (ℝ -> ℝ))
  (x_0 : ℝ)
  (a : ℝ)
  (b : ℝ)
  (h1 : x_0 ∈ (Set.univ : Set ℝ))
  (h2 : a ∈ (Set.univ : Set ℝ))
  (h3 : b ∈ (Set.univ : Set ℝ))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (if (x ≤ x_0) then (x ^ (2 : ℕ)) else (if (x > x_0) then ((a * x) + b) else ((a * x) + b)))))))
  (h5 : (f x_0) = (x_0 ^ (2 : ℕ)))
  (h6 : Tendsto (fun x : ℝ => (f x)) (𝓝[<] x_0) (𝓝 (x_0 ^ (2 : ℕ))))
  (h7 : Tendsto (fun x : ℝ => (f x)) (𝓝[<] x_0) (𝓝 (f x_0)))
  (h8 : Tendsto (fun x : ℝ => (f x)) (𝓝[>] x_0) (𝓝 ((a * x_0) + b)))
  (h9 : ((x_0 ^ (2 : ℕ)) = ((a * x_0) + b)) → (ContinuousAt f x_0))
  (h10 : (iteratedDeriv 1 (fun t => f t) x_0) = (2 * x_0))
  (h11 : (iteratedDeriv 1 (fun t => f t) x_0) = a)
  (h12 : (a = (2 * x_0)) → (DifferentiableAt ℝ f x_0))
  (h13 : (x_0 ^ (2 : ℕ)) = ((2 * (x_0 ^ (2 : ℕ))) + b))
  (h14 : b = (-(x_0 ^ (2 : ℕ))))
  : ((a, b) = ((2 * x_0), (-(x_0 ^ (2 : ℕ))))) → ((ContinuousAt f x_0) ∧ (DifferentiableAt ℝ f x_0)) := by
  sorry
