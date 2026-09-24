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

-- exercise: exercise_1313

theorem proof_gap_exercise_1313_1
  (f : (ℝ -> ℝ))
  (g : (ℝ -> ℝ))
  (h : (ℝ -> ℝ))
  (p : (ℝ -> ℝ))
  (n : ℝ)
  (h1 : n ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((f x) = (Real.rpow x n)))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((g x) = (Real.exp x)))))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((h x) = (x * (Real.log x))))))
  (h5 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((p x) = (Real.log x)))))
  : (n > 1) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((iteratedDeriv 2 (fun t => f t) x) = ((n * (n - 1)) * (Real.rpow x (n - 2)))))) := by
  sorry

theorem proof_gap_exercise_1313_2
  (f : (ℝ -> ℝ))
  (g : (ℝ -> ℝ))
  (h : (ℝ -> ℝ))
  (p : (ℝ -> ℝ))
  (n : ℝ)
  (h1 : n ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((f x) = (Real.rpow x n)))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((g x) = (Real.exp x)))))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((h x) = (x * (Real.log x))))))
  (h5 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((p x) = (Real.log x)))))
  (h6 : (n > 1) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((iteratedDeriv 2 (fun t => f t) x) = ((n * (n - 1)) * (Real.rpow x (n - 2)))))))
  : (n > 1) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((iteratedDeriv 2 (fun t => f t) x) > 0))) := by
  sorry

theorem proof_gap_exercise_1313_3
  (f : (ℝ -> ℝ))
  (g : (ℝ -> ℝ))
  (h : (ℝ -> ℝ))
  (p : (ℝ -> ℝ))
  (n : ℝ)
  (h1 : n ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((f x) = (Real.rpow x n)))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((g x) = (Real.exp x)))))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((h x) = (x * (Real.log x))))))
  (h5 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((p x) = (Real.log x)))))
  (h6 : (n > 1) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((iteratedDeriv 2 (fun t => f t) x) = ((n * (n - 1)) * (Real.rpow x (n - 2)))))))
  (h7 : (n > 1) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((iteratedDeriv 2 (fun t => f t) x) > 0))))
  : (n > 1) → (ConcaveOn ℝ (Set.Ioi 0) f) := by
  sorry

theorem proof_gap_exercise_1313_4
  (f : (ℝ -> ℝ))
  (g : (ℝ -> ℝ))
  (h : (ℝ -> ℝ))
  (p : (ℝ -> ℝ))
  (n : ℝ)
  (h1 : n ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((f x) = (Real.rpow x n)))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((g x) = (Real.exp x)))))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((h x) = (x * (Real.log x))))))
  (h5 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((p x) = (Real.log x)))))
  (h6 : (n > 1) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((iteratedDeriv 2 (fun t => f t) x) = ((n * (n - 1)) * (Real.rpow x (n - 2)))))))
  (h7 : (n > 1) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((iteratedDeriv 2 (fun t => f t) x) > 0))))
  (h8 : (n > 1) → (ConvexOn ℝ (Set.Ioi 0) f))
  : (0 < n) → ((n < 1) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((iteratedDeriv 2 (fun t => f t) x) = ((n * (n - 1)) * (Real.rpow x (n - 2))))))) := by
  sorry

theorem proof_gap_exercise_1313_5
  (f : (ℝ -> ℝ))
  (g : (ℝ -> ℝ))
  (h : (ℝ -> ℝ))
  (p : (ℝ -> ℝ))
  (n : ℝ)
  (h1 : n ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((f x) = (Real.rpow x n)))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((g x) = (Real.exp x)))))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((h x) = (x * (Real.log x))))))
  (h5 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((p x) = (Real.log x)))))
  (h6 : (n > 1) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((iteratedDeriv 2 (fun t => f t) x) = ((n * (n - 1)) * (Real.rpow x (n - 2)))))))
  (h7 : (n > 1) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((iteratedDeriv 2 (fun t => f t) x) > 0))))
  (h8 : (n > 1) → (ConvexOn ℝ (Set.Ioi 0) f))
  (h9 : (0 < n) → ((n < 1) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((iteratedDeriv 2 (fun t => f t) x) = ((n * (n - 1)) * (Real.rpow x (n - 2))))))))
  : (0 < n) → ((n < 1) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((iteratedDeriv 2 (fun t => f t) x) < 0)))) := by
  sorry

theorem proof_gap_exercise_1313_6
  (f : (ℝ -> ℝ))
  (g : (ℝ -> ℝ))
  (h : (ℝ -> ℝ))
  (p : (ℝ -> ℝ))
  (n : ℝ)
  (h1 : n ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((f x) = (Real.rpow x n)))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((g x) = (Real.exp x)))))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((h x) = (x * (Real.log x))))))
  (h5 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((p x) = (Real.log x)))))
  (h6 : (n > 1) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((iteratedDeriv 2 (fun t => f t) x) = ((n * (n - 1)) * (Real.rpow x (n - 2)))))))
  (h7 : (n > 1) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((iteratedDeriv 2 (fun t => f t) x) > 0))))
  (h8 : (n > 1) → (ConcaveOn ℝ (Set.Ioi 0) f))
  (h9 : (0 < n) → ((n < 1) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((iteratedDeriv 2 (fun t => f t) x) = ((n * (n - 1)) * (Real.rpow x (n - 2))))))))
  (h10 : (0 < n) → ((n < 1) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((iteratedDeriv 2 (fun t => f t) x) < 0)))))
  : (0 < n) → ((n < 1) → (ConvexOn ℝ (Set.Ioi 0) f)) := by
  sorry

theorem proof_gap_exercise_1313_7
  (f : (ℝ -> ℝ))
  (g : (ℝ -> ℝ))
  (h : (ℝ -> ℝ))
  (p : (ℝ -> ℝ))
  (n : ℝ)
  (h1 : n ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((f x) = (Real.rpow x n)))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((g x) = (Real.exp x)))))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((h x) = (x * (Real.log x))))))
  (h5 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((p x) = (Real.log x)))))
  (h6 : (n > 1) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((iteratedDeriv 2 (fun t => f t) x) = ((n * (n - 1)) * (Real.rpow x (n - 2)))))))
  (h7 : (n > 1) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((iteratedDeriv 2 (fun t => f t) x) > 0))))
  (h8 : (n > 1) → (ConcaveOn ℝ (Set.Ioi 0) f))
  (h9 : (0 < n) → ((n < 1) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((iteratedDeriv 2 (fun t => f t) x) = ((n * (n - 1)) * (Real.rpow x (n - 2))))))))
  (h10 : (0 < n) → ((n < 1) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((iteratedDeriv 2 (fun t => f t) x) < 0)))))
  (h11 : (0 < n) → ((n < 1) → (ConvexOn ℝ (Set.Ioi 0) f)))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 2 (fun t => g t) x) = (Real.exp x)))) := by
  sorry

theorem proof_gap_exercise_1313_8
  (f : (ℝ -> ℝ))
  (g : (ℝ -> ℝ))
  (h : (ℝ -> ℝ))
  (p : (ℝ -> ℝ))
  (n : ℝ)
  (h1 : n ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((f x) = (Real.rpow x n)))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((g x) = (Real.exp x)))))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((h x) = (x * (Real.log x))))))
  (h5 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((p x) = (Real.log x)))))
  (h6 : (n > 1) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((iteratedDeriv 2 (fun t => f t) x) = ((n * (n - 1)) * (Real.rpow x (n - 2)))))))
  (h7 : (n > 1) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((iteratedDeriv 2 (fun t => f t) x) > 0))))
  (h8 : (n > 1) → (ConcaveOn ℝ (Set.Ioi 0) f))
  (h9 : (0 < n) → ((n < 1) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((iteratedDeriv 2 (fun t => f t) x) = ((n * (n - 1)) * (Real.rpow x (n - 2))))))))
  (h10 : (0 < n) → ((n < 1) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((iteratedDeriv 2 (fun t => f t) x) < 0)))))
  (h11 : (0 < n) → ((n < 1) → (ConvexOn ℝ (Set.Ioi 0) f)))
  (h12 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 2 (fun t => g t) x) = (Real.exp x)))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((iteratedDeriv 2 (fun t => g t) x) > 0))) := by
  sorry

theorem proof_gap_exercise_1313_9
  (f : (ℝ -> ℝ))
  (g : (ℝ -> ℝ))
  (h : (ℝ -> ℝ))
  (p : (ℝ -> ℝ))
  (n : ℝ)
  (h1 : n ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((f x) = (Real.rpow x n)))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((g x) = (Real.exp x)))))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((h x) = (x * (Real.log x))))))
  (h5 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((p x) = (Real.log x)))))
  (h6 : (n > 1) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((iteratedDeriv 2 (fun t => f t) x) = ((n * (n - 1)) * (Real.rpow x (n - 2)))))))
  (h7 : (n > 1) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((iteratedDeriv 2 (fun t => f t) x) > 0))))
  (h8 : (n > 1) → (ConcaveOn ℝ (Set.Ioi 0) f))
  (h9 : (0 < n) → ((n < 1) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((iteratedDeriv 2 (fun t => f t) x) = ((n * (n - 1)) * (Real.rpow x (n - 2))))))))
  (h10 : (0 < n) → ((n < 1) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((iteratedDeriv 2 (fun t => f t) x) < 0)))))
  (h11 : (0 < n) → ((n < 1) → (ConvexOn ℝ (Set.Ioi 0) f)))
  (h12 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 2 (fun t => g t) x) = (Real.exp x)))))
  (h13 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((iteratedDeriv 2 (fun t => g t) x) > 0))))
  : ConcaveOn ℝ (Set.Ioi 0) g := by
  sorry

theorem proof_gap_exercise_1313_10
  (f : (ℝ -> ℝ))
  (g : (ℝ -> ℝ))
  (h : (ℝ -> ℝ))
  (p : (ℝ -> ℝ))
  (n : ℝ)
  (h1 : n ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((f x) = (Real.rpow x n)))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((g x) = (Real.exp x)))))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((h x) = (x * (Real.log x))))))
  (h5 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((p x) = (Real.log x)))))
  (h6 : (n > 1) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((iteratedDeriv 2 (fun t => f t) x) = ((n * (n - 1)) * (Real.rpow x (n - 2)))))))
  (h7 : (n > 1) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((iteratedDeriv 2 (fun t => f t) x) > 0))))
  (h8 : (n > 1) → (ConvexOn ℝ (Set.Ioi 0) f))
  (h9 : (0 < n) → ((n < 1) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((iteratedDeriv 2 (fun t => f t) x) = ((n * (n - 1)) * (Real.rpow x (n - 2))))))))
  (h10 : (0 < n) → ((n < 1) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((iteratedDeriv 2 (fun t => f t) x) < 0)))))
  (h11 : (0 < n) → ((n < 1) → (ConcaveOn ℝ (Set.Ioi 0) f)))
  (h12 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 2 (fun t => g t) x) = (Real.exp x)))))
  (h13 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((iteratedDeriv 2 (fun t => g t) x) > 0))))
  (h14 : ConvexOn ℝ (Set.Ioi 0) g)
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((iteratedDeriv 2 (fun t => h t) x) = (1 /. x)))) := by
  sorry

theorem proof_gap_exercise_1313_11
  (f : (ℝ -> ℝ))
  (g : (ℝ -> ℝ))
  (h : (ℝ -> ℝ))
  (p : (ℝ -> ℝ))
  (n : ℝ)
  (h1 : n ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((f x) = (Real.rpow x n)))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((g x) = (Real.exp x)))))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((h x) = (x * (Real.log x))))))
  (h5 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((p x) = (Real.log x)))))
  (h6 : (n > 1) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((iteratedDeriv 2 (fun t => f t) x) = ((n * (n - 1)) * (Real.rpow x (n - 2)))))))
  (h7 : (n > 1) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((iteratedDeriv 2 (fun t => f t) x) > 0))))
  (h8 : (n > 1) → (ConcaveOn ℝ (Set.Ioi 0) f))
  (h9 : (0 < n) → ((n < 1) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((iteratedDeriv 2 (fun t => f t) x) = ((n * (n - 1)) * (Real.rpow x (n - 2))))))))
  (h10 : (0 < n) → ((n < 1) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((iteratedDeriv 2 (fun t => f t) x) < 0)))))
  (h11 : (0 < n) → ((n < 1) → (ConvexOn ℝ (Set.Ioi 0) f)))
  (h12 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 2 (fun t => g t) x) = (Real.exp x)))))
  (h13 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((iteratedDeriv 2 (fun t => g t) x) > 0))))
  (h14 : ConcaveOn ℝ (Set.Ioi 0) g)
  (h15 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((iteratedDeriv 2 (fun t => h t) x) = (1 /. x)))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((iteratedDeriv 2 (fun t => h t) x) > 0))) := by
  sorry

theorem proof_gap_exercise_1313_12
  (f : (ℝ -> ℝ))
  (g : (ℝ -> ℝ))
  (h : (ℝ -> ℝ))
  (p : (ℝ -> ℝ))
  (n : ℝ)
  (h1 : n ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((f x) = (Real.rpow x n)))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((g x) = (Real.exp x)))))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((h x) = (x * (Real.log x))))))
  (h5 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((p x) = (Real.log x)))))
  (h6 : (n > 1) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((iteratedDeriv 2 (fun t => f t) x) = ((n * (n - 1)) * (Real.rpow x (n - 2)))))))
  (h7 : (n > 1) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((iteratedDeriv 2 (fun t => f t) x) > 0))))
  (h8 : (n > 1) → (ConcaveOn ℝ (Set.Ioi 0) f))
  (h9 : (0 < n) → ((n < 1) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((iteratedDeriv 2 (fun t => f t) x) = ((n * (n - 1)) * (Real.rpow x (n - 2))))))))
  (h10 : (0 < n) → ((n < 1) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((iteratedDeriv 2 (fun t => f t) x) < 0)))))
  (h11 : (0 < n) → ((n < 1) → (ConvexOn ℝ (Set.Ioi 0) f)))
  (h12 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 2 (fun t => g t) x) = (Real.exp x)))))
  (h13 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((iteratedDeriv 2 (fun t => g t) x) > 0))))
  (h14 : ConcaveOn ℝ (Set.Ioi 0) g)
  (h15 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((iteratedDeriv 2 (fun t => h t) x) = (1 /. x)))))
  (h16 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((iteratedDeriv 2 (fun t => h t) x) > 0))))
  : ConcaveOn ℝ (Set.Ioi 0) h := by
  sorry

theorem proof_gap_exercise_1313_13
  (f : (ℝ -> ℝ))
  (g : (ℝ -> ℝ))
  (h : (ℝ -> ℝ))
  (p : (ℝ -> ℝ))
  (n : ℝ)
  (h1 : n ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((f x) = (Real.rpow x n)))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((g x) = (Real.exp x)))))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((h x) = (x * (Real.log x))))))
  (h5 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((p x) = (Real.log x)))))
  (h6 : (n > 1) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((iteratedDeriv 2 (fun t => f t) x) = ((n * (n - 1)) * (Real.rpow x (n - 2)))))))
  (h7 : (n > 1) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((iteratedDeriv 2 (fun t => f t) x) > 0))))
  (h8 : (n > 1) → (ConcaveOn ℝ (Set.Ioi 0) f))
  (h9 : (0 < n) → ((n < 1) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((iteratedDeriv 2 (fun t => f t) x) = ((n * (n - 1)) * (Real.rpow x (n - 2))))))))
  (h10 : (0 < n) → ((n < 1) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((iteratedDeriv 2 (fun t => f t) x) < 0)))))
  (h11 : (0 < n) → ((n < 1) → (ConvexOn ℝ (Set.Ioi 0) f)))
  (h12 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 2 (fun t => g t) x) = (Real.exp x)))))
  (h13 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((iteratedDeriv 2 (fun t => g t) x) > 0))))
  (h14 : ConcaveOn ℝ (Set.Ioi 0) g)
  (h15 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((iteratedDeriv 2 (fun t => h t) x) = (1 /. x)))))
  (h16 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((iteratedDeriv 2 (fun t => h t) x) > 0))))
  (h17 : ConcaveOn ℝ (Set.Ioi 0) h)
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((iteratedDeriv 2 (fun t => p t) x) = (-(1 /. (x ^ (2 : ℕ))))))) := by
  sorry

theorem proof_gap_exercise_1313_14
  (f : (ℝ -> ℝ))
  (g : (ℝ -> ℝ))
  (h : (ℝ -> ℝ))
  (p : (ℝ -> ℝ))
  (n : ℝ)
  (h1 : n ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((f x) = (Real.rpow x n)))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((g x) = (Real.exp x)))))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((h x) = (x * (Real.log x))))))
  (h5 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((p x) = (Real.log x)))))
  (h6 : (n > 1) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((iteratedDeriv 2 (fun t => f t) x) = ((n * (n - 1)) * (Real.rpow x (n - 2)))))))
  (h7 : (n > 1) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((iteratedDeriv 2 (fun t => f t) x) > 0))))
  (h8 : (n > 1) → (ConcaveOn ℝ (Set.Ioi 0) f))
  (h9 : (0 < n) → ((n < 1) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((iteratedDeriv 2 (fun t => f t) x) = ((n * (n - 1)) * (Real.rpow x (n - 2))))))))
  (h10 : (0 < n) → ((n < 1) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((iteratedDeriv 2 (fun t => f t) x) < 0)))))
  (h11 : (0 < n) → ((n < 1) → (ConvexOn ℝ (Set.Ioi 0) f)))
  (h12 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 2 (fun t => g t) x) = (Real.exp x)))))
  (h13 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((iteratedDeriv 2 (fun t => g t) x) > 0))))
  (h14 : ConcaveOn ℝ (Set.Ioi 0) g)
  (h15 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((iteratedDeriv 2 (fun t => h t) x) = (1 /. x)))))
  (h16 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((iteratedDeriv 2 (fun t => h t) x) > 0))))
  (h17 : ConcaveOn ℝ (Set.Ioi 0) h)
  (h18 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((iteratedDeriv 2 (fun t => p t) x) = (-(1 /. (x ^ (2 : ℕ))))))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((iteratedDeriv 2 (fun t => p t) x) < 0))) := by
  sorry

theorem proof_gap_exercise_1313_15
  (f : (ℝ -> ℝ))
  (g : (ℝ -> ℝ))
  (h : (ℝ -> ℝ))
  (p : (ℝ -> ℝ))
  (n : ℝ)
  (h1 : n ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((f x) = (Real.rpow x n)))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((g x) = (Real.exp x)))))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((h x) = (x * (Real.log x))))))
  (h5 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((p x) = (Real.log x)))))
  (h6 : (n > 1) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((iteratedDeriv 2 (fun t => f t) x) = ((n * (n - 1)) * (Real.rpow x (n - 2)))))))
  (h7 : (n > 1) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((iteratedDeriv 2 (fun t => f t) x) > 0))))
  (h8 : (n > 1) → (ConcaveOn ℝ (Set.Ioi 0) f))
  (h9 : (0 < n) → ((n < 1) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((iteratedDeriv 2 (fun t => f t) x) = ((n * (n - 1)) * (Real.rpow x (n - 2))))))))
  (h10 : (0 < n) → ((n < 1) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((iteratedDeriv 2 (fun t => f t) x) < 0)))))
  (h11 : (0 < n) → ((n < 1) → (ConvexOn ℝ (Set.Ioi 0) f)))
  (h12 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 2 (fun t => g t) x) = (Real.exp x)))))
  (h13 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((iteratedDeriv 2 (fun t => g t) x) > 0))))
  (h14 : ConcaveOn ℝ (Set.Ioi 0) g)
  (h15 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((iteratedDeriv 2 (fun t => h t) x) = (1 /. x)))))
  (h16 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((iteratedDeriv 2 (fun t => h t) x) > 0))))
  (h17 : ConcaveOn ℝ (Set.Ioi 0) h)
  (h18 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((iteratedDeriv 2 (fun t => p t) x) = (-(1 /. (x ^ (2 : ℕ))))))))
  (h19 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((iteratedDeriv 2 (fun t => p t) x) < 0))))
  : ConvexOn ℝ (Set.Ioi 0) p := by
  sorry

theorem proof_gap_exercise_1313_16
  (f : (ℝ -> ℝ))
  (g : (ℝ -> ℝ))
  (h : (ℝ -> ℝ))
  (p : (ℝ -> ℝ))
  (n : ℝ)
  (h1 : n ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((f x) = (Real.rpow x n)))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((g x) = (Real.exp x)))))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((h x) = (x * (Real.log x))))))
  (h5 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((p x) = (Real.log x)))))
  (h6 : (n > 1) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((iteratedDeriv 2 (fun t => f t) x) = ((n * (n - 1)) * (Real.rpow x (n - 2)))))))
  (h7 : (n > 1) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((iteratedDeriv 2 (fun t => f t) x) > 0))))
  (h8 : (n > 1) → (ConcaveOn ℝ (Set.Ioi 0) f))
  (h9 : (0 < n) → ((n < 1) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((iteratedDeriv 2 (fun t => f t) x) = ((n * (n - 1)) * (Real.rpow x (n - 2))))))))
  (h10 : (0 < n) → ((n < 1) → (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((iteratedDeriv 2 (fun t => f t) x) < 0)))))
  (h11 : (0 < n) → ((n < 1) → (ConvexOn ℝ (Set.Ioi 0) f)))
  (h12 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 2 (fun t => g t) x) = (Real.exp x)))))
  (h13 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((iteratedDeriv 2 (fun t => g t) x) > 0))))
  (h14 : ConcaveOn ℝ (Set.Ioi 0) g)
  (h15 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((iteratedDeriv 2 (fun t => h t) x) = (1 /. x)))))
  (h16 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((iteratedDeriv 2 (fun t => h t) x) > 0))))
  (h17 : ConcaveOn ℝ (Set.Ioi 0) h)
  (h18 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((iteratedDeriv 2 (fun t => p t) x) = (-(1 /. (x ^ (2 : ℕ))))))))
  (h19 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((iteratedDeriv 2 (fun t => p t) x) < 0))))
  (h20 : ConvexOn ℝ (Set.Ioi 0) p)
  : (((((n > 1) → (ConcaveOn ℝ (Set.Ioi 0) f)) ∧ (ConcaveOn ℝ (Set.Ioi 0) g)) ∧ (ConcaveOn ℝ (Set.Ioi 0) h)) ∧ (((0 < n) ∧ (n < 1)) → (ConvexOn ℝ (Set.Ioi 0) f))) ∧ (ConvexOn ℝ (Set.Ioi 0) p) := by
  sorry
