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

-- exercise: exercise_2600

theorem proof_gap_exercise_2600_1
  (u : (ℕ -> ℝ))
  (p : ℝ)
  (h1 : p ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((u n) = (((n)! * (Real.exp (n : ℝ))) /. (Real.rpow (n : ℝ) (n + p)))))))
  : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((((u n) /. (u (n + 1))) = ((((n)! * (Real.exp (n : ℝ))) /. (Real.rpow (n : ℝ) (n + p))) /. ((((n + 1))! * (Real.exp (n + 1))) /. (Real.rpow (n + 1) ((n + 1) + p))))) ∧ (((((n)! * (Real.exp (n : ℝ))) /. (Real.rpow (n : ℝ) (n + p))) /. ((((n + 1))! * (Real.exp (n + 1))) /. (Real.rpow (n + 1) ((n + 1) + p)))) = ((1 /. (Real.exp 1)) * (Real.rpow ((n + 1) /. n) (n + p))))))) := by
  sorry

theorem proof_gap_exercise_2600_2
  (u : (ℕ -> ℝ))
  (p : ℝ)
  (h1 : p ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((u n) = (((n)! * (Real.exp (n : ℝ))) /. (Real.rpow (n : ℝ) (n + p)))))))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((((u n) /. (u (n + 1))) = ((((n)! * (Real.exp (n : ℝ))) /. (Real.rpow (n : ℝ) (n + p))) /. ((((n + 1))! * (Real.exp (n + 1))) /. (Real.rpow (n + 1) ((n + 1) + p))))) ∧ (((((n)! * (Real.exp (n : ℝ))) /. (Real.rpow (n : ℝ) (n + p))) /. ((((n + 1))! * (Real.exp (n + 1))) /. (Real.rpow (n + 1) ((n + 1) + p)))) = ((1 /. (Real.exp 1)) * (Real.rpow ((n + 1) /. n) (n + p))))))))
  : (∃ L : ℝ, Tendsto (fun n : ℕ => ((((1 /. (Real.exp 1)) * (Real.rpow ((n + 1) /. n) (n + p))) - 1) /. (1 /. n))) atTop (𝓝 L) ∧ (Tendsto (fun n : ℕ => (n * (((u n) /. (u (n + 1))) - 1))) atTop (𝓝 (atTop.limUnder (fun n : ℕ => ((((1 /. (Real.exp 1)) * (Real.rpow ((n + 1) /. n) (n + p))) - 1) /. (1 /. n))))))) := by
  sorry

theorem proof_gap_exercise_2600_3
  (u : (ℕ -> ℝ))
  (p : ℝ)
  (h1 : p ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((u n) = (((n)! * (Real.exp (n : ℝ))) /. (Real.rpow (n : ℝ) (n + p)))))))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((((u n) /. (u (n + 1))) = ((((n)! * (Real.exp (n : ℝ))) /. (Real.rpow (n : ℝ) (n + p))) /. ((((n + 1))! * (Real.exp (n + 1))) /. (Real.rpow (n + 1) ((n + 1) + p))))) ∧ (((((n)! * (Real.exp (n : ℝ))) /. (Real.rpow (n : ℝ) (n + p))) /. ((((n + 1))! * (Real.exp (n + 1))) /. (Real.rpow (n + 1) ((n + 1) + p)))) = ((1 /. (Real.exp 1)) * (Real.rpow ((n + 1) /. n) (n + p))))))))
  (h4 : Tendsto (fun n : ℕ => (n * (((u n) /. (u (n + 1))) - 1))) atTop (𝓝 (atTop.limUnder (fun n : ℕ => ((((1 /. (Real.exp 1)) * (Real.rpow ((n + 1) /. n) (n + p))) - 1) /. (1 /. n))))))
  (h5 : ∃ L : ℝ, Tendsto (fun n : ℕ => ((((1 /. (Real.exp 1)) * (Real.rpow ((n + 1) /. n) (n + p))) - 1) /. (1 /. n))) atTop (𝓝 L))
  : Tendsto (fun n : ℕ => ((((1 /. (Real.exp 1)) * (Real.rpow ((n + 1) /. n) (n + p))) - 1) /. (1 /. n))) atTop (𝓝 (p - (1 /. 2))) := by
  sorry

theorem proof_gap_exercise_2600_4
  (u : (ℕ -> ℝ))
  (p : ℝ)
  (h1 : p ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((u n) = (((n)! * (Real.exp (n : ℝ))) /. (Real.rpow (n : ℝ) (n + p)))))))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((((u n) /. (u (n + 1))) = ((((n)! * (Real.exp (n : ℝ))) /. (Real.rpow (n : ℝ) (n + p))) /. ((((n + 1))! * (Real.exp (n + 1))) /. (Real.rpow (n + 1) ((n + 1) + p))))) ∧ (((((n)! * (Real.exp (n : ℝ))) /. (Real.rpow (n : ℝ) (n + p))) /. ((((n + 1))! * (Real.exp (n + 1))) /. (Real.rpow (n + 1) ((n + 1) + p)))) = ((1 /. (Real.exp 1)) * (Real.rpow ((n + 1) /. n) (n + p))))))))
  (h4 : Tendsto (fun n : ℕ => (n * (((u n) /. (u (n + 1))) - 1))) atTop (𝓝 (atTop.limUnder (fun n : ℕ => ((((1 /. (Real.exp 1)) * (Real.rpow ((n + 1) /. n) (n + p))) - 1) /. (1 /. n))))))
  (h5 : Tendsto (fun n : ℕ => ((((1 /. (Real.exp 1)) * (Real.rpow ((n + 1) /. n) (n + p))) - 1) /. (1 /. n))) atTop (𝓝 (p - (1 /. 2))))
  (h6 : ∃ L : ℝ, Tendsto (fun n : ℕ => ((((1 /. (Real.exp 1)) * (Real.rpow ((n + 1) /. n) (n + p))) - 1) /. (1 /. n))) atTop (𝓝 L))
  : Tendsto (fun n : ℕ => (n * (((u n) /. (u (n + 1))) - 1))) atTop (𝓝 (p - (1 /. 2))) := by
  sorry

theorem proof_gap_exercise_2600_5
  (u : (ℕ -> ℝ))
  (p : ℝ)
  (h1 : p ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((u n) = (((n)! * (Real.exp (n : ℝ))) /. (Real.rpow (n : ℝ) (n + p)))))))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((((u n) /. (u (n + 1))) = ((((n)! * (Real.exp (n : ℝ))) /. (Real.rpow (n : ℝ) (n + p))) /. ((((n + 1))! * (Real.exp (n + 1))) /. (Real.rpow (n + 1) ((n + 1) + p))))) ∧ (((((n)! * (Real.exp (n : ℝ))) /. (Real.rpow (n : ℝ) (n + p))) /. ((((n + 1))! * (Real.exp (n + 1))) /. (Real.rpow (n + 1) ((n + 1) + p)))) = ((1 /. (Real.exp 1)) * (Real.rpow ((n + 1) /. n) (n + p))))))))
  (h4 : Tendsto (fun n : ℕ => (n * (((u n) /. (u (n + 1))) - 1))) atTop (𝓝 (atTop.limUnder (fun n : ℕ => ((((1 /. (Real.exp 1)) * (Real.rpow ((n + 1) /. n) (n + p))) - 1) /. (1 /. n))))))
  (h5 : Tendsto (fun n : ℕ => ((((1 /. (Real.exp 1)) * (Real.rpow ((n + 1) /. n) (n + p))) - 1) /. (1 /. n))) atTop (𝓝 (p - (1 /. 2))))
  (h6 : Tendsto (fun n : ℕ => (n * (((u n) /. (u (n + 1))) - 1))) atTop (𝓝 (p - (1 /. 2))))
  (h7 : ∃ L : ℝ, Tendsto (fun n : ℕ => ((((1 /. (Real.exp 1)) * (Real.rpow ((n + 1) /. n) (n + p))) - 1) /. (1 /. n))) atTop (𝓝 L))
  : ((p - (1 /. 2)) > 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (u n) else 0)) := by
  sorry

theorem proof_gap_exercise_2600_6
  (u : (ℕ -> ℝ))
  (p : ℝ)
  (h1 : p ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((u n) = (((n)! * (Real.exp (n : ℝ))) /. (Real.rpow (n : ℝ) (n + p)))))))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((((u n) /. (u (n + 1))) = ((((n)! * (Real.exp (n : ℝ))) /. (Real.rpow (n : ℝ) (n + p))) /. ((((n + 1))! * (Real.exp (n + 1))) /. (Real.rpow (n + 1) ((n + 1) + p))))) ∧ (((((n)! * (Real.exp (n : ℝ))) /. (Real.rpow (n : ℝ) (n + p))) /. ((((n + 1))! * (Real.exp (n + 1))) /. (Real.rpow (n + 1) ((n + 1) + p)))) = ((1 /. (Real.exp 1)) * (Real.rpow ((n + 1) /. n) (n + p))))))))
  (h4 : Tendsto (fun n : ℕ => (n * (((u n) /. (u (n + 1))) - 1))) atTop (𝓝 (atTop.limUnder (fun n : ℕ => ((((1 /. (Real.exp 1)) * (Real.rpow ((n + 1) /. n) (n + p))) - 1) /. (1 /. n))))))
  (h5 : Tendsto (fun n : ℕ => ((((1 /. (Real.exp 1)) * (Real.rpow ((n + 1) /. n) (n + p))) - 1) /. (1 /. n))) atTop (𝓝 (p - (1 /. 2))))
  (h6 : Tendsto (fun n : ℕ => (n * (((u n) /. (u (n + 1))) - 1))) atTop (𝓝 (p - (1 /. 2))))
  (h7 : ((p - (1 /. 2)) > 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (u n) else 0)))
  (h8 : ∃ L : ℝ, Tendsto (fun n : ℕ => ((((1 /. (Real.exp 1)) * (Real.rpow ((n + 1) /. n) (n + p))) - 1) /. (1 /. n))) atTop (𝓝 L))
  : (p > (3 /. 2)) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (u n) else 0)) := by
  sorry

theorem proof_gap_exercise_2600_7
  (u : (ℕ -> ℝ))
  (p : ℝ)
  (h1 : p ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((u n) = (((n)! * (Real.exp (n : ℝ))) /. (Real.rpow (n : ℝ) (n + p)))))))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((((u n) /. (u (n + 1))) = ((((n)! * (Real.exp (n : ℝ))) /. (Real.rpow (n : ℝ) (n + p))) /. ((((n + 1))! * (Real.exp (n + 1))) /. (Real.rpow (n + 1) ((n + 1) + p))))) ∧ (((((n)! * (Real.exp (n : ℝ))) /. (Real.rpow (n : ℝ) (n + p))) /. ((((n + 1))! * (Real.exp (n + 1))) /. (Real.rpow (n + 1) ((n + 1) + p)))) = ((1 /. (Real.exp 1)) * (Real.rpow ((n + 1) /. n) (n + p))))))))
  (h4 : Tendsto (fun n : ℕ => (n * (((u n) /. (u (n + 1))) - 1))) atTop (𝓝 (atTop.limUnder (fun n : ℕ => ((((1 /. (Real.exp 1)) * (Real.rpow ((n + 1) /. n) (n + p))) - 1) /. (1 /. n))))))
  (h5 : Tendsto (fun n : ℕ => ((((1 /. (Real.exp 1)) * (Real.rpow ((n + 1) /. n) (n + p))) - 1) /. (1 /. n))) atTop (𝓝 (p - (1 /. 2))))
  (h6 : Tendsto (fun n : ℕ => (n * (((u n) /. (u (n + 1))) - 1))) atTop (𝓝 (p - (1 /. 2))))
  (h7 : ((p - (1 /. 2)) > 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (u n) else 0)))
  (h8 : (p > (3 /. 2)) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (u n) else 0)))
  (h9 : ∃ L : ℝ, Tendsto (fun n : ℕ => ((((1 /. (Real.exp 1)) * (Real.rpow ((n + 1) /. n) (n + p))) - 1) /. (1 /. n))) atTop (𝓝 L))
  : (p > (3 /. 2)) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (u n) else 0)) := by
  sorry
