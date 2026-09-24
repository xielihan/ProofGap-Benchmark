import Mathlib

attribute [local instance] Classical.propDecidable

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

-- exercise: exercise_71

theorem proof_gap_exercise_71_1
  (p : (ℕ -> ℝ))
  (q : (ℕ -> ℝ))
  (n : ℕ)
  (h1 : True)
  (h2 : True)
  (h3 : n ∈ (Set.univ : Set ℕ))
  (h4 : Tendsto (fun n_1 : ℕ => (((p n_1) : ℝ) : EReal)) atTop (𝓝 ⊤))
  (h5 : Tendsto (fun n_1 : ℕ => (((q n_1) : ℝ) : EReal)) atTop (𝓝 ⊥))
  (h6 : (forall (n_1 : ℕ), (((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) → (((p n_1) ∉ (Set.Icc (-(1 : ℝ)) 0)) ∧ ((q n_1) ∉ (Set.Icc (-(1 : ℝ)) 0))))))
  (h7 : (forall (n_1 : ℕ), (((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2})))) → (((k : ℕ → _) n_1) = ⌊(p n_1)⌋)))
  : Tendsto (fun n_1 : ℕ => (((k n_1) : ℝ) : EReal)) atTop (𝓝 ⊤) := by
  sorry

theorem proof_gap_exercise_71_2
  (p : (ℕ -> ℝ))
  (q : (ℕ -> ℝ))
  (n : ℕ)
  (h1 : True)
  (h2 : True)
  (h3 : n ∈ (Set.univ : Set ℕ))
  (h4 : Tendsto (fun n_1 : ℕ => (((p n_1) : ℝ) : EReal)) atTop (𝓝 ⊤))
  (h5 : Tendsto (fun n_1 : ℕ => (((q n_1) : ℝ) : EReal)) atTop (𝓝 ⊥))
  (h6 : (forall (n_1 : ℕ), (((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) → (((p n_1) ∉ (Set.Icc (-(1 : ℝ)) 0)) ∧ ((q n_1) ∉ (Set.Icc (-(1 : ℝ)) 0))))))
  (h7 : (forall (n_1 : ℕ), (((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2})))) → (((k : ℕ → _) n_1) = ⌊(p n_1)⌋)))
  (h8 : Tendsto (fun n_1 : ℕ => (((k n_1) : ℝ) : EReal)) atTop (𝓝 ⊤))
  : (forall (n_1 : ℕ), (((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) → ((k n_1) ≤ (p n_1)))) := by
  sorry

theorem proof_gap_exercise_71_3
  (p : (ℕ -> ℝ))
  (q : (ℕ -> ℝ))
  (n : ℕ)
  (h1 : True)
  (h2 : True)
  (h3 : n ∈ (Set.univ : Set ℕ))
  (h4 : Tendsto (fun n_1 : ℕ => (((p n_1) : ℝ) : EReal)) atTop (𝓝 ⊤))
  (h5 : Tendsto (fun n_1 : ℕ => (((q n_1) : ℝ) : EReal)) atTop (𝓝 ⊥))
  (h6 : (forall (n_1 : ℕ), (((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) → (((p n_1) ∉ (Set.Icc (-(1 : ℝ)) 0)) ∧ ((q n_1) ∉ (Set.Icc (-(1 : ℝ)) 0))))))
  (h7 : (forall (n_1 : ℕ), (((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2})))) → (((k : ℕ → _) n_1) = ⌊(p n_1)⌋)))
  (h8 : Tendsto (fun n_1 : ℕ => (((k n_1) : ℝ) : EReal)) atTop (𝓝 ⊤))
  (h9 : (forall (n_1 : ℕ), (((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) → ((k n_1) ≤ (p n_1)))))
  : (forall (n_1 : ℕ), (((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) → ((p n_1) < ((k n_1) + 1)))) := by
  sorry

theorem proof_gap_exercise_71_4
  (p : (ℕ -> ℝ))
  (q : (ℕ -> ℝ))
  (n : ℕ)
  (h1 : True)
  (h2 : True)
  (h3 : n ∈ (Set.univ : Set ℕ))
  (h4 : Tendsto (fun n_1 : ℕ => (((p n_1) : ℝ) : EReal)) atTop (𝓝 ⊤))
  (h5 : Tendsto (fun n_1 : ℕ => (((q n_1) : ℝ) : EReal)) atTop (𝓝 ⊥))
  (h6 : (forall (n_1 : ℕ), (((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) → (((p n_1) ∉ (Set.Icc (-(1 : ℝ)) 0)) ∧ ((q n_1) ∉ (Set.Icc (-(1 : ℝ)) 0))))))
  (h7 : (forall (n_1 : ℕ), (((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2})))) → (((k : ℕ → _) n_1) = ⌊(p n_1)⌋)))
  (h8 : Tendsto (fun n_1 : ℕ => (((k n_1) : ℝ) : EReal)) atTop (𝓝 ⊤))
  (h9 : (forall (n_1 : ℕ), (((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) → ((k n_1) ≤ (p n_1)))))
  (h10 : (forall (n_1 : ℕ), (((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) → ((p n_1) < ((k n_1) + 1)))))
  : (forall (n_1 : ℕ), ((((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ ((k n_1) > 0)) → ((1 /. (k n_1)) ≥ (1 /. (p n_1))))) := by
  sorry

theorem proof_gap_exercise_71_5
  (p : (ℕ -> ℝ))
  (q : (ℕ -> ℝ))
  (n : ℕ)
  (h1 : True)
  (h2 : True)
  (h3 : n ∈ (Set.univ : Set ℕ))
  (h4 : Tendsto (fun n_1 : ℕ => (((p n_1) : ℝ) : EReal)) atTop (𝓝 ⊤))
  (h5 : Tendsto (fun n_1 : ℕ => (((q n_1) : ℝ) : EReal)) atTop (𝓝 ⊥))
  (h6 : (forall (n_1 : ℕ), (((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) → (((p n_1) ∉ (Set.Icc (-(1 : ℝ)) 0)) ∧ ((q n_1) ∉ (Set.Icc (-(1 : ℝ)) 0))))))
  (h7 : (forall (n_1 : ℕ), (((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2})))) → (((k : ℕ → _) n_1) = ⌊(p n_1)⌋)))
  (h8 : Tendsto (fun n_1 : ℕ => (((k n_1) : ℝ) : EReal)) atTop (𝓝 ⊤))
  (h9 : (forall (n_1 : ℕ), (((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) → ((k n_1) ≤ (p n_1)))))
  (h10 : (forall (n_1 : ℕ), (((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) → ((p n_1) < ((k n_1) + 1)))))
  (h11 : (forall (n_1 : ℕ), ((((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ ((k n_1) > 0)) → ((1 /. (k n_1)) ≥ (1 /. (p n_1))))))
  : (forall (n_1 : ℕ), ((((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ ((k n_1) > 0)) → ((1 /. (p n_1)) > (1 /. ((k n_1) + 1))))) := by
  sorry

theorem proof_gap_exercise_71_6
  (p : (ℕ -> ℝ))
  (q : (ℕ -> ℝ))
  (n : ℕ)
  (h1 : True)
  (h2 : True)
  (h3 : n ∈ (Set.univ : Set ℕ))
  (h4 : Tendsto (fun n_1 : ℕ => (((p n_1) : ℝ) : EReal)) atTop (𝓝 ⊤))
  (h5 : Tendsto (fun n_1 : ℕ => (((q n_1) : ℝ) : EReal)) atTop (𝓝 ⊥))
  (h6 : (forall (n_1 : ℕ), (((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) → (((p n_1) ∉ (Set.Icc (-(1 : ℝ)) 0)) ∧ ((q n_1) ∉ (Set.Icc (-(1 : ℝ)) 0))))))
  (h7 : (forall (n_1 : ℕ), (((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2})))) → (((k : ℕ → _) n_1) = ⌊(p n_1)⌋)))
  (h8 : Tendsto (fun n_1 : ℕ => (((k n_1) : ℝ) : EReal)) atTop (𝓝 ⊤))
  (h9 : (forall (n_1 : ℕ), (((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) → ((k n_1) ≤ (p n_1)))))
  (h10 : (forall (n_1 : ℕ), (((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) → ((p n_1) < ((k n_1) + 1)))))
  (h11 : (forall (n_1 : ℕ), ((((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ ((k n_1) > 0)) → ((1 /. (k n_1)) ≥ (1 /. (p n_1))))))
  (h12 : (forall (n_1 : ℕ), ((((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ ((k n_1) > 0)) → ((1 /. (p n_1)) > (1 /. ((k n_1) + 1))))))
  : (forall (n_1 : ℕ), ((((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ ((k n_1) > 0)) → ((Real.rpow (1 + (1 /. (k n_1))) ((k n_1) + 1)) > (Real.rpow (1 + (1 /. (p n_1))) (p n_1))))) := by
  sorry

theorem proof_gap_exercise_71_7
  (p : (ℕ -> ℝ))
  (q : (ℕ -> ℝ))
  (n : ℕ)
  (h1 : True)
  (h2 : True)
  (h3 : n ∈ (Set.univ : Set ℕ))
  (h4 : Tendsto (fun n_1 : ℕ => (((p n_1) : ℝ) : EReal)) atTop (𝓝 ⊤))
  (h5 : Tendsto (fun n_1 : ℕ => (((q n_1) : ℝ) : EReal)) atTop (𝓝 ⊥))
  (h6 : (forall (n_1 : ℕ), (((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) → (((p n_1) ∉ (Set.Icc (-(1 : ℝ)) 0)) ∧ ((q n_1) ∉ (Set.Icc (-(1 : ℝ)) 0))))))
  (h7 : (forall (n_1 : ℕ), (((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2})))) → (((k : ℕ → _) n_1) = ⌊(p n_1)⌋)))
  (h8 : Tendsto (fun n_1 : ℕ => (((k n_1) : ℝ) : EReal)) atTop (𝓝 ⊤))
  (h9 : (forall (n_1 : ℕ), (((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) → ((k n_1) ≤ (p n_1)))))
  (h10 : (forall (n_1 : ℕ), (((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) → ((p n_1) < ((k n_1) + 1)))))
  (h11 : (forall (n_1 : ℕ), ((((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ ((k n_1) > 0)) → ((1 /. (k n_1)) ≥ (1 /. (p n_1))))))
  (h12 : (forall (n_1 : ℕ), ((((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ ((k n_1) > 0)) → ((1 /. (p n_1)) > (1 /. ((k n_1) + 1))))))
  (h13 : (forall (n_1 : ℕ), ((((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ ((k n_1) > 0)) → ((Real.rpow (1 + (1 /. (k n_1))) ((k n_1) + 1)) > (Real.rpow (1 + (1 /. (p n_1))) (p n_1))))))
  : (forall (n_1 : ℕ), ((((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ ((k n_1) > 0)) → ((Real.rpow (1 + (1 /. (p n_1))) (p n_1)) > (Real.rpow (1 + (1 /. ((k n_1) + 1))) (k n_1))))) := by
  sorry

theorem proof_gap_exercise_71_8
  (p : (ℕ -> ℝ))
  (q : (ℕ -> ℝ))
  (n : ℕ)
  (h1 : True)
  (h2 : True)
  (h3 : n ∈ (Set.univ : Set ℕ))
  (h4 : Tendsto (fun n_1 : ℕ => (((p n_1) : ℝ) : EReal)) atTop (𝓝 ⊤))
  (h5 : Tendsto (fun n_1 : ℕ => (((q n_1) : ℝ) : EReal)) atTop (𝓝 ⊥))
  (h6 : (forall (n_1 : ℕ), (((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) → (((p n_1) ∉ (Set.Icc (-(1 : ℝ)) 0)) ∧ ((q n_1) ∉ (Set.Icc (-(1 : ℝ)) 0))))))
  (h7 : (forall (n_1 : ℕ), (((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2})))) → (((k : ℕ → _) n_1) = ⌊(p n_1)⌋)))
  (h8 : Tendsto (fun n_1 : ℕ => (((k n_1) : ℝ) : EReal)) atTop (𝓝 ⊤))
  (h9 : (forall (n_1 : ℕ), (((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) → ((k n_1) ≤ (p n_1)))))
  (h10 : (forall (n_1 : ℕ), (((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) → ((p n_1) < ((k n_1) + 1)))))
  (h11 : (forall (n_1 : ℕ), ((((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ ((k n_1) > 0)) → ((1 /. (k n_1)) ≥ (1 /. (p n_1))))))
  (h12 : (forall (n_1 : ℕ), ((((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ ((k n_1) > 0)) → ((1 /. (p n_1)) > (1 /. ((k n_1) + 1))))))
  (h13 : (forall (n_1 : ℕ), ((((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ ((k n_1) > 0)) → ((Real.rpow (1 + (1 /. (k n_1))) ((k n_1) + 1)) > (Real.rpow (1 + (1 /. (p n_1))) (p n_1))))))
  (h14 : (forall (n_1 : ℕ), ((((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ ((k n_1) > 0)) → ((Real.rpow (1 + (1 /. (p n_1))) (p n_1)) > (Real.rpow (1 + (1 /. ((k n_1) + 1))) (k n_1))))))
  : Tendsto (fun n_1 : ℕ => (Real.rpow (1 + (1 /. (k n_1))) ((k n_1) + 1))) atTop (𝓝 (Real.exp 1)) := by
  sorry

theorem proof_gap_exercise_71_9
  (p : (ℕ -> ℝ))
  (q : (ℕ -> ℝ))
  (n : ℕ)
  (h1 : True)
  (h2 : True)
  (h3 : n ∈ (Set.univ : Set ℕ))
  (h4 : Tendsto (fun n_1 : ℕ => (((p n_1) : ℝ) : EReal)) atTop (𝓝 ⊤))
  (h5 : Tendsto (fun n_1 : ℕ => (((q n_1) : ℝ) : EReal)) atTop (𝓝 ⊥))
  (h6 : (forall (n_1 : ℕ), (((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) → (((p n_1) ∉ (Set.Icc (-(1 : ℝ)) 0)) ∧ ((q n_1) ∉ (Set.Icc (-(1 : ℝ)) 0))))))
  (h7 : (forall (n_1 : ℕ), (((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2})))) → (((k : ℕ → _) n_1) = ⌊(p n_1)⌋)))
  (h8 : Tendsto (fun n_1 : ℕ => (((k n_1) : ℝ) : EReal)) atTop (𝓝 ⊤))
  (h9 : (forall (n_1 : ℕ), (((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) → ((k n_1) ≤ (p n_1)))))
  (h10 : (forall (n_1 : ℕ), (((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) → ((p n_1) < ((k n_1) + 1)))))
  (h11 : (forall (n_1 : ℕ), ((((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ ((k n_1) > 0)) → ((1 /. (k n_1)) ≥ (1 /. (p n_1))))))
  (h12 : (forall (n_1 : ℕ), ((((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ ((k n_1) > 0)) → ((1 /. (p n_1)) > (1 /. ((k n_1) + 1))))))
  (h13 : (forall (n_1 : ℕ), ((((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ ((k n_1) > 0)) → ((Real.rpow (1 + (1 /. (k n_1))) ((k n_1) + 1)) > (Real.rpow (1 + (1 /. (p n_1))) (p n_1))))))
  (h14 : (forall (n_1 : ℕ), ((((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ ((k n_1) > 0)) → ((Real.rpow (1 + (1 /. (p n_1))) (p n_1)) > (Real.rpow (1 + (1 /. ((k n_1) + 1))) (k n_1))))))
  (h15 : Tendsto (fun n_1 : ℕ => (Real.rpow (1 + (1 /. (k n_1))) ((k n_1) + 1))) atTop (𝓝 (Real.exp 1)))
  : (∃ L : ℝ, Tendsto (fun n_1 : ℕ => ((Real.rpow (1 + (1 /. ((k n_1) + 1))) ((k n_1) + 1)) * ((1 + (1 /. ((k n_1) + 1))) ^ (-(1 : ℤ))))) atTop (𝓝 L) ∧ (Tendsto (fun n_1 : ℕ => (Real.rpow (1 + (1 /. ((k n_1) + 1))) (k n_1))) atTop (𝓝 (atTop.limUnder (fun n_1 : ℕ => ((Real.rpow (1 + (1 /. ((k n_1) + 1))) ((k n_1) + 1)) * ((1 + (1 /. ((k n_1) + 1))) ^ (-(1 : ℤ))))))))) := by
  sorry

theorem proof_gap_exercise_71_10
  (p : (ℕ -> ℝ))
  (q : (ℕ -> ℝ))
  (n : ℕ)
  (h1 : True)
  (h2 : True)
  (h3 : n ∈ (Set.univ : Set ℕ))
  (h4 : Tendsto (fun n_1 : ℕ => (((p n_1) : ℝ) : EReal)) atTop (𝓝 ⊤))
  (h5 : Tendsto (fun n_1 : ℕ => (((q n_1) : ℝ) : EReal)) atTop (𝓝 ⊥))
  (h6 : (forall (n_1 : ℕ), (((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) → (((p n_1) ∉ (Set.Icc (-(1 : ℝ)) 0)) ∧ ((q n_1) ∉ (Set.Icc (-(1 : ℝ)) 0))))))
  (h7 : (forall (n_1 : ℕ), (((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2})))) → (((k : ℕ → _) n_1) = ⌊(p n_1)⌋)))
  (h8 : Tendsto (fun n_1 : ℕ => (((k n_1) : ℝ) : EReal)) atTop (𝓝 ⊤))
  (h9 : (forall (n_1 : ℕ), (((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) → ((k n_1) ≤ (p n_1)))))
  (h10 : (forall (n_1 : ℕ), (((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) → ((p n_1) < ((k n_1) + 1)))))
  (h11 : (forall (n_1 : ℕ), ((((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ ((k n_1) > 0)) → ((1 /. (k n_1)) ≥ (1 /. (p n_1))))))
  (h12 : (forall (n_1 : ℕ), ((((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ ((k n_1) > 0)) → ((1 /. (p n_1)) > (1 /. ((k n_1) + 1))))))
  (h13 : (forall (n_1 : ℕ), ((((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ ((k n_1) > 0)) → ((Real.rpow (1 + (1 /. (k n_1))) ((k n_1) + 1)) > (Real.rpow (1 + (1 /. (p n_1))) (p n_1))))))
  (h14 : (forall (n_1 : ℕ), ((((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ ((k n_1) > 0)) → ((Real.rpow (1 + (1 /. (p n_1))) (p n_1)) > (Real.rpow (1 + (1 /. ((k n_1) + 1))) (k n_1))))))
  (h15 : Tendsto (fun n_1 : ℕ => (Real.rpow (1 + (1 /. (k n_1))) ((k n_1) + 1))) atTop (𝓝 (Real.exp 1)))
  (h16 : Tendsto (fun n_1 : ℕ => (Real.rpow (1 + (1 /. ((k n_1) + 1))) (k n_1))) atTop (𝓝 (atTop.limUnder (fun n_1 : ℕ => ((Real.rpow (1 + (1 /. ((k n_1) + 1))) ((k n_1) + 1)) * ((1 + (1 /. ((k n_1) + 1))) ^ (-(1 : ℤ))))))))
  (h17 : ∃ L : ℝ, Tendsto (fun n_1 : ℕ => ((Real.rpow (1 + (1 /. ((k n_1) + 1))) ((k n_1) + 1)) * ((1 + (1 /. ((k n_1) + 1))) ^ (-(1 : ℤ))))) atTop (𝓝 L))
  : Tendsto (fun n_1 : ℕ => (Real.rpow (1 + (1 /. ((k n_1) + 1))) (k n_1))) atTop (𝓝 (Real.exp 1)) := by
  sorry

theorem proof_gap_exercise_71_11
  (p : (ℕ -> ℝ))
  (q : (ℕ -> ℝ))
  (n : ℕ)
  (h1 : True)
  (h2 : True)
  (h3 : n ∈ (Set.univ : Set ℕ))
  (h4 : Tendsto (fun n_1 : ℕ => (((p n_1) : ℝ) : EReal)) atTop (𝓝 ⊤))
  (h5 : Tendsto (fun n_1 : ℕ => (((q n_1) : ℝ) : EReal)) atTop (𝓝 ⊥))
  (h6 : (forall (n_1 : ℕ), (((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) → (((p n_1) ∉ (Set.Icc (-(1 : ℝ)) 0)) ∧ ((q n_1) ∉ (Set.Icc (-(1 : ℝ)) 0))))))
  (h7 : (forall (n_1 : ℕ), (((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2})))) → (((k : ℕ → _) n_1) = ⌊(p n_1)⌋)))
  (h8 : Tendsto (fun n_1 : ℕ => (((k n_1) : ℝ) : EReal)) atTop (𝓝 ⊤))
  (h9 : (forall (n_1 : ℕ), (((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) → ((k n_1) ≤ (p n_1)))))
  (h10 : (forall (n_1 : ℕ), (((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) → ((p n_1) < ((k n_1) + 1)))))
  (h11 : (forall (n_1 : ℕ), ((((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ ((k n_1) > 0)) → ((1 /. (k n_1)) ≥ (1 /. (p n_1))))))
  (h12 : (forall (n_1 : ℕ), ((((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ ((k n_1) > 0)) → ((1 /. (p n_1)) > (1 /. ((k n_1) + 1))))))
  (h13 : (forall (n_1 : ℕ), ((((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ ((k n_1) > 0)) → ((Real.rpow (1 + (1 /. (k n_1))) ((k n_1) + 1)) > (Real.rpow (1 + (1 /. (p n_1))) (p n_1))))))
  (h14 : (forall (n_1 : ℕ), ((((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ ((k n_1) > 0)) → ((Real.rpow (1 + (1 /. (p n_1))) (p n_1)) > (Real.rpow (1 + (1 /. ((k n_1) + 1))) (k n_1))))))
  (h15 : Tendsto (fun n_1 : ℕ => (Real.rpow (1 + (1 /. (k n_1))) ((k n_1) + 1))) atTop (𝓝 (Real.exp 1)))
  (h16 : Tendsto (fun n_1 : ℕ => (Real.rpow (1 + (1 /. ((k n_1) + 1))) (k n_1))) atTop (𝓝 (atTop.limUnder (fun n_1 : ℕ => ((Real.rpow (1 + (1 /. ((k n_1) + 1))) ((k n_1) + 1)) * ((1 + (1 /. ((k n_1) + 1))) ^ (-(1 : ℤ))))))))
  (h17 : Tendsto (fun n_1 : ℕ => (Real.rpow (1 + (1 /. ((k n_1) + 1))) (k n_1))) atTop (𝓝 (Real.exp 1)))
  (h18 : ∃ L : ℝ, Tendsto (fun n_1 : ℕ => ((Real.rpow (1 + (1 /. ((k n_1) + 1))) ((k n_1) + 1)) * ((1 + (1 /. ((k n_1) + 1))) ^ (-(1 : ℤ))))) atTop (𝓝 L))
  : Tendsto (fun n_1 : ℕ => (Real.rpow (1 + (1 /. (p n_1))) (p n_1))) atTop (𝓝 (Real.exp 1)) := by
  sorry

theorem proof_gap_exercise_71_12
  (p : (ℕ -> ℝ))
  (q : (ℕ -> ℝ))
  (n : ℕ)
  (h1 : True)
  (h2 : True)
  (h3 : n ∈ (Set.univ : Set ℕ))
  (h4 : Tendsto (fun n_1 : ℕ => (((p n_1) : ℝ) : EReal)) atTop (𝓝 ⊤))
  (h5 : Tendsto (fun n_1 : ℕ => (((q n_1) : ℝ) : EReal)) atTop (𝓝 ⊥))
  (h6 : (forall (n_1 : ℕ), (((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) → (((p n_1) ∉ (Set.Icc (-(1 : ℝ)) 0)) ∧ ((q n_1) ∉ (Set.Icc (-(1 : ℝ)) 0))))))
  (h7 : (forall (n_1 : ℕ), (((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2})))) → (((k : ℕ → _) n_1) = ⌊(p n_1)⌋)))
  (h8 : Tendsto (fun n_1 : ℕ => (((k n_1) : ℝ) : EReal)) atTop (𝓝 ⊤))
  (h9 : (forall (n_1 : ℕ), (((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) → ((k n_1) ≤ (p n_1)))))
  (h10 : (forall (n_1 : ℕ), (((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) → ((p n_1) < ((k n_1) + 1)))))
  (h11 : (forall (n_1 : ℕ), ((((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ ((k n_1) > 0)) → ((1 /. (k n_1)) ≥ (1 /. (p n_1))))))
  (h12 : (forall (n_1 : ℕ), ((((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ ((k n_1) > 0)) → ((1 /. (p n_1)) > (1 /. ((k n_1) + 1))))))
  (h13 : (forall (n_1 : ℕ), ((((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ ((k n_1) > 0)) → ((Real.rpow (1 + (1 /. (k n_1))) ((k n_1) + 1)) > (Real.rpow (1 + (1 /. (p n_1))) (p n_1))))))
  (h14 : (forall (n_1 : ℕ), ((((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ ((k n_1) > 0)) → ((Real.rpow (1 + (1 /. (p n_1))) (p n_1)) > (Real.rpow (1 + (1 /. ((k n_1) + 1))) (k n_1))))))
  (h15 : Tendsto (fun n_1 : ℕ => (Real.rpow (1 + (1 /. (k n_1))) ((k n_1) + 1))) atTop (𝓝 (Real.exp 1)))
  (h16 : Tendsto (fun n_1 : ℕ => (Real.rpow (1 + (1 /. ((k n_1) + 1))) (k n_1))) atTop (𝓝 (atTop.limUnder (fun n_1 : ℕ => ((Real.rpow (1 + (1 /. ((k n_1) + 1))) ((k n_1) + 1)) * ((1 + (1 /. ((k n_1) + 1))) ^ (-(1 : ℤ))))))))
  (h17 : Tendsto (fun n_1 : ℕ => (Real.rpow (1 + (1 /. ((k n_1) + 1))) (k n_1))) atTop (𝓝 (Real.exp 1)))
  (h18 : Tendsto (fun n_1 : ℕ => (Real.rpow (1 + (1 /. (p n_1))) (p n_1))) atTop (𝓝 (Real.exp 1)))
  (h19 : (forall (n_1 : ℕ), (((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2})))) → (((r : ℕ → _) n_1) = (-(q n_1)))))
  (h20 : ∃ L : ℝ, Tendsto (fun n_1 : ℕ => ((Real.rpow (1 + (1 /. ((k n_1) + 1))) ((k n_1) + 1)) * ((1 + (1 /. ((k n_1) + 1))) ^ (-(1 : ℤ))))) atTop (𝓝 L))
  : Tendsto (fun n_1 : ℕ => (((r n_1) : ℝ) : EReal)) atTop (𝓝 ⊤) := by
  sorry

theorem proof_gap_exercise_71_13
  (p : (ℕ -> ℝ))
  (q : (ℕ -> ℝ))
  (n : ℕ)
  (h1 : True)
  (h2 : True)
  (h3 : n ∈ (Set.univ : Set ℕ))
  (h4 : Tendsto (fun n_1 : ℕ => (((p n_1) : ℝ) : EReal)) atTop (𝓝 ⊤))
  (h5 : Tendsto (fun n_1 : ℕ => (((q n_1) : ℝ) : EReal)) atTop (𝓝 ⊥))
  (h6 : (forall (n_1 : ℕ), (((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) → (((p n_1) ∉ (Set.Icc (-(1 : ℝ)) 0)) ∧ ((q n_1) ∉ (Set.Icc (-(1 : ℝ)) 0))))))
  (h7 : (forall (n_1 : ℕ), (((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2})))) → (((k : ℕ → _) n_1) = ⌊(p n_1)⌋)))
  (h8 : Tendsto (fun n_1 : ℕ => (((k n_1) : ℝ) : EReal)) atTop (𝓝 ⊤))
  (h9 : (forall (n_1 : ℕ), (((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) → ((k n_1) ≤ (p n_1)))))
  (h10 : (forall (n_1 : ℕ), (((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) → ((p n_1) < ((k n_1) + 1)))))
  (h11 : (forall (n_1 : ℕ), ((((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ ((k n_1) > 0)) → ((1 /. (k n_1)) ≥ (1 /. (p n_1))))))
  (h12 : (forall (n_1 : ℕ), ((((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ ((k n_1) > 0)) → ((1 /. (p n_1)) > (1 /. ((k n_1) + 1))))))
  (h13 : (forall (n_1 : ℕ), ((((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ ((k n_1) > 0)) → ((Real.rpow (1 + (1 /. (k n_1))) ((k n_1) + 1)) > (Real.rpow (1 + (1 /. (p n_1))) (p n_1))))))
  (h14 : (forall (n_1 : ℕ), ((((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ ((k n_1) > 0)) → ((Real.rpow (1 + (1 /. (p n_1))) (p n_1)) > (Real.rpow (1 + (1 /. ((k n_1) + 1))) (k n_1))))))
  (h15 : Tendsto (fun n_1 : ℕ => (Real.rpow (1 + (1 /. (k n_1))) ((k n_1) + 1))) atTop (𝓝 (Real.exp 1)))
  (h16 : Tendsto (fun n_1 : ℕ => (Real.rpow (1 + (1 /. ((k n_1) + 1))) (k n_1))) atTop (𝓝 (atTop.limUnder (fun n_1 : ℕ => ((Real.rpow (1 + (1 /. ((k n_1) + 1))) ((k n_1) + 1)) * ((1 + (1 /. ((k n_1) + 1))) ^ (-(1 : ℤ))))))))
  (h17 : Tendsto (fun n_1 : ℕ => (Real.rpow (1 + (1 /. ((k n_1) + 1))) (k n_1))) atTop (𝓝 (Real.exp 1)))
  (h18 : Tendsto (fun n_1 : ℕ => (Real.rpow (1 + (1 /. (p n_1))) (p n_1))) atTop (𝓝 (Real.exp 1)))
  (h19 : (forall (n_1 : ℕ), (((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2})))) → (((r : ℕ → _) n_1) = (-(q n_1)))))
  (h20 : Tendsto (fun n_1 : ℕ => (((r n_1) : ℝ) : EReal)) atTop (𝓝 ⊤))
  (h21 : ∃ L : ℝ, Tendsto (fun n_1 : ℕ => ((Real.rpow (1 + (1 /. ((k n_1) + 1))) ((k n_1) + 1)) * ((1 + (1 /. ((k n_1) + 1))) ^ (-(1 : ℤ))))) atTop (𝓝 L))
  : Tendsto (fun n_1 : ℕ => (Real.rpow (1 + (1 /. (r n_1))) (r n_1))) atTop (𝓝 (Real.exp 1)) := by
  sorry

theorem proof_gap_exercise_71_14
  (p : (ℕ -> ℝ))
  (q : (ℕ -> ℝ))
  (n : ℕ)
  (h1 : True)
  (h2 : True)
  (h3 : n ∈ (Set.univ : Set ℕ))
  (h4 : Tendsto (fun n_1 : ℕ => (((p n_1) : ℝ) : EReal)) atTop (𝓝 ⊤))
  (h5 : Tendsto (fun n_1 : ℕ => (((q n_1) : ℝ) : EReal)) atTop (𝓝 ⊥))
  (h6 : (forall (n_1 : ℕ), (((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) → (((p n_1) ∉ (Set.Icc (-(1 : ℝ)) 0)) ∧ ((q n_1) ∉ (Set.Icc (-(1 : ℝ)) 0))))))
  (h7 : (forall (n_1 : ℕ), (((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2})))) → (((k : ℕ → _) n_1) = ⌊(p n_1)⌋)))
  (h8 : Tendsto (fun n_1 : ℕ => (((k n_1) : ℝ) : EReal)) atTop (𝓝 ⊤))
  (h9 : (forall (n_1 : ℕ), (((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) → ((k n_1) ≤ (p n_1)))))
  (h10 : (forall (n_1 : ℕ), (((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) → ((p n_1) < ((k n_1) + 1)))))
  (h11 : (forall (n_1 : ℕ), ((((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ ((k n_1) > 0)) → ((1 /. (k n_1)) ≥ (1 /. (p n_1))))))
  (h12 : (forall (n_1 : ℕ), ((((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ ((k n_1) > 0)) → ((1 /. (p n_1)) > (1 /. ((k n_1) + 1))))))
  (h13 : (forall (n_1 : ℕ), ((((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ ((k n_1) > 0)) → ((Real.rpow (1 + (1 /. (k n_1))) ((k n_1) + 1)) > (Real.rpow (1 + (1 /. (p n_1))) (p n_1))))))
  (h14 : (forall (n_1 : ℕ), ((((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ ((k n_1) > 0)) → ((Real.rpow (1 + (1 /. (p n_1))) (p n_1)) > (Real.rpow (1 + (1 /. ((k n_1) + 1))) (k n_1))))))
  (h15 : Tendsto (fun n_1 : ℕ => (Real.rpow (1 + (1 /. (k n_1))) ((k n_1) + 1))) atTop (𝓝 (Real.exp 1)))
  (h16 : Tendsto (fun n_1 : ℕ => (Real.rpow (1 + (1 /. ((k n_1) + 1))) (k n_1))) atTop (𝓝 (atTop.limUnder (fun n_1 : ℕ => ((Real.rpow (1 + (1 /. ((k n_1) + 1))) ((k n_1) + 1)) * ((1 + (1 /. ((k n_1) + 1))) ^ (-(1 : ℤ))))))))
  (h17 : Tendsto (fun n_1 : ℕ => (Real.rpow (1 + (1 /. ((k n_1) + 1))) (k n_1))) atTop (𝓝 (Real.exp 1)))
  (h18 : Tendsto (fun n_1 : ℕ => (Real.rpow (1 + (1 /. (p n_1))) (p n_1))) atTop (𝓝 (Real.exp 1)))
  (h19 : (forall (n_1 : ℕ), (((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2})))) → (((r : ℕ → _) n_1) = (-(q n_1)))))
  (h20 : Tendsto (fun n_1 : ℕ => (((r n_1) : ℝ) : EReal)) atTop (𝓝 ⊤))
  (h21 : Tendsto (fun n_1 : ℕ => (Real.rpow (1 + (1 /. (r n_1))) (r n_1))) atTop (𝓝 (Real.exp 1)))
  (h22 : ∃ L : ℝ, Tendsto (fun n_1 : ℕ => ((Real.rpow (1 + (1 /. ((k n_1) + 1))) ((k n_1) + 1)) * ((1 + (1 /. ((k n_1) + 1))) ^ (-(1 : ℤ))))) atTop (𝓝 L))
  : (forall (n_1 : ℕ), ((((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ ((r n_1) > 1)) → ((Real.rpow (1 + (1 /. (q n_1))) (q n_1)) = (Real.rpow (1 - (1 /. (r n_1))) (-(r n_1)))))) := by
  sorry

theorem proof_gap_exercise_71_15
  (p : (ℕ -> ℝ))
  (q : (ℕ -> ℝ))
  (n : ℕ)
  (h1 : True)
  (h2 : True)
  (h3 : n ∈ (Set.univ : Set ℕ))
  (h4 : Tendsto (fun n_1 : ℕ => (((p n_1) : ℝ) : EReal)) atTop (𝓝 ⊤))
  (h5 : Tendsto (fun n_1 : ℕ => (((q n_1) : ℝ) : EReal)) atTop (𝓝 ⊥))
  (h6 : (forall (n_1 : ℕ), (((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) → (((p n_1) ∉ (Set.Icc (-(1 : ℝ)) 0)) ∧ ((q n_1) ∉ (Set.Icc (-(1 : ℝ)) 0))))))
  (h7 : (forall (n_1 : ℕ), (((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2})))) → (((k : ℕ → _) n_1) = ⌊(p n_1)⌋)))
  (h8 : Tendsto (fun n_1 : ℕ => (((k n_1) : ℝ) : EReal)) atTop (𝓝 ⊤))
  (h9 : (forall (n_1 : ℕ), (((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) → ((k n_1) ≤ (p n_1)))))
  (h10 : (forall (n_1 : ℕ), (((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) → ((p n_1) < ((k n_1) + 1)))))
  (h11 : (forall (n_1 : ℕ), ((((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ ((k n_1) > 0)) → ((1 /. (k n_1)) ≥ (1 /. (p n_1))))))
  (h12 : (forall (n_1 : ℕ), ((((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ ((k n_1) > 0)) → ((1 /. (p n_1)) > (1 /. ((k n_1) + 1))))))
  (h13 : (forall (n_1 : ℕ), ((((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ ((k n_1) > 0)) → ((Real.rpow (1 + (1 /. (k n_1))) ((k n_1) + 1)) > (Real.rpow (1 + (1 /. (p n_1))) (p n_1))))))
  (h14 : (forall (n_1 : ℕ), ((((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ ((k n_1) > 0)) → ((Real.rpow (1 + (1 /. (p n_1))) (p n_1)) > (Real.rpow (1 + (1 /. ((k n_1) + 1))) (k n_1))))))
  (h15 : Tendsto (fun n_1 : ℕ => (Real.rpow (1 + (1 /. (k n_1))) ((k n_1) + 1))) atTop (𝓝 (Real.exp 1)))
  (h16 : Tendsto (fun n_1 : ℕ => (Real.rpow (1 + (1 /. ((k n_1) + 1))) (k n_1))) atTop (𝓝 (atTop.limUnder (fun n_1 : ℕ => ((Real.rpow (1 + (1 /. ((k n_1) + 1))) ((k n_1) + 1)) * ((1 + (1 /. ((k n_1) + 1))) ^ (-(1 : ℤ))))))))
  (h17 : Tendsto (fun n_1 : ℕ => (Real.rpow (1 + (1 /. ((k n_1) + 1))) (k n_1))) atTop (𝓝 (Real.exp 1)))
  (h18 : Tendsto (fun n_1 : ℕ => (Real.rpow (1 + (1 /. (p n_1))) (p n_1))) atTop (𝓝 (Real.exp 1)))
  (h19 : (forall (n_1 : ℕ), (((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2})))) → (((r : ℕ → _) n_1) = (-(q n_1)))))
  (h20 : Tendsto (fun n_1 : ℕ => (((r n_1) : ℝ) : EReal)) atTop (𝓝 ⊤))
  (h21 : Tendsto (fun n_1 : ℕ => (Real.rpow (1 + (1 /. (r n_1))) (r n_1))) atTop (𝓝 (Real.exp 1)))
  (h22 : (forall (n_1 : ℕ), ((((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ ((r n_1) > 1)) → ((Real.rpow (1 + (1 /. (q n_1))) (q n_1)) = (Real.rpow (1 - (1 /. (r n_1))) (-(r n_1)))))))
  (h23 : ∃ L : ℝ, Tendsto (fun n_1 : ℕ => ((Real.rpow (1 + (1 /. ((k n_1) + 1))) ((k n_1) + 1)) * ((1 + (1 /. ((k n_1) + 1))) ^ (-(1 : ℤ))))) atTop (𝓝 L))
  : (forall (n_1 : ℕ), ((((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ ((r n_1) > 1)) → ((Real.rpow (1 - (1 /. (r n_1))) (-(r n_1))) = (Real.rpow ((r n_1) /. ((r n_1) - 1)) (r n_1))))) := by
  sorry

theorem proof_gap_exercise_71_16
  (p : (ℕ -> ℝ))
  (q : (ℕ -> ℝ))
  (n : ℕ)
  (h1 : True)
  (h2 : True)
  (h3 : n ∈ (Set.univ : Set ℕ))
  (h4 : Tendsto (fun n_1 : ℕ => (((p n_1) : ℝ) : EReal)) atTop (𝓝 ⊤))
  (h5 : Tendsto (fun n_1 : ℕ => (((q n_1) : ℝ) : EReal)) atTop (𝓝 ⊥))
  (h6 : (forall (n_1 : ℕ), (((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) → (((p n_1) ∉ (Set.Icc (-(1 : ℝ)) 0)) ∧ ((q n_1) ∉ (Set.Icc (-(1 : ℝ)) 0))))))
  (h7 : (forall (n_1 : ℕ), (((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2})))) → (((k : ℕ → _) n_1) = ⌊(p n_1)⌋)))
  (h8 : Tendsto (fun n_1 : ℕ => (((k n_1) : ℝ) : EReal)) atTop (𝓝 ⊤))
  (h9 : (forall (n_1 : ℕ), (((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) → ((k n_1) ≤ (p n_1)))))
  (h10 : (forall (n_1 : ℕ), (((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) → ((p n_1) < ((k n_1) + 1)))))
  (h11 : (forall (n_1 : ℕ), ((((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ ((k n_1) > 0)) → ((1 /. (k n_1)) ≥ (1 /. (p n_1))))))
  (h12 : (forall (n_1 : ℕ), ((((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ ((k n_1) > 0)) → ((1 /. (p n_1)) > (1 /. ((k n_1) + 1))))))
  (h13 : (forall (n_1 : ℕ), ((((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ ((k n_1) > 0)) → ((Real.rpow (1 + (1 /. (k n_1))) ((k n_1) + 1)) > (Real.rpow (1 + (1 /. (p n_1))) (p n_1))))))
  (h14 : (forall (n_1 : ℕ), ((((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ ((k n_1) > 0)) → ((Real.rpow (1 + (1 /. (p n_1))) (p n_1)) > (Real.rpow (1 + (1 /. ((k n_1) + 1))) (k n_1))))))
  (h15 : Tendsto (fun n_1 : ℕ => (Real.rpow (1 + (1 /. (k n_1))) ((k n_1) + 1))) atTop (𝓝 (Real.exp 1)))
  (h16 : Tendsto (fun n_1 : ℕ => (Real.rpow (1 + (1 /. ((k n_1) + 1))) (k n_1))) atTop (𝓝 (atTop.limUnder (fun n_1 : ℕ => ((Real.rpow (1 + (1 /. ((k n_1) + 1))) ((k n_1) + 1)) * ((1 + (1 /. ((k n_1) + 1))) ^ (-(1 : ℤ))))))))
  (h17 : Tendsto (fun n_1 : ℕ => (Real.rpow (1 + (1 /. ((k n_1) + 1))) (k n_1))) atTop (𝓝 (Real.exp 1)))
  (h18 : Tendsto (fun n_1 : ℕ => (Real.rpow (1 + (1 /. (p n_1))) (p n_1))) atTop (𝓝 (Real.exp 1)))
  (h19 : (forall (n_1 : ℕ), (((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2})))) → (((r : ℕ → _) n_1) = (-(q n_1)))))
  (h20 : Tendsto (fun n_1 : ℕ => (((r n_1) : ℝ) : EReal)) atTop (𝓝 ⊤))
  (h21 : Tendsto (fun n_1 : ℕ => (Real.rpow (1 + (1 /. (r n_1))) (r n_1))) atTop (𝓝 (Real.exp 1)))
  (h22 : (forall (n_1 : ℕ), ((((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ ((r n_1) > 1)) → ((Real.rpow (1 + (1 /. (q n_1))) (q n_1)) = (Real.rpow (1 - (1 /. (r n_1))) (-(r n_1)))))))
  (h23 : (forall (n_1 : ℕ), ((((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ ((r n_1) > 1)) → ((Real.rpow (1 - (1 /. (r n_1))) (-(r n_1))) = (Real.rpow ((r n_1) /. ((r n_1) - 1)) (r n_1))))))
  (h24 : ∃ L : ℝ, Tendsto (fun n_1 : ℕ => ((Real.rpow (1 + (1 /. ((k n_1) + 1))) ((k n_1) + 1)) * ((1 + (1 /. ((k n_1) + 1))) ^ (-(1 : ℤ))))) atTop (𝓝 L))
  : (forall (n_1 : ℕ), ((((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ ((r n_1) > 1)) → ((Real.rpow ((r n_1) /. ((r n_1) - 1)) (r n_1)) = ((Real.rpow (1 + (1 /. ((r n_1) - 1))) ((r n_1) - 1)) * (1 + (1 /. ((r n_1) - 1))))))) := by
  sorry

theorem proof_gap_exercise_71_17
  (p : (ℕ -> ℝ))
  (q : (ℕ -> ℝ))
  (n : ℕ)
  (h1 : True)
  (h2 : True)
  (h3 : n ∈ (Set.univ : Set ℕ))
  (h4 : Tendsto (fun n_1 : ℕ => (((p n_1) : ℝ) : EReal)) atTop (𝓝 ⊤))
  (h5 : Tendsto (fun n_1 : ℕ => (((q n_1) : ℝ) : EReal)) atTop (𝓝 ⊥))
  (h6 : (forall (n_1 : ℕ), (((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) → (((p n_1) ∉ (Set.Icc (-(1 : ℝ)) 0)) ∧ ((q n_1) ∉ (Set.Icc (-(1 : ℝ)) 0))))))
  (h7 : (forall (n_1 : ℕ), (((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2})))) → (((k : ℕ → _) n_1) = ⌊(p n_1)⌋)))
  (h8 : Tendsto (fun n_1 : ℕ => (((k n_1) : ℝ) : EReal)) atTop (𝓝 ⊤))
  (h9 : (forall (n_1 : ℕ), (((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) → ((k n_1) ≤ (p n_1)))))
  (h10 : (forall (n_1 : ℕ), (((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) → ((p n_1) < ((k n_1) + 1)))))
  (h11 : (forall (n_1 : ℕ), ((((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ ((k n_1) > 0)) → ((1 /. (k n_1)) ≥ (1 /. (p n_1))))))
  (h12 : (forall (n_1 : ℕ), ((((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ ((k n_1) > 0)) → ((1 /. (p n_1)) > (1 /. ((k n_1) + 1))))))
  (h13 : (forall (n_1 : ℕ), ((((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ ((k n_1) > 0)) → ((Real.rpow (1 + (1 /. (k n_1))) ((k n_1) + 1)) > (Real.rpow (1 + (1 /. (p n_1))) (p n_1))))))
  (h14 : (forall (n_1 : ℕ), ((((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ ((k n_1) > 0)) → ((Real.rpow (1 + (1 /. (p n_1))) (p n_1)) > (Real.rpow (1 + (1 /. ((k n_1) + 1))) (k n_1))))))
  (h15 : Tendsto (fun n_1 : ℕ => (Real.rpow (1 + (1 /. (k n_1))) ((k n_1) + 1))) atTop (𝓝 (Real.exp 1)))
  (h16 : Tendsto (fun n_1 : ℕ => (Real.rpow (1 + (1 /. ((k n_1) + 1))) (k n_1))) atTop (𝓝 (atTop.limUnder (fun n_1 : ℕ => ((Real.rpow (1 + (1 /. ((k n_1) + 1))) ((k n_1) + 1)) * ((1 + (1 /. ((k n_1) + 1))) ^ (-(1 : ℤ))))))))
  (h17 : Tendsto (fun n_1 : ℕ => (Real.rpow (1 + (1 /. ((k n_1) + 1))) (k n_1))) atTop (𝓝 (Real.exp 1)))
  (h18 : Tendsto (fun n_1 : ℕ => (Real.rpow (1 + (1 /. (p n_1))) (p n_1))) atTop (𝓝 (Real.exp 1)))
  (h19 : (forall (n_1 : ℕ), (((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2})))) → (((r : ℕ → _) n_1) = (-(q n_1)))))
  (h20 : Tendsto (fun n_1 : ℕ => (((r n_1) : ℝ) : EReal)) atTop (𝓝 ⊤))
  (h21 : Tendsto (fun n_1 : ℕ => (Real.rpow (1 + (1 /. (r n_1))) (r n_1))) atTop (𝓝 (Real.exp 1)))
  (h22 : (forall (n_1 : ℕ), ((((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ ((r n_1) > 1)) → ((Real.rpow (1 + (1 /. (q n_1))) (q n_1)) = (Real.rpow (1 - (1 /. (r n_1))) (-(r n_1)))))))
  (h23 : (forall (n_1 : ℕ), ((((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ ((r n_1) > 1)) → ((Real.rpow (1 - (1 /. (r n_1))) (-(r n_1))) = (Real.rpow ((r n_1) /. ((r n_1) - 1)) (r n_1))))))
  (h24 : (forall (n_1 : ℕ), ((((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ ((r n_1) > 1)) → ((Real.rpow ((r n_1) /. ((r n_1) - 1)) (r n_1)) = ((Real.rpow (1 + (1 /. ((r n_1) - 1))) ((r n_1) - 1)) * (1 + (1 /. ((r n_1) - 1))))))))
  (h25 : ∃ L : ℝ, Tendsto (fun n_1 : ℕ => ((Real.rpow (1 + (1 /. ((k n_1) + 1))) ((k n_1) + 1)) * ((1 + (1 /. ((k n_1) + 1))) ^ (-(1 : ℤ))))) atTop (𝓝 L))
  : Tendsto (fun n_1 : ℕ => (Real.rpow (1 + (1 /. (q n_1))) (q n_1))) atTop (𝓝 (Real.exp 1)) := by
  sorry

theorem proof_gap_exercise_71_18
  (p : (ℕ -> ℝ))
  (q : (ℕ -> ℝ))
  (n : ℕ)
  (h1 : True)
  (h2 : True)
  (h3 : n ∈ (Set.univ : Set ℕ))
  (h4 : Tendsto (fun n_1 : ℕ => (((p n_1) : ℝ) : EReal)) atTop (𝓝 ⊤))
  (h5 : Tendsto (fun n_1 : ℕ => (((q n_1) : ℝ) : EReal)) atTop (𝓝 ⊥))
  (h6 : (forall (n_1 : ℕ), (((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) → (((p n_1) ∉ (Set.Icc (-(1 : ℝ)) 0)) ∧ ((q n_1) ∉ (Set.Icc (-(1 : ℝ)) 0))))))
  (h7 : (forall (n_1 : ℕ), (((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2})))) → (((k : ℕ → _) n_1) = ⌊(p n_1)⌋)))
  (h8 : Tendsto (fun n_1 : ℕ => (((k n_1) : ℝ) : EReal)) atTop (𝓝 ⊤))
  (h9 : (forall (n_1 : ℕ), (((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) → ((k n_1) ≤ (p n_1)))))
  (h10 : (forall (n_1 : ℕ), (((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) → ((p n_1) < ((k n_1) + 1)))))
  (h11 : (forall (n_1 : ℕ), ((((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ ((k n_1) > 0)) → ((1 /. (k n_1)) ≥ (1 /. (p n_1))))))
  (h12 : (forall (n_1 : ℕ), ((((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ ((k n_1) > 0)) → ((1 /. (p n_1)) > (1 /. ((k n_1) + 1))))))
  (h13 : (forall (n_1 : ℕ), ((((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ ((k n_1) > 0)) → ((Real.rpow (1 + (1 /. (k n_1))) ((k n_1) + 1)) > (Real.rpow (1 + (1 /. (p n_1))) (p n_1))))))
  (h14 : (forall (n_1 : ℕ), ((((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ ((k n_1) > 0)) → ((Real.rpow (1 + (1 /. (p n_1))) (p n_1)) > (Real.rpow (1 + (1 /. ((k n_1) + 1))) (k n_1))))))
  (h15 : Tendsto (fun n_1 : ℕ => (Real.rpow (1 + (1 /. (k n_1))) ((k n_1) + 1))) atTop (𝓝 (Real.exp 1)))
  (h16 : Tendsto (fun n_1 : ℕ => (Real.rpow (1 + (1 /. ((k n_1) + 1))) (k n_1))) atTop (𝓝 (atTop.limUnder (fun n_1 : ℕ => ((Real.rpow (1 + (1 /. ((k n_1) + 1))) ((k n_1) + 1)) * ((1 + (1 /. ((k n_1) + 1))) ^ (-(1 : ℤ))))))))
  (h17 : Tendsto (fun n_1 : ℕ => (Real.rpow (1 + (1 /. ((k n_1) + 1))) (k n_1))) atTop (𝓝 (Real.exp 1)))
  (h18 : Tendsto (fun n_1 : ℕ => (Real.rpow (1 + (1 /. (p n_1))) (p n_1))) atTop (𝓝 (Real.exp 1)))
  (h19 : (forall (n_1 : ℕ), (((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2})))) → (((r : ℕ → _) n_1) = (-(q n_1)))))
  (h20 : Tendsto (fun n_1 : ℕ => (((r n_1) : ℝ) : EReal)) atTop (𝓝 ⊤))
  (h21 : Tendsto (fun n_1 : ℕ => (Real.rpow (1 + (1 /. (r n_1))) (r n_1))) atTop (𝓝 (Real.exp 1)))
  (h22 : (forall (n_1 : ℕ), ((((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ ((r n_1) > 1)) → ((Real.rpow (1 + (1 /. (q n_1))) (q n_1)) = (Real.rpow (1 - (1 /. (r n_1))) (-(r n_1)))))))
  (h23 : (forall (n_1 : ℕ), ((((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ ((r n_1) > 1)) → ((Real.rpow (1 - (1 /. (r n_1))) (-(r n_1))) = (Real.rpow ((r n_1) /. ((r n_1) - 1)) (r n_1))))))
  (h24 : (forall (n_1 : ℕ), ((((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ ((r n_1) > 1)) → ((Real.rpow ((r n_1) /. ((r n_1) - 1)) (r n_1)) = ((Real.rpow (1 + (1 /. ((r n_1) - 1))) ((r n_1) - 1)) * (1 + (1 /. ((r n_1) - 1))))))))
  (h25 : Tendsto (fun n_1 : ℕ => (Real.rpow (1 + (1 /. (q n_1))) (q n_1))) atTop (𝓝 (Real.exp 1)))
  (h26 : ∃ L : ℝ, Tendsto (fun n_1 : ℕ => ((Real.rpow (1 + (1 /. ((k n_1) + 1))) ((k n_1) + 1)) * ((1 + (1 /. ((k n_1) + 1))) ^ (-(1 : ℤ))))) atTop (𝓝 L))
  : Tendsto (fun n_1 : ℕ => (Real.rpow (1 + (1 /. (p n_1))) (p n_1))) atTop (𝓝 (Real.exp 1)) := by
  sorry

theorem proof_gap_exercise_71_19
  (p : (ℕ -> ℝ))
  (q : (ℕ -> ℝ))
  (n : ℕ)
  (h1 : True)
  (h2 : True)
  (h3 : n ∈ (Set.univ : Set ℕ))
  (h4 : Tendsto (fun n_1 : ℕ => (((p n_1) : ℝ) : EReal)) atTop (𝓝 ⊤))
  (h5 : Tendsto (fun n_1 : ℕ => (((q n_1) : ℝ) : EReal)) atTop (𝓝 ⊥))
  (h6 : (forall (n_1 : ℕ), (((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) → (((p n_1) ∉ (Set.Icc (-(1 : ℝ)) 0)) ∧ ((q n_1) ∉ (Set.Icc (-(1 : ℝ)) 0))))))
  (h7 : (forall (n_1 : ℕ), (((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2})))) → (((k : ℕ → _) n_1) = ⌊(p n_1)⌋)))
  (h8 : Tendsto (fun n_1 : ℕ => (((k n_1) : ℝ) : EReal)) atTop (𝓝 ⊤))
  (h9 : (forall (n_1 : ℕ), (((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) → ((k n_1) ≤ (p n_1)))))
  (h10 : (forall (n_1 : ℕ), (((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) → ((p n_1) < ((k n_1) + 1)))))
  (h11 : (forall (n_1 : ℕ), ((((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ ((k n_1) > 0)) → ((1 /. (k n_1)) ≥ (1 /. (p n_1))))))
  (h12 : (forall (n_1 : ℕ), ((((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ ((k n_1) > 0)) → ((1 /. (p n_1)) > (1 /. ((k n_1) + 1))))))
  (h13 : (forall (n_1 : ℕ), ((((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ ((k n_1) > 0)) → ((Real.rpow (1 + (1 /. (k n_1))) ((k n_1) + 1)) > (Real.rpow (1 + (1 /. (p n_1))) (p n_1))))))
  (h14 : (forall (n_1 : ℕ), ((((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ ((k n_1) > 0)) → ((Real.rpow (1 + (1 /. (p n_1))) (p n_1)) > (Real.rpow (1 + (1 /. ((k n_1) + 1))) (k n_1))))))
  (h15 : Tendsto (fun n_1 : ℕ => (Real.rpow (1 + (1 /. (k n_1))) ((k n_1) + 1))) atTop (𝓝 (Real.exp 1)))
  (h16 : Tendsto (fun n_1 : ℕ => (Real.rpow (1 + (1 /. ((k n_1) + 1))) (k n_1))) atTop (𝓝 (atTop.limUnder (fun n_1 : ℕ => ((Real.rpow (1 + (1 /. ((k n_1) + 1))) ((k n_1) + 1)) * ((1 + (1 /. ((k n_1) + 1))) ^ (-(1 : ℤ))))))))
  (h17 : Tendsto (fun n_1 : ℕ => (Real.rpow (1 + (1 /. ((k n_1) + 1))) (k n_1))) atTop (𝓝 (Real.exp 1)))
  (h18 : Tendsto (fun n_1 : ℕ => (Real.rpow (1 + (1 /. (p n_1))) (p n_1))) atTop (𝓝 (Real.exp 1)))
  (h19 : (forall (n_1 : ℕ), (((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2})))) → (((r : ℕ → _) n_1) = (-(q n_1)))))
  (h20 : Tendsto (fun n_1 : ℕ => (((r n_1) : ℝ) : EReal)) atTop (𝓝 ⊤))
  (h21 : Tendsto (fun n_1 : ℕ => (Real.rpow (1 + (1 /. (r n_1))) (r n_1))) atTop (𝓝 (Real.exp 1)))
  (h22 : (forall (n_1 : ℕ), ((((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ ((r n_1) > 1)) → ((Real.rpow (1 + (1 /. (q n_1))) (q n_1)) = (Real.rpow (1 - (1 /. (r n_1))) (-(r n_1)))))))
  (h23 : (forall (n_1 : ℕ), ((((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ ((r n_1) > 1)) → ((Real.rpow (1 - (1 /. (r n_1))) (-(r n_1))) = (Real.rpow ((r n_1) /. ((r n_1) - 1)) (r n_1))))))
  (h24 : (forall (n_1 : ℕ), ((((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ ((r n_1) > 1)) → ((Real.rpow ((r n_1) /. ((r n_1) - 1)) (r n_1)) = ((Real.rpow (1 + (1 /. ((r n_1) - 1))) ((r n_1) - 1)) * (1 + (1 /. ((r n_1) - 1))))))))
  (h25 : Tendsto (fun n_1 : ℕ => (Real.rpow (1 + (1 /. (q n_1))) (q n_1))) atTop (𝓝 (Real.exp 1)))
  (h26 : Tendsto (fun n_1 : ℕ => (Real.rpow (1 + (1 /. (p n_1))) (p n_1))) atTop (𝓝 (Real.exp 1)))
  (h27 : ∃ L : ℝ, Tendsto (fun n_1 : ℕ => ((Real.rpow (1 + (1 /. ((k n_1) + 1))) ((k n_1) + 1)) * ((1 + (1 /. ((k n_1) + 1))) ^ (-(1 : ℤ))))) atTop (𝓝 L))
  : Tendsto (fun n_1 : ℕ => (Real.rpow (1 + (1 /. (q n_1))) (q n_1))) atTop (𝓝 (Real.exp 1)) := by
  sorry

theorem proof_gap_exercise_71_20
  (p : (ℕ -> ℝ))
  (q : (ℕ -> ℝ))
  (n : ℕ)
  (h1 : True)
  (h2 : True)
  (h3 : n ∈ (Set.univ : Set ℕ))
  (h4 : Tendsto (fun n_1 : ℕ => (((p n_1) : ℝ) : EReal)) atTop (𝓝 ⊤))
  (h5 : Tendsto (fun n_1 : ℕ => (((q n_1) : ℝ) : EReal)) atTop (𝓝 ⊥))
  (h6 : (forall (n_1 : ℕ), (((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) → (((p n_1) ∉ (Set.Icc (-(1 : ℝ)) 0)) ∧ ((q n_1) ∉ (Set.Icc (-(1 : ℝ)) 0))))))
  (h7 : (forall (n_1 : ℕ), (((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2})))) → (((k : ℕ → _) n_1) = ⌊(p n_1)⌋)))
  (h8 : Tendsto (fun n_1 : ℕ => (((k n_1) : ℝ) : EReal)) atTop (𝓝 ⊤))
  (h9 : (forall (n_1 : ℕ), (((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) → ((k n_1) ≤ (p n_1)))))
  (h10 : (forall (n_1 : ℕ), (((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) → ((p n_1) < ((k n_1) + 1)))))
  (h11 : (forall (n_1 : ℕ), ((((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ ((k n_1) > 0)) → ((1 /. (k n_1)) ≥ (1 /. (p n_1))))))
  (h12 : (forall (n_1 : ℕ), ((((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ ((k n_1) > 0)) → ((1 /. (p n_1)) > (1 /. ((k n_1) + 1))))))
  (h13 : (forall (n_1 : ℕ), ((((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ ((k n_1) > 0)) → ((Real.rpow (1 + (1 /. (k n_1))) ((k n_1) + 1)) > (Real.rpow (1 + (1 /. (p n_1))) (p n_1))))))
  (h14 : (forall (n_1 : ℕ), ((((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ ((k n_1) > 0)) → ((Real.rpow (1 + (1 /. (p n_1))) (p n_1)) > (Real.rpow (1 + (1 /. ((k n_1) + 1))) (k n_1))))))
  (h15 : Tendsto (fun n_1 : ℕ => (Real.rpow (1 + (1 /. (k n_1))) ((k n_1) + 1))) atTop (𝓝 (Real.exp 1)))
  (h16 : Tendsto (fun n_1 : ℕ => (Real.rpow (1 + (1 /. ((k n_1) + 1))) (k n_1))) atTop (𝓝 (atTop.limUnder (fun n_1 : ℕ => ((Real.rpow (1 + (1 /. ((k n_1) + 1))) ((k n_1) + 1)) * ((1 + (1 /. ((k n_1) + 1))) ^ (-(1 : ℤ))))))))
  (h17 : Tendsto (fun n_1 : ℕ => (Real.rpow (1 + (1 /. ((k n_1) + 1))) (k n_1))) atTop (𝓝 (Real.exp 1)))
  (h18 : Tendsto (fun n_1 : ℕ => (Real.rpow (1 + (1 /. (p n_1))) (p n_1))) atTop (𝓝 (Real.exp 1)))
  (h19 : (forall (n_1 : ℕ), (((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2})))) → (((r : ℕ → _) n_1) = (-(q n_1)))))
  (h20 : Tendsto (fun n_1 : ℕ => (((r n_1) : ℝ) : EReal)) atTop (𝓝 ⊤))
  (h21 : Tendsto (fun n_1 : ℕ => (Real.rpow (1 + (1 /. (r n_1))) (r n_1))) atTop (𝓝 (Real.exp 1)))
  (h22 : (forall (n_1 : ℕ), ((((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ ((r n_1) > 1)) → ((Real.rpow (1 + (1 /. (q n_1))) (q n_1)) = (Real.rpow (1 - (1 /. (r n_1))) (-(r n_1)))))))
  (h23 : (forall (n_1 : ℕ), ((((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ ((r n_1) > 1)) → ((Real.rpow (1 - (1 /. (r n_1))) (-(r n_1))) = (Real.rpow ((r n_1) /. ((r n_1) - 1)) (r n_1))))))
  (h24 : (forall (n_1 : ℕ), ((((n_1 ∈ (Set.univ : Set ℕ)) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ ((r n_1) > 1)) → ((Real.rpow ((r n_1) /. ((r n_1) - 1)) (r n_1)) = ((Real.rpow (1 + (1 /. ((r n_1) - 1))) ((r n_1) - 1)) * (1 + (1 /. ((r n_1) - 1))))))))
  (h25 : Tendsto (fun n_1 : ℕ => (Real.rpow (1 + (1 /. (q n_1))) (q n_1))) atTop (𝓝 (Real.exp 1)))
  (h26 : Tendsto (fun n_1 : ℕ => (Real.rpow (1 + (1 /. (p n_1))) (p n_1))) atTop (𝓝 (Real.exp 1)))
  (h27 : Tendsto (fun n_1 : ℕ => (Real.rpow (1 + (1 /. (q n_1))) (q n_1))) atTop (𝓝 (Real.exp 1)))
  (h28 : ∃ L : ℝ, Tendsto (fun n_1 : ℕ => ((Real.rpow (1 + (1 /. ((k n_1) + 1))) ((k n_1) + 1)) * ((1 + (1 /. ((k n_1) + 1))) ^ (-(1 : ℤ))))) atTop (𝓝 L))
  : (Tendsto (fun n_1 : ℕ => (Real.rpow (1 + (1 /. (p n_1))) (p n_1))) atTop (𝓝 (Real.exp 1))) ∧ (Tendsto (fun n_1 : ℕ => (Real.rpow (1 + (1 /. (q n_1))) (q n_1))) atTop (𝓝 (Real.exp 1))) := by
  sorry
