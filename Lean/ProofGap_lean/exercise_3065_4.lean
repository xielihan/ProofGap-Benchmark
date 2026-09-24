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

-- exercise: exercise_3065_4

theorem proof_gap_exercise_3065_4_1
  (p : (ℕ -> ℝ))
  (q : (ℕ -> ℝ))
  (P : ℝ)
  (Q : ℝ)
  (h1 : P ∈ (Set.univ : Set ℝ))
  (h2 : Q ∈ (Set.univ : Set ℝ))
  (h3 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (i : ℕ), ((i ∈ (Set.univ : Set ℕ)) → (Tendsto (fun n_1 : ℕ => (∏' i_1, if ((i_1 ∈ ({n_2 : ℕ | 0 < n_2})) ∧ (i_1 ≤ n_1)) then (p i_1) else 1)) atTop (𝓝 P)))))))
  (h4 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (i : ℕ), ((i ∈ (Set.univ : Set ℕ)) → (Tendsto (fun n_1 : ℕ => (∏' i_1, if ((i_1 ∈ ({n_2 : ℕ | 0 < n_2})) ∧ (i_1 ≤ n_1)) then (q i_1) else 1)) atTop (𝓝 Q)))))))
  (h5 : P ≠ 0)
  (h6 : Q ≠ 0)
  (h7 : (forall (i : ℕ), (((i ∈ (Set.univ : Set ℕ)) ∧ (i ∈ ({n_1 : ℕ | 0 < n_1}))) → ((q i) ≠ 0))))
  (h8 : A = (fun (n : ℕ) => (∏' i, if ((i ∈ ({n_1 : ℕ | 0 < n_1})) ∧ (i ≤ n)) then (p i) else 1)))
  (h9 : B = (fun (n : ℕ) => (∏' i, if ((i ∈ ({n_1 : ℕ | 0 < n_1})) ∧ (i ≤ n)) then (q i) else 1)))
  (h10 : C = (fun (n : ℕ) => (∏' i, if ((i ∈ ({n_1 : ℕ | 0 < n_1})) ∧ (i ≤ n)) then ((p i) /. (q i)) else 1)))
  : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((C n) = ((A n) /. (B n))))) := by
  sorry

theorem proof_gap_exercise_3065_4_2
  (p : (ℕ -> ℝ))
  (q : (ℕ -> ℝ))
  (P : ℝ)
  (Q : ℝ)
  (h1 : P ∈ (Set.univ : Set ℝ))
  (h2 : Q ∈ (Set.univ : Set ℝ))
  (h3 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (i : ℕ), ((i ∈ (Set.univ : Set ℕ)) → (Tendsto (fun n_1 : ℕ => (∏' i_1, if ((i_1 ∈ ({n_2 : ℕ | 0 < n_2})) ∧ (i_1 ≤ n_1)) then (p i_1) else 1)) atTop (𝓝 P)))))))
  (h4 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (i : ℕ), ((i ∈ (Set.univ : Set ℕ)) → (Tendsto (fun n_1 : ℕ => (∏' i_1, if ((i_1 ∈ ({n_2 : ℕ | 0 < n_2})) ∧ (i_1 ≤ n_1)) then (q i_1) else 1)) atTop (𝓝 Q)))))))
  (h5 : P ≠ 0)
  (h6 : Q ≠ 0)
  (h7 : (forall (i : ℕ), (((i ∈ (Set.univ : Set ℕ)) ∧ (i ∈ ({n_1 : ℕ | 0 < n_1}))) → ((q i) ≠ 0))))
  (h8 : A = (fun (n : ℕ) => (∏' i, if ((i ∈ ({n_1 : ℕ | 0 < n_1})) ∧ (i ≤ n)) then (p i) else 1)))
  (h9 : B = (fun (n : ℕ) => (∏' i, if ((i ∈ ({n_1 : ℕ | 0 < n_1})) ∧ (i ≤ n)) then (q i) else 1)))
  (h10 : C = (fun (n : ℕ) => (∏' i, if ((i ∈ ({n_1 : ℕ | 0 < n_1})) ∧ (i ≤ n)) then ((p i) /. (q i)) else 1)))
  (h11 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((C n) = ((A n) /. (B n))))))
  : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (Tendsto (fun n_1 : ℕ => (A n_1)) atTop (𝓝 P)))) := by
  sorry

theorem proof_gap_exercise_3065_4_3
  (p : (ℕ -> ℝ))
  (q : (ℕ -> ℝ))
  (P : ℝ)
  (Q : ℝ)
  (h1 : P ∈ (Set.univ : Set ℝ))
  (h2 : Q ∈ (Set.univ : Set ℝ))
  (h3 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (i : ℕ), ((i ∈ (Set.univ : Set ℕ)) → (Tendsto (fun n_1 : ℕ => (∏' i_1, if ((i_1 ∈ ({n_2 : ℕ | 0 < n_2})) ∧ (i_1 ≤ n_1)) then (p i_1) else 1)) atTop (𝓝 P)))))))
  (h4 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (i : ℕ), ((i ∈ (Set.univ : Set ℕ)) → (Tendsto (fun n_1 : ℕ => (∏' i_1, if ((i_1 ∈ ({n_2 : ℕ | 0 < n_2})) ∧ (i_1 ≤ n_1)) then (q i_1) else 1)) atTop (𝓝 Q)))))))
  (h5 : P ≠ 0)
  (h6 : Q ≠ 0)
  (h7 : (forall (i : ℕ), (((i ∈ (Set.univ : Set ℕ)) ∧ (i ∈ ({n_1 : ℕ | 0 < n_1}))) → ((q i) ≠ 0))))
  (h8 : A = (fun (n : ℕ) => (∏' i, if ((i ∈ ({n_1 : ℕ | 0 < n_1})) ∧ (i ≤ n)) then (p i) else 1)))
  (h9 : B = (fun (n : ℕ) => (∏' i, if ((i ∈ ({n_1 : ℕ | 0 < n_1})) ∧ (i ≤ n)) then (q i) else 1)))
  (h10 : C = (fun (n : ℕ) => (∏' i, if ((i ∈ ({n_1 : ℕ | 0 < n_1})) ∧ (i ≤ n)) then ((p i) /. (q i)) else 1)))
  (h11 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((C n) = ((A n) /. (B n))))))
  (h12 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (Tendsto (fun n_1 : ℕ => (A n_1)) atTop (𝓝 P)))))
  : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (Tendsto (fun n_1 : ℕ => (B n_1)) atTop (𝓝 Q)))) := by
  sorry

theorem proof_gap_exercise_3065_4_4
  (p : (ℕ -> ℝ))
  (q : (ℕ -> ℝ))
  (P : ℝ)
  (Q : ℝ)
  (h1 : P ∈ (Set.univ : Set ℝ))
  (h2 : Q ∈ (Set.univ : Set ℝ))
  (h3 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (i : ℕ), ((i ∈ (Set.univ : Set ℕ)) → (Tendsto (fun n_1 : ℕ => (∏' i_1, if ((i_1 ∈ ({n_2 : ℕ | 0 < n_2})) ∧ (i_1 ≤ n_1)) then (p i_1) else 1)) atTop (𝓝 P)))))))
  (h4 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (i : ℕ), ((i ∈ (Set.univ : Set ℕ)) → (Tendsto (fun n_1 : ℕ => (∏' i_1, if ((i_1 ∈ ({n_2 : ℕ | 0 < n_2})) ∧ (i_1 ≤ n_1)) then (q i_1) else 1)) atTop (𝓝 Q)))))))
  (h5 : P ≠ 0)
  (h6 : Q ≠ 0)
  (h7 : (forall (i : ℕ), (((i ∈ (Set.univ : Set ℕ)) ∧ (i ∈ ({n_1 : ℕ | 0 < n_1}))) → ((q i) ≠ 0))))
  (h8 : A = (fun (n : ℕ) => (∏' i, if ((i ∈ ({n_1 : ℕ | 0 < n_1})) ∧ (i ≤ n)) then (p i) else 1)))
  (h9 : B = (fun (n : ℕ) => (∏' i, if ((i ∈ ({n_1 : ℕ | 0 < n_1})) ∧ (i ≤ n)) then (q i) else 1)))
  (h10 : C = (fun (n : ℕ) => (∏' i, if ((i ∈ ({n_1 : ℕ | 0 < n_1})) ∧ (i ≤ n)) then ((p i) /. (q i)) else 1)))
  (h11 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((C n) = ((A n) /. (B n))))))
  (h12 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (Tendsto (fun n_1 : ℕ => (A n_1)) atTop (𝓝 P)))))
  (h13 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (Tendsto (fun n_1 : ℕ => (B n_1)) atTop (𝓝 Q)))))
  : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (Tendsto (fun n_1 : ℕ => (C n_1)) atTop (𝓝 (P /. Q))))) := by
  sorry

theorem proof_gap_exercise_3065_4_5
  (p : (ℕ -> ℝ))
  (q : (ℕ -> ℝ))
  (P : ℝ)
  (Q : ℝ)
  (h1 : P ∈ (Set.univ : Set ℝ))
  (h2 : Q ∈ (Set.univ : Set ℝ))
  (h3 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (i : ℕ), ((i ∈ (Set.univ : Set ℕ)) → (Tendsto (fun n_1 : ℕ => (∏' i_1, if ((i_1 ∈ ({n_2 : ℕ | 0 < n_2})) ∧ (i_1 ≤ n_1)) then (p i_1) else 1)) atTop (𝓝 P)))))))
  (h4 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (i : ℕ), ((i ∈ (Set.univ : Set ℕ)) → (Tendsto (fun n_1 : ℕ => (∏' i_1, if ((i_1 ∈ ({n_2 : ℕ | 0 < n_2})) ∧ (i_1 ≤ n_1)) then (q i_1) else 1)) atTop (𝓝 Q)))))))
  (h5 : P ≠ 0)
  (h6 : Q ≠ 0)
  (h7 : (forall (i : ℕ), (((i ∈ (Set.univ : Set ℕ)) ∧ (i ∈ ({n_1 : ℕ | 0 < n_1}))) → ((q i) ≠ 0))))
  (h8 : A = (fun (n : ℕ) => (∏' i, if ((i ∈ ({n_1 : ℕ | 0 < n_1})) ∧ (i ≤ n)) then (p i) else 1)))
  (h9 : B = (fun (n : ℕ) => (∏' i, if ((i ∈ ({n_1 : ℕ | 0 < n_1})) ∧ (i ≤ n)) then (q i) else 1)))
  (h10 : C = (fun (n : ℕ) => (∏' i, if ((i ∈ ({n_1 : ℕ | 0 < n_1})) ∧ (i ≤ n)) then ((p i) /. (q i)) else 1)))
  (h11 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((C n) = ((A n) /. (B n))))))
  (h12 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (Tendsto (fun n_1 : ℕ => (A n_1)) atTop (𝓝 P)))))
  (h13 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (Tendsto (fun n_1 : ℕ => (B n_1)) atTop (𝓝 Q)))))
  (h14 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (Tendsto (fun n_1 : ℕ => (C n_1)) atTop (𝓝 (P /. Q))))))
  : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → (forall (i : ℕ), ((i ∈ (Set.univ : Set ℕ)) → (Tendsto (fun n_1 : ℕ => (∏' i_1, if ((i_1 ∈ ({n_2 : ℕ | 0 < n_2})) ∧ (i_1 ≤ n_1)) then ((p i_1) /. (q i_1)) else 1)) atTop (𝓝 (P /. Q))))))) := by
  sorry
