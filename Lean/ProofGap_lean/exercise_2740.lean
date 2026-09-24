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

-- exercise: exercise_2740

theorem proof_gap_exercise_2740_1
  (a : (ℕ -> ℝ))
  (x_0 : ℝ)
  (h1 : x_0 ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) ∈ (Set.univ : Set ℝ)))))
  (h3 : (forall (m : ℕ), (((m ∈ (Set.univ : Set ℕ)) ∧ (m ∈ ({n_1 : ℕ | 0 < n_1}))) → (Summable (fun (m_1 : ℕ) => if (1 : ℕ) ≤ m_1 then ((a m_1) /. (Real.rpow (m_1 : ℝ) x_0)) else 0)))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > x_0)) → ((∑' n, if (1 : ℕ) ≤ n then ((a n) /. (Real.rpow (n : ℝ) x)) else 0) = (∑' n, if (1 : ℕ) ≤ n then (((a n) /. (Real.rpow (n : ℝ) x_0)) * (1 /. (Real.rpow (n : ℝ) (x - x_0)))) else 0)))) := by
  sorry

theorem proof_gap_exercise_2740_2
  (a : (ℕ -> ℝ))
  (x_0 : ℝ)
  (h1 : x_0 ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) ∈ (Set.univ : Set ℝ)))))
  (h3 : (forall (m : ℕ), (((m ∈ (Set.univ : Set ℕ)) ∧ (m ∈ ({n_1 : ℕ | 0 < n_1}))) → (Summable (fun (m_1 : ℕ) => if (1 : ℕ) ≤ m_1 then ((a m_1) /. (Real.rpow (m_1 : ℝ) x_0)) else 0)))))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > x_0)) → ((∑' n, if (1 : ℕ) ≤ n then ((a n) /. (Real.rpow (n : ℝ) x)) else 0) = (∑' n, if (1 : ℕ) ≤ n then (((a n) /. (Real.rpow (n : ℝ) x_0)) * (1 /. (Real.rpow (n : ℝ) (x - x_0)))) else 0)))))
  (h5 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > x_0)) → (exists (b : (ℕ -> ℝ)), (b = (fun (n : ℕ) => (1 /. (Real.rpow (n : ℝ) (x - x_0)))))))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > x_0)) → (exists (b : (ℕ -> ℝ)), (Antitone b)))) := by
  sorry

theorem proof_gap_exercise_2740_3
  (a : (ℕ -> ℝ))
  (x_0 : ℝ)
  (h1 : x_0 ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) ∈ (Set.univ : Set ℝ)))))
  (h3 : (forall (m : ℕ), (((m ∈ (Set.univ : Set ℕ)) ∧ (m ∈ ({n_1 : ℕ | 0 < n_1}))) → (Summable (fun (m_1 : ℕ) => if (1 : ℕ) ≤ m_1 then ((a m_1) /. (Real.rpow (m_1 : ℝ) x_0)) else 0)))))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > x_0)) → ((∑' n, if (1 : ℕ) ≤ n then ((a n) /. (Real.rpow (n : ℝ) x)) else 0) = (∑' n, if (1 : ℕ) ≤ n then (((a n) /. (Real.rpow (n : ℝ) x_0)) * (1 /. (Real.rpow (n : ℝ) (x - x_0)))) else 0)))))
  (h5 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > x_0)) → (exists (b : (ℕ -> ℝ)), (b = (fun (n : ℕ) => (1 /. (Real.rpow (n : ℝ) (x - x_0)))))))))
  (h6 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > x_0)) → (exists (b : (ℕ -> ℝ)), (Antitone b)))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > x_0)) → (exists (b : (ℕ -> ℝ)), (Tendsto (fun n : ℕ => (b n)) atTop (𝓝 0))))) := by
  sorry

theorem proof_gap_exercise_2740_4
  (a : (ℕ -> ℝ))
  (x_0 : ℝ)
  (h1 : x_0 ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) ∈ (Set.univ : Set ℝ)))))
  (h3 : (forall (m : ℕ), (((m ∈ (Set.univ : Set ℕ)) ∧ (m ∈ ({n_1 : ℕ | 0 < n_1}))) → (Summable (fun (m_1 : ℕ) => if (1 : ℕ) ≤ m_1 then ((a m_1) /. (Real.rpow (m_1 : ℝ) x_0)) else 0)))))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > x_0)) → ((∑' n, if (1 : ℕ) ≤ n then ((a n) /. (Real.rpow (n : ℝ) x)) else 0) = (∑' n, if (1 : ℕ) ≤ n then (((a n) /. (Real.rpow (n : ℝ) x_0)) * (1 /. (Real.rpow (n : ℝ) (x - x_0)))) else 0)))))
  (h5 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > x_0)) → (exists (b : (ℕ -> ℝ)), (b = (fun (n : ℕ) => (1 /. (Real.rpow (n : ℝ) (x - x_0)))))))))
  (h6 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > x_0)) → (exists (b : (ℕ -> ℝ)), (Antitone b)))))
  (h7 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > x_0)) → (exists (b : (ℕ -> ℝ)), (Tendsto (fun n : ℕ => (b n)) atTop (𝓝 0))))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > x_0)) → (exists (b : (ℕ -> ℝ)), (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (((a n) /. (Real.rpow (n : ℝ) x_0)) * (b n)) else 0))))) := by
  sorry

theorem proof_gap_exercise_2740_5
  (a : (ℕ -> ℝ))
  (x_0 : ℝ)
  (h1 : x_0 ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) ∈ (Set.univ : Set ℝ)))))
  (h3 : (forall (m : ℕ), (((m ∈ (Set.univ : Set ℕ)) ∧ (m ∈ ({n_1 : ℕ | 0 < n_1}))) → (Summable (fun (m_1 : ℕ) => if (1 : ℕ) ≤ m_1 then ((a m_1) /. (Real.rpow (m_1 : ℝ) x_0)) else 0)))))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > x_0)) → ((∑' n, if (1 : ℕ) ≤ n then ((a n) /. (Real.rpow (n : ℝ) x)) else 0) = (∑' n, if (1 : ℕ) ≤ n then (((a n) /. (Real.rpow (n : ℝ) x_0)) * (1 /. (Real.rpow (n : ℝ) (x - x_0)))) else 0)))))
  (h5 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > x_0)) → (exists (b : (ℕ -> ℝ)), (b = (fun (n : ℕ) => (1 /. (Real.rpow (n : ℝ) (x - x_0)))))))))
  (h6 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > x_0)) → (exists (b : (ℕ -> ℝ)), (Antitone b)))))
  (h7 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > x_0)) → (exists (b : (ℕ -> ℝ)), (Tendsto (fun n : ℕ => (b n)) atTop (𝓝 0))))))
  (h8 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > x_0)) → (exists (b : (ℕ -> ℝ)), (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (((a n) /. (Real.rpow (n : ℝ) x_0)) * (b n)) else 0))))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > x_0)) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ((a n) /. (Real.rpow (n : ℝ) x)) else 0)))) := by
  sorry

theorem proof_gap_exercise_2740_6
  (a : (ℕ -> ℝ))
  (x_0 : ℝ)
  (h1 : x_0 ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) ∈ (Set.univ : Set ℝ)))))
  (h3 : (forall (m : ℕ), (((m ∈ (Set.univ : Set ℕ)) ∧ (m ∈ ({n_1 : ℕ | 0 < n_1}))) → (Summable (fun (m_1 : ℕ) => if (1 : ℕ) ≤ m_1 then ((a m_1) /. (Real.rpow (m_1 : ℝ) x_0)) else 0)))))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > x_0)) → ((∑' n, if (1 : ℕ) ≤ n then ((a n) /. (Real.rpow (n : ℝ) x)) else 0) = (∑' n, if (1 : ℕ) ≤ n then (((a n) /. (Real.rpow (n : ℝ) x_0)) * (1 /. (Real.rpow (n : ℝ) (x - x_0)))) else 0)))))
  (h5 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > x_0)) → (exists (b : (ℕ -> ℝ)), (b = (fun (n : ℕ) => (1 /. (Real.rpow (n : ℝ) (x - x_0)))))))))
  (h6 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > x_0)) → (exists (b : (ℕ -> ℝ)), (Antitone b)))))
  (h7 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > x_0)) → (exists (b : (ℕ -> ℝ)), (Tendsto (fun n : ℕ => (b n)) atTop (𝓝 0))))))
  (h8 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > x_0)) → (exists (b : (ℕ -> ℝ)), (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (((a n) /. (Real.rpow (n : ℝ) x_0)) * (b n)) else 0))))))
  (h9 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > x_0)) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ((a n) /. (Real.rpow (n : ℝ) x)) else 0)))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > x_0)) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ((a n) /. (Real.rpow (n : ℝ) x)) else 0)))) := by
  sorry

theorem proof_gap_exercise_2740_7
  (a : (ℕ -> ℝ))
  (x_0 : ℝ)
  (h1 : x_0 ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) ∈ (Set.univ : Set ℝ)))))
  (h3 : (forall (m : ℕ), (((m ∈ (Set.univ : Set ℕ)) ∧ (m ∈ ({n_1 : ℕ | 0 < n_1}))) → (Summable (fun (m_1 : ℕ) => if (1 : ℕ) ≤ m_1 then ((a m_1) /. (Real.rpow (m_1 : ℝ) x_0)) else 0)))))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > x_0)) → ((∑' n, if (1 : ℕ) ≤ n then ((a n) /. (Real.rpow (n : ℝ) x)) else 0) = (∑' n, if (1 : ℕ) ≤ n then (((a n) /. (Real.rpow (n : ℝ) x_0)) * (1 /. (Real.rpow (n : ℝ) (x - x_0)))) else 0)))))
  (h5 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > x_0)) → (exists (b : (ℕ -> ℝ)), (b = (fun (n : ℕ) => (1 /. (Real.rpow (n : ℝ) (x - x_0)))))))))
  (h6 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > x_0)) → (exists (b : (ℕ -> ℝ)), (Antitone b)))))
  (h7 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > x_0)) → (exists (b : (ℕ -> ℝ)), (Tendsto (fun n : ℕ => (b n)) atTop (𝓝 0))))))
  (h8 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > x_0)) → (exists (b : (ℕ -> ℝ)), (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (((a n) /. (Real.rpow (n : ℝ) x_0)) * (b n)) else 0))))))
  (h9 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > x_0)) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ((a n) /. (Real.rpow (n : ℝ) x)) else 0)))))
  (h10 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > x_0)) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ((a n) /. (Real.rpow (n : ℝ) x)) else 0)))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > x_0)) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ((a n) /. (Real.rpow (n : ℝ) x)) else 0)))) := by
  sorry
