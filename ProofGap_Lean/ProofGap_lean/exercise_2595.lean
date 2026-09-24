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

-- exercise: exercise_2595

theorem proof_gap_exercise_2595_1
  (h1 : a = (fun (n : ℕ) => ((2 + ((-(1 : ℤ)) ^ n)) /. ((2 : ℕ) ^ n))))
  : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = ((2 + ((-(1 : ℤ)) ^ n)) /. ((2 : ℕ) ^ n))))) := by
  sorry

theorem proof_gap_exercise_2595_2
  (h1 : a = (fun (n : ℕ) => ((2 + ((-(1 : ℤ)) ^ n)) /. ((2 : ℕ) ^ n))))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = ((2 + ((-(1 : ℤ)) ^ n)) /. ((2 : ℕ) ^ n))))))
  : (∃ L : ℝ, Tendsto (fun n : ℕ => ((Real.rpow (2 + (Real.rpow (-(1 : ℝ)) n)) ((n)⁻¹)) /. 2)) atTop (𝓝 L) ∧ (Tendsto (fun n : ℕ => (Real.rpow (a n) ((n)⁻¹))) atTop (𝓝 (atTop.limUnder (fun n : ℕ => ((Real.rpow (2 + (Real.rpow (-(1 : ℝ)) n)) ((n)⁻¹)) /. 2)))))) := by
  sorry

theorem proof_gap_exercise_2595_3
  (h1 : a = (fun (n : ℕ) => ((2 + ((-(1 : ℤ)) ^ n)) /. ((2 : ℕ) ^ n))))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = ((2 + ((-(1 : ℤ)) ^ n)) /. ((2 : ℕ) ^ n))))))
  (h3 : Tendsto (fun n : ℕ => (Real.rpow (a n) ((n)⁻¹))) atTop (𝓝 (atTop.limUnder (fun n : ℕ => ((Real.rpow (2 + (Real.rpow (-(1 : ℝ)) n)) ((n)⁻¹)) /. 2)))))
  (h4 : ∃ L : ℝ, Tendsto (fun n : ℕ => ((Real.rpow (2 + (Real.rpow (-(1 : ℝ)) n)) ((n)⁻¹)) /. 2)) atTop (𝓝 L))
  : Tendsto (fun n : ℕ => ((Real.rpow (2 + (Real.rpow (-(1 : ℝ)) n)) ((n)⁻¹)) /. 2)) atTop (𝓝 (1 /. 2)) := by
  sorry

theorem proof_gap_exercise_2595_4
  (h1 : a = (fun (n : ℕ) => ((2 + ((-(1 : ℤ)) ^ n)) /. ((2 : ℕ) ^ n))))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = ((2 + ((-(1 : ℤ)) ^ n)) /. ((2 : ℕ) ^ n))))))
  (h3 : Tendsto (fun n : ℕ => (Real.rpow (a n) ((n)⁻¹))) atTop (𝓝 (atTop.limUnder (fun n : ℕ => ((Real.rpow (2 + (Real.rpow (-(1 : ℝ)) n)) ((n)⁻¹)) /. 2)))))
  (h4 : Tendsto (fun n : ℕ => ((Real.rpow (2 + (Real.rpow (-(1 : ℝ)) n)) ((n)⁻¹)) /. 2)) atTop (𝓝 (1 /. 2)))
  (h5 : ∃ L : ℝ, Tendsto (fun n : ℕ => ((Real.rpow (2 + (Real.rpow (-(1 : ℝ)) n)) ((n)⁻¹)) /. 2)) atTop (𝓝 L))
  : Tendsto (fun n : ℕ => (Real.rpow (a n) ((n)⁻¹))) atTop (𝓝 (1 /. 2)) := by
  sorry

theorem proof_gap_exercise_2595_5
  (h1 : a = (fun (n : ℕ) => ((2 + ((-(1 : ℤ)) ^ n)) /. ((2 : ℕ) ^ n))))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = ((2 + ((-(1 : ℤ)) ^ n)) /. ((2 : ℕ) ^ n))))))
  (h3 : Tendsto (fun n : ℕ => (Real.rpow (a n) ((n)⁻¹))) atTop (𝓝 (atTop.limUnder (fun n : ℕ => ((Real.rpow (2 + (Real.rpow (-(1 : ℝ)) n)) ((n)⁻¹)) /. 2)))))
  (h4 : Tendsto (fun n : ℕ => ((Real.rpow (2 + (Real.rpow (-(1 : ℝ)) n)) ((n)⁻¹)) /. 2)) atTop (𝓝 (1 /. 2)))
  (h5 : Tendsto (fun n : ℕ => (Real.rpow (a n) ((n)⁻¹))) atTop (𝓝 (1 /. 2)))
  (h6 : ∃ L : ℝ, Tendsto (fun n : ℕ => ((Real.rpow (2 + (Real.rpow (-(1 : ℝ)) n)) ((n)⁻¹)) /. 2)) atTop (𝓝 L))
  : (1 /. 2) < 1 := by
  sorry

theorem proof_gap_exercise_2595_6
  (h1 : a = (fun (n : ℕ) => ((2 + ((-(1 : ℤ)) ^ n)) /. ((2 : ℕ) ^ n))))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = ((2 + ((-(1 : ℤ)) ^ n)) /. ((2 : ℕ) ^ n))))))
  (h3 : Tendsto (fun n : ℕ => (Real.rpow (a n) ((n)⁻¹))) atTop (𝓝 (atTop.limUnder (fun n : ℕ => ((Real.rpow (2 + (Real.rpow (-(1 : ℝ)) n)) ((n)⁻¹)) /. 2)))))
  (h4 : Tendsto (fun n : ℕ => ((Real.rpow (2 + (Real.rpow (-(1 : ℝ)) n)) ((n)⁻¹)) /. 2)) atTop (𝓝 (1 /. 2)))
  (h5 : Tendsto (fun n : ℕ => (Real.rpow (a n) ((n)⁻¹))) atTop (𝓝 (1 /. 2)))
  (h6 : (1 /. 2) < 1)
  (h7 : ∃ L : ℝ, Tendsto (fun n : ℕ => ((Real.rpow (2 + (Real.rpow (-(1 : ℝ)) n)) ((n)⁻¹)) /. 2)) atTop (𝓝 L))
  : Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (a n) else 0) := by
  sorry

theorem proof_gap_exercise_2595_7
  (h1 : a = (fun (n : ℕ) => ((2 + ((-(1 : ℤ)) ^ n)) /. ((2 : ℕ) ^ n))))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = ((2 + ((-(1 : ℤ)) ^ n)) /. ((2 : ℕ) ^ n))))))
  (h3 : Tendsto (fun n : ℕ => (Real.rpow (a n) ((n)⁻¹))) atTop (𝓝 (atTop.limUnder (fun n : ℕ => ((Real.rpow (2 + (Real.rpow (-(1 : ℝ)) n)) ((n)⁻¹)) /. 2)))))
  (h4 : Tendsto (fun n : ℕ => ((Real.rpow (2 + (Real.rpow (-(1 : ℝ)) n)) ((n)⁻¹)) /. 2)) atTop (𝓝 (1 /. 2)))
  (h5 : Tendsto (fun n : ℕ => (Real.rpow (a n) ((n)⁻¹))) atTop (𝓝 (1 /. 2)))
  (h6 : (1 /. 2) < 1)
  (h7 : Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (a n) else 0))
  (h8 : ∃ L : ℝ, Tendsto (fun n : ℕ => ((Real.rpow (2 + (Real.rpow (-(1 : ℝ)) n)) ((n)⁻¹)) /. 2)) atTop (𝓝 L))
  : Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ((2 + ((-(1 : ℤ)) ^ n)) /. ((2 : ℕ) ^ n)) else 0) := by
  sorry

theorem proof_gap_exercise_2595_8
  (h1 : a = (fun (n : ℕ) => ((2 + ((-(1 : ℤ)) ^ n)) /. ((2 : ℕ) ^ n))))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = ((2 + ((-(1 : ℤ)) ^ n)) /. ((2 : ℕ) ^ n))))))
  (h3 : Tendsto (fun n : ℕ => (Real.rpow (a n) ((n)⁻¹))) atTop (𝓝 (atTop.limUnder (fun n : ℕ => ((Real.rpow (2 + (Real.rpow (-(1 : ℝ)) n)) ((n)⁻¹)) /. 2)))))
  (h4 : Tendsto (fun n : ℕ => ((Real.rpow (2 + (Real.rpow (-(1 : ℝ)) n)) ((n)⁻¹)) /. 2)) atTop (𝓝 (1 /. 2)))
  (h5 : Tendsto (fun n : ℕ => (Real.rpow (a n) ((n)⁻¹))) atTop (𝓝 (1 /. 2)))
  (h6 : (1 /. 2) < 1)
  (h7 : Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (a n) else 0))
  (h8 : Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ((2 + ((-(1 : ℤ)) ^ n)) /. ((2 : ℕ) ^ n)) else 0))
  (h9 : ∃ L : ℝ, Tendsto (fun n : ℕ => ((Real.rpow (2 + (Real.rpow (-(1 : ℝ)) n)) ((n)⁻¹)) /. 2)) atTop (𝓝 L))
  : Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ((2 + ((-(1 : ℤ)) ^ n)) /. ((2 : ℕ) ^ n)) else 0) := by
  sorry
