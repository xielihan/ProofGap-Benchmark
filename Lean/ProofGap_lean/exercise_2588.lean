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

-- exercise: exercise_2588

theorem proof_gap_exercise_2588_1
  (a : (ℕ -> ℝ))
  (b : (ℕ -> ℝ))
  (h1 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ 2)) → ((a n) = (1 /. (Real.rpow (Real.log (n : ℝ)) (((n : ℝ))⁻¹)))))))
  (h2 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ 2)) → ((b n) = (1 /. (Real.rpow (n : ℝ) (((n : ℝ))⁻¹)))))))
  : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ 2)) → (((Real.log (n : ℝ)) > 0) ∧ ((Real.log (n : ℝ)) < n)))) := by
  sorry

theorem proof_gap_exercise_2588_2
  (a : (ℕ -> ℝ))
  (b : (ℕ -> ℝ))
  (h1 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ 2)) → ((a n) = (1 /. (Real.rpow (Real.log (n : ℝ)) (((n : ℝ))⁻¹)))))))
  (h2 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ 2)) → ((b n) = (1 /. (Real.rpow (n : ℝ) (((n : ℝ))⁻¹)))))))
  (h3 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ 2)) → (((Real.log (n : ℝ)) > 0) ∧ ((Real.log (n : ℝ)) < n)))))
  : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ 2)) → (((a n) > (b n)) ∧ ((b n) > 0)))) := by
  sorry

theorem proof_gap_exercise_2588_3
  (a : (ℕ -> ℝ))
  (b : (ℕ -> ℝ))
  (h1 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ 2)) → ((a n) = (1 /. (Real.rpow (Real.log (n : ℝ)) (((n : ℝ))⁻¹)))))))
  (h2 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ 2)) → ((b n) = (1 /. (Real.rpow (n : ℝ) (((n : ℝ))⁻¹)))))))
  (h3 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ 2)) → (((Real.log (n : ℝ)) > 0) ∧ ((Real.log (n : ℝ)) < n)))))
  (h4 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ 2)) → (((a n) > (b n)) ∧ ((b n) > 0)))))
  : Tendsto (fun n : ℕ => (b n)) atTop (𝓝 1) := by
  sorry

theorem proof_gap_exercise_2588_4
  (a : (ℕ -> ℝ))
  (b : (ℕ -> ℝ))
  (h1 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ 2)) → ((a n) = (1 /. (Real.rpow (Real.log (n : ℝ)) (((n : ℝ))⁻¹)))))))
  (h2 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ 2)) → ((b n) = (1 /. (Real.rpow (n : ℝ) (((n : ℝ))⁻¹)))))))
  (h3 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ 2)) → (((Real.log (n : ℝ)) > 0) ∧ ((Real.log (n : ℝ)) < n)))))
  (h4 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ 2)) → (((a n) > (b n)) ∧ ((b n) > 0)))))
  (h5 : Tendsto (fun n : ℕ => (b n)) atTop (𝓝 1))
  : 1 ≠ 0 := by
  sorry

theorem proof_gap_exercise_2588_5
  (a : (ℕ -> ℝ))
  (b : (ℕ -> ℝ))
  (h1 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ 2)) → ((a n) = (1 /. (Real.rpow (Real.log (n : ℝ)) (((n : ℝ))⁻¹)))))))
  (h2 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ 2)) → ((b n) = (1 /. (Real.rpow (n : ℝ) (((n : ℝ))⁻¹)))))))
  (h3 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ 2)) → (((Real.log (n : ℝ)) > 0) ∧ ((Real.log (n : ℝ)) < n)))))
  (h4 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ 2)) → (((a n) > (b n)) ∧ ((b n) > 0)))))
  (h5 : Tendsto (fun n : ℕ => (b n)) atTop (𝓝 1))
  (h6 : 1 ≠ 0)
  : (∃ L : ℝ, Tendsto (fun n : ℕ => (b n)) atTop (𝓝 L) ∧ (atTop.limUnder (fun n : ℕ => (b n)) ≠ 0)) := by
  sorry

theorem proof_gap_exercise_2588_6
  (a : (ℕ -> ℝ))
  (b : (ℕ -> ℝ))
  (h1 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ 2)) → ((a n) = (1 /. (Real.rpow (Real.log (n : ℝ)) (((n : ℝ))⁻¹)))))))
  (h2 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ 2)) → ((b n) = (1 /. (Real.rpow (n : ℝ) (((n : ℝ))⁻¹)))))))
  (h3 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ 2)) → (((Real.log (n : ℝ)) > 0) ∧ ((Real.log (n : ℝ)) < n)))))
  (h4 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ 2)) → (((a n) > (b n)) ∧ ((b n) > 0)))))
  (h5 : Tendsto (fun n : ℕ => (b n)) atTop (𝓝 1))
  (h6 : 1 ≠ 0)
  (h7 : atTop.limUnder (fun n : ℕ => (b n)) ≠ 0)
  (h8 : ∃ L : ℝ, Tendsto (fun n : ℕ => (b n)) atTop (𝓝 L))
  : ¬ Summable (fun (n : ℕ) => if (2 : ℕ) ≤ n then (b n) else 0) := by
  sorry

theorem proof_gap_exercise_2588_7
  (a : (ℕ -> ℝ))
  (b : (ℕ -> ℝ))
  (h1 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ 2)) → ((a n) = (1 /. (Real.rpow (Real.log (n : ℝ)) (((n : ℝ))⁻¹)))))))
  (h2 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ 2)) → ((b n) = (1 /. (Real.rpow (n : ℝ) (((n : ℝ))⁻¹)))))))
  (h3 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ 2)) → (((Real.log (n : ℝ)) > 0) ∧ ((Real.log (n : ℝ)) < n)))))
  (h4 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ 2)) → (((a n) > (b n)) ∧ ((b n) > 0)))))
  (h5 : Tendsto (fun n : ℕ => (b n)) atTop (𝓝 1))
  (h6 : 1 ≠ 0)
  (h7 : atTop.limUnder (fun n : ℕ => (b n)) ≠ 0)
  (h8 : ¬ Summable (fun (n : ℕ) => if (2 : ℕ) ≤ n then (b n) else 0))
  (h9 : ∃ L : ℝ, Tendsto (fun n : ℕ => (b n)) atTop (𝓝 L))
  : ¬ Summable (fun (n : ℕ) => if (2 : ℕ) ≤ n then (a n) else 0) := by
  sorry

theorem proof_gap_exercise_2588_8
  (a : (ℕ -> ℝ))
  (b : (ℕ -> ℝ))
  (h1 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ 2)) → ((a n) = (1 /. (Real.rpow (Real.log (n : ℝ)) (((n : ℝ))⁻¹)))))))
  (h2 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ 2)) → ((b n) = (1 /. (Real.rpow (n : ℝ) (((n : ℝ))⁻¹)))))))
  (h3 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ 2)) → (((Real.log (n : ℝ)) > 0) ∧ ((Real.log (n : ℝ)) < n)))))
  (h4 : (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n ≥ 2)) → (((a n) > (b n)) ∧ ((b n) > 0)))))
  (h5 : Tendsto (fun n : ℕ => (b n)) atTop (𝓝 1))
  (h6 : 1 ≠ 0)
  (h7 : atTop.limUnder (fun n : ℕ => (b n)) ≠ 0)
  (h8 : ¬ Summable (fun (n : ℕ) => if (2 : ℕ) ≤ n then (b n) else 0))
  (h9 : ¬ Summable (fun (n : ℕ) => if (2 : ℕ) ≤ n then (a n) else 0))
  (h10 : ∃ L : ℝ, Tendsto (fun n : ℕ => (b n)) atTop (𝓝 L))
  : ¬ Summable (fun (n : ℕ) => if (2 : ℕ) ≤ n then (a n) else 0) := by
  sorry
