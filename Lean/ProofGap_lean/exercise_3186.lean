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

-- exercise: exercise_3186

theorem proof_gap_exercise_3186_1
  : (forall (x : ℝ), (x ∈ (Set.univ : Set ℝ))) := by
  sorry

theorem proof_gap_exercise_3186_2
  (h1 : (forall (x : ℝ), (x ∈ (Set.univ : Set ℝ))))
  : (forall (y : ℝ), (y ∈ (Set.univ : Set ℝ))) := by
  sorry

theorem proof_gap_exercise_3186_3
  (h1 : (forall (x : ℝ), (x ∈ (Set.univ : Set ℝ))))
  (h2 : (forall (y : ℝ), (y ∈ (Set.univ : Set ℝ))))
  : (forall (x : ℝ) (y : ℝ), ((((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) ≠ 0)) ∧ (x ≠ 0)) ∧ (y ≠ 0)) → (0 ≤ (((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) /. ((x ^ (4 : ℕ)) + (y ^ (4 : ℕ))))))) := by
  sorry

theorem proof_gap_exercise_3186_4
  (h1 : (forall (x : ℝ), (x ∈ (Set.univ : Set ℝ))))
  (h2 : (forall (y : ℝ), (y ∈ (Set.univ : Set ℝ))))
  (h3 : (forall (x : ℝ) (y : ℝ), ((((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) ≠ 0)) ∧ (x ≠ 0)) ∧ (y ≠ 0)) → (0 ≤ (((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) /. ((x ^ (4 : ℕ)) + (y ^ (4 : ℕ))))))))
  : (forall (x : ℝ) (y : ℝ), ((((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) ≠ 0)) ∧ (x ≠ 0)) ∧ (y ≠ 0)) → ((((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) /. ((x ^ (4 : ℕ)) + (y ^ (4 : ℕ)))) ≤ (((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) /. ((2 * (x ^ (2 : ℕ))) * (y ^ (2 : ℕ))))))) := by
  sorry

theorem proof_gap_exercise_3186_5
  (h1 : (forall (x : ℝ), (x ∈ (Set.univ : Set ℝ))))
  (h2 : (forall (y : ℝ), (y ∈ (Set.univ : Set ℝ))))
  (h3 : (forall (x : ℝ) (y : ℝ), ((((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) ≠ 0)) ∧ (x ≠ 0)) ∧ (y ≠ 0)) → (0 ≤ (((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) /. ((x ^ (4 : ℕ)) + (y ^ (4 : ℕ))))))))
  (h4 : (forall (x : ℝ) (y : ℝ), ((((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) ≠ 0)) ∧ (x ≠ 0)) ∧ (y ≠ 0)) → ((((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) /. ((x ^ (4 : ℕ)) + (y ^ (4 : ℕ)))) ≤ (((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) /. ((2 * (x ^ (2 : ℕ))) * (y ^ (2 : ℕ))))))))
  : (forall (x : ℝ) (y : ℝ), ((((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) ≠ 0)) ∧ (x ≠ 0)) ∧ (y ≠ 0)) → ((((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) /. ((2 * (x ^ (2 : ℕ))) * (y ^ (2 : ℕ)))) = ((1 /. 2) * ((1 /. (x ^ (2 : ℕ))) + (1 /. (y ^ (2 : ℕ)))))))) := by
  sorry

theorem proof_gap_exercise_3186_6
  (h1 : (forall (x : ℝ), (x ∈ (Set.univ : Set ℝ))))
  (h2 : (forall (y : ℝ), (y ∈ (Set.univ : Set ℝ))))
  (h3 : (forall (x : ℝ) (y : ℝ), ((((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) ≠ 0)) ∧ (x ≠ 0)) ∧ (y ≠ 0)) → (0 ≤ (((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) /. ((x ^ (4 : ℕ)) + (y ^ (4 : ℕ))))))))
  (h4 : (forall (x : ℝ) (y : ℝ), ((((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) ≠ 0)) ∧ (x ≠ 0)) ∧ (y ≠ 0)) → ((((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) /. ((x ^ (4 : ℕ)) + (y ^ (4 : ℕ)))) ≤ (((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) /. ((2 * (x ^ (2 : ℕ))) * (y ^ (2 : ℕ))))))))
  (h5 : (forall (x : ℝ) (y : ℝ), ((((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) ≠ 0)) ∧ (x ≠ 0)) ∧ (y ≠ 0)) → ((((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) /. ((2 * (x ^ (2 : ℕ))) * (y ^ (2 : ℕ)))) = ((1 /. 2) * ((1 /. (x ^ (2 : ℕ))) + (1 /. (y ^ (2 : ℕ)))))))))
  : (forall (x : ℝ) (y : ℝ), ((((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) ≠ 0)) ∧ (x ≠ 0)) ∧ (y ≠ 0)) → (0 ≤ ((1 /. 2) * ((1 /. (x ^ (2 : ℕ))) + (1 /. (y ^ (2 : ℕ)))))))) := by
  sorry

theorem proof_gap_exercise_3186_7
  (h1 : (forall (x : ℝ), (x ∈ (Set.univ : Set ℝ))))
  (h2 : (forall (y : ℝ), (y ∈ (Set.univ : Set ℝ))))
  (h3 : (forall (x : ℝ) (y : ℝ), ((((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) ≠ 0)) ∧ (x ≠ 0)) ∧ (y ≠ 0)) → (0 ≤ (((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) /. ((x ^ (4 : ℕ)) + (y ^ (4 : ℕ))))))))
  (h4 : (forall (x : ℝ) (y : ℝ), ((((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) ≠ 0)) ∧ (x ≠ 0)) ∧ (y ≠ 0)) → ((((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) /. ((x ^ (4 : ℕ)) + (y ^ (4 : ℕ)))) ≤ (((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) /. ((2 * (x ^ (2 : ℕ))) * (y ^ (2 : ℕ))))))))
  (h5 : (forall (x : ℝ) (y : ℝ), ((((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) ≠ 0)) ∧ (x ≠ 0)) ∧ (y ≠ 0)) → ((((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) /. ((2 * (x ^ (2 : ℕ))) * (y ^ (2 : ℕ)))) = ((1 /. 2) * ((1 /. (x ^ (2 : ℕ))) + (1 /. (y ^ (2 : ℕ)))))))))
  (h6 : (forall (x : ℝ) (y : ℝ), ((((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) ≠ 0)) ∧ (x ≠ 0)) ∧ (y ≠ 0)) → (0 ≤ ((1 /. 2) * ((1 /. (x ^ (2 : ℕ))) + (1 /. (y ^ (2 : ℕ)))))))))
  : Tendsto (fun p : ℝ × ℝ => ((1 /. 2) * ((1 /. (p.1 ^ (2 : ℕ))) + (1 /. (p.2 ^ (2 : ℕ)))))) (atTop ×ˢ atTop) (𝓝 0) := by
  sorry

theorem proof_gap_exercise_3186_8
  (h1 : (forall (x : ℝ), (x ∈ (Set.univ : Set ℝ))))
  (h2 : (forall (y : ℝ), (y ∈ (Set.univ : Set ℝ))))
  (h3 : (forall (x : ℝ) (y : ℝ), ((((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) ≠ 0)) ∧ (x ≠ 0)) ∧ (y ≠ 0)) → (0 ≤ (((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) /. ((x ^ (4 : ℕ)) + (y ^ (4 : ℕ))))))))
  (h4 : (forall (x : ℝ) (y : ℝ), ((((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) ≠ 0)) ∧ (x ≠ 0)) ∧ (y ≠ 0)) → ((((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) /. ((x ^ (4 : ℕ)) + (y ^ (4 : ℕ)))) ≤ (((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) /. ((2 * (x ^ (2 : ℕ))) * (y ^ (2 : ℕ))))))))
  (h5 : (forall (x : ℝ) (y : ℝ), ((((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) ≠ 0)) ∧ (x ≠ 0)) ∧ (y ≠ 0)) → ((((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) /. ((2 * (x ^ (2 : ℕ))) * (y ^ (2 : ℕ)))) = ((1 /. 2) * ((1 /. (x ^ (2 : ℕ))) + (1 /. (y ^ (2 : ℕ)))))))))
  (h6 : (forall (x : ℝ) (y : ℝ), ((((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) ≠ 0)) ∧ (x ≠ 0)) ∧ (y ≠ 0)) → (0 ≤ ((1 /. 2) * ((1 /. (x ^ (2 : ℕ))) + (1 /. (y ^ (2 : ℕ)))))))))
  (h7 : Tendsto (fun p : ℝ × ℝ => ((1 /. 2) * ((1 /. (p.1 ^ (2 : ℕ))) + (1 /. (p.2 ^ (2 : ℕ)))))) (atTop ×ˢ atTop) (𝓝 0))
  : Tendsto (fun p : ℝ × ℝ => (((p.1 ^ (2 : ℕ)) + (p.2 ^ (2 : ℕ))) /. ((p.1 ^ (4 : ℕ)) + (p.2 ^ (4 : ℕ))))) (atTop ×ˢ atTop) (𝓝 0) := by
  sorry
