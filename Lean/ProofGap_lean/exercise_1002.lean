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

-- exercise: exercise_1002

theorem proof_gap_exercise_1002_1
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (if (x ≠ 0) then (x * |((Real.cos (Real.pi /. x)))|) else (if (x = 0) then 0 else 0))))))
  : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) ∧ (Not (exists (k : ℤ), ((k ∈ (Set.univ : Set ℤ)) ∧ (x = (2 /. ((2 * k) + 1))))))) → ((Real.cos (Real.pi /. x)) ≠ 0))) := by
  sorry

theorem proof_gap_exercise_1002_2
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (if (x ≠ 0) then (x * |((Real.cos (Real.pi /. x)))|) else (if (x = 0) then 0 else 0))))))
  (h2 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) ∧ (Not (exists (k : ℤ), ((k ∈ (Set.univ : Set ℤ)) ∧ (x = (2 /. ((2 * k) + 1))))))) → ((Real.cos (Real.pi /. x)) ≠ 0))))
  : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) ∧ (Not (exists (k : ℤ), ((k ∈ (Set.univ : Set ℤ)) ∧ (x = (2 /. ((2 * k) + 1))))))) → ((iteratedDeriv 1 (fun t => f t) x) = (|((Real.cos (Real.pi /. x)))| + (((Real.pi /. x) * (|((Real.cos (Real.pi /. x)))| /. (Real.cos (Real.pi /. x)))) * (Real.sin (Real.pi /. x))))))) := by
  sorry

theorem proof_gap_exercise_1002_3
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (if (x ≠ 0) then (x * |((Real.cos (Real.pi /. x)))|) else (if (x = 0) then 0 else 0))))))
  (h2 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) ∧ (Not (exists (k : ℤ), ((k ∈ (Set.univ : Set ℤ)) ∧ (x = (2 /. ((2 * k) + 1))))))) → ((Real.cos (Real.pi /. x)) ≠ 0))))
  (h3 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) ∧ (Not (exists (k : ℤ), ((k ∈ (Set.univ : Set ℤ)) ∧ (x = (2 /. ((2 * k) + 1))))))) → ((iteratedDeriv 1 (fun t => f t) x) = (|((Real.cos (Real.pi /. x)))| + (((Real.pi /. x) * (|((Real.cos (Real.pi /. x)))| /. (Real.cos (Real.pi /. x)))) * (Real.sin (Real.pi /. x))))))))
  : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) ∧ (Not (exists (k : ℤ), ((k ∈ (Set.univ : Set ℤ)) ∧ (x = (2 /. ((2 * k) + 1))))))) → ((|((Real.cos (Real.pi /. x)))| + (((Real.pi /. x) * (|((Real.cos (Real.pi /. x)))| /. (Real.cos (Real.pi /. x)))) * (Real.sin (Real.pi /. x)))) = (((Real.cos (Real.pi /. x)) + ((Real.pi /. x) * (Real.sin (Real.pi /. x)))) * (SignType.sign (Real.cos (Real.pi /. x)) : ℝ))))) := by
  sorry

theorem proof_gap_exercise_1002_4
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (if (x ≠ 0) then (x * |((Real.cos (Real.pi /. x)))|) else (if (x = 0) then 0 else 0))))))
  (h2 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) ∧ (Not (exists (k : ℤ), ((k ∈ (Set.univ : Set ℤ)) ∧ (x = (2 /. ((2 * k) + 1))))))) → ((Real.cos (Real.pi /. x)) ≠ 0))))
  (h3 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) ∧ (Not (exists (k : ℤ), ((k ∈ (Set.univ : Set ℤ)) ∧ (x = (2 /. ((2 * k) + 1))))))) → ((iteratedDeriv 1 (fun t => f t) x) = (|((Real.cos (Real.pi /. x)))| + (((Real.pi /. x) * (|((Real.cos (Real.pi /. x)))| /. (Real.cos (Real.pi /. x)))) * (Real.sin (Real.pi /. x))))))))
  (h4 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) ∧ (Not (exists (k : ℤ), ((k ∈ (Set.univ : Set ℤ)) ∧ (x = (2 /. ((2 * k) + 1))))))) → ((|((Real.cos (Real.pi /. x)))| + (((Real.pi /. x) * (|((Real.cos (Real.pi /. x)))| /. (Real.cos (Real.pi /. x)))) * (Real.sin (Real.pi /. x)))) = (((Real.cos (Real.pi /. x)) + ((Real.pi /. x) * (Real.sin (Real.pi /. x)))) * (SignType.sign (Real.cos (Real.pi /. x)) : ℝ))))))
  : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) ∧ (Not (exists (k : ℤ), ((k ∈ (Set.univ : Set ℤ)) ∧ (x = (2 /. ((2 * k) + 1))))))) → ((iteratedDeriv 1 (fun t => f t) x) = (((Real.cos (Real.pi /. x)) + ((Real.pi /. x) * (Real.sin (Real.pi /. x)))) * (SignType.sign (Real.cos (Real.pi /. x)) : ℝ))))) := by
  sorry

theorem proof_gap_exercise_1002_5
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (if (x ≠ 0) then (x * |((Real.cos (Real.pi /. x)))|) else (if (x = 0) then 0 else 0))))))
  (h2 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) ∧ (Not (exists (k : ℤ), ((k ∈ (Set.univ : Set ℤ)) ∧ (x = (2 /. ((2 * k) + 1))))))) → ((Real.cos (Real.pi /. x)) ≠ 0))))
  (h3 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) ∧ (Not (exists (k : ℤ), ((k ∈ (Set.univ : Set ℤ)) ∧ (x = (2 /. ((2 * k) + 1))))))) → ((iteratedDeriv 1 (fun t_1 => f t_1) x) = (|((Real.cos (Real.pi /. x)))| + (((Real.pi /. x) * (|((Real.cos (Real.pi /. x)))| /. (Real.cos (Real.pi /. x)))) * (Real.sin (Real.pi /. x))))))))
  (h4 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) ∧ (Not (exists (k : ℤ), ((k ∈ (Set.univ : Set ℤ)) ∧ (x = (2 /. ((2 * k) + 1))))))) → ((|((Real.cos (Real.pi /. x)))| + (((Real.pi /. x) * (|((Real.cos (Real.pi /. x)))| /. (Real.cos (Real.pi /. x)))) * (Real.sin (Real.pi /. x)))) = (((Real.cos (Real.pi /. x)) + ((Real.pi /. x) * (Real.sin (Real.pi /. x)))) * (SignType.sign (Real.cos (Real.pi /. x)) : ℝ))))))
  (h5 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) ∧ (Not (exists (k : ℤ), ((k ∈ (Set.univ : Set ℤ)) ∧ (x = (2 /. ((2 * k) + 1))))))) → ((iteratedDeriv 1 (fun t_1 => f t_1) x) = (((Real.cos (Real.pi /. x)) + ((Real.pi /. x) * (Real.sin (Real.pi /. x)))) * (SignType.sign (Real.cos (Real.pi /. x)) : ℝ))))))
  : (forall (k : ℤ), ((k ∈ (Set.univ : Set ℤ)) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (k ∈ (Set.univ : Set ℤ))) ∧ (x = (2 /. ((2 * k) + 1)))) → (Tendsto (fun t : ℝ => (((f t) - (f x)) /. (t - x))) (𝓝[<] x) (𝓝 ((-(((2 * k) + 1) /. 2)) * Real.pi))))))) := by
  sorry

theorem proof_gap_exercise_1002_6
  (f : (ℝ -> ℝ))
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (if (x ≠ 0) then (x * |((Real.cos (Real.pi /. x)))|) else (if (x = 0) then 0 else 0))))))
  (h2 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) ∧ (Not (exists (k : ℤ), ((k ∈ (Set.univ : Set ℤ)) ∧ (x = (2 /. ((2 * k) + 1))))))) → ((Real.cos (Real.pi /. x)) ≠ 0))))
  (h3 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) ∧ (Not (exists (k : ℤ), ((k ∈ (Set.univ : Set ℤ)) ∧ (x = (2 /. ((2 * k) + 1))))))) → ((iteratedDeriv 1 (fun t_1 => f t_1) x) = (|((Real.cos (Real.pi /. x)))| + (((Real.pi /. x) * (|((Real.cos (Real.pi /. x)))| /. (Real.cos (Real.pi /. x)))) * (Real.sin (Real.pi /. x))))))))
  (h4 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) ∧ (Not (exists (k : ℤ), ((k ∈ (Set.univ : Set ℤ)) ∧ (x = (2 /. ((2 * k) + 1))))))) → ((|((Real.cos (Real.pi /. x)))| + (((Real.pi /. x) * (|((Real.cos (Real.pi /. x)))| /. (Real.cos (Real.pi /. x)))) * (Real.sin (Real.pi /. x)))) = (((Real.cos (Real.pi /. x)) + ((Real.pi /. x) * (Real.sin (Real.pi /. x)))) * (SignType.sign (Real.cos (Real.pi /. x)) : ℝ))))))
  (h5 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) ∧ (Not (exists (k : ℤ), ((k ∈ (Set.univ : Set ℤ)) ∧ (x = (2 /. ((2 * k) + 1))))))) → ((iteratedDeriv 1 (fun t_1 => f t_1) x) = (((Real.cos (Real.pi /. x)) + ((Real.pi /. x) * (Real.sin (Real.pi /. x)))) * (SignType.sign (Real.cos (Real.pi /. x)) : ℝ))))))
  (h6 : (forall (k : ℤ), ((k ∈ (Set.univ : Set ℤ)) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (k ∈ (Set.univ : Set ℤ))) ∧ (x = (2 /. ((2 * k) + 1)))) → (Tendsto (fun t : ℝ => (((f t) - (f x)) /. (t - x))) (𝓝[<] x) (𝓝 ((-(((2 * k) + 1) /. 2)) * Real.pi))))))))
  : (forall (k : ℤ), ((k ∈ (Set.univ : Set ℤ)) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (k ∈ (Set.univ : Set ℤ))) ∧ (x = (2 /. ((2 * k) + 1)))) → (Tendsto (fun t : ℝ => (((f t) - (f x)) /. (t - x))) (𝓝[>] x) (𝓝 ((((2 * k) + 1) /. 2) * Real.pi))))))) := by
  sorry
