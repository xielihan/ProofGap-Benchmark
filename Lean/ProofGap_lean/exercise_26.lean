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

-- exercise: exercise_26

theorem proof_gap_exercise_26_1
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t = (x - 2))) → (t ∈ (Set.univ : Set ℝ)))) := by
  sorry

theorem proof_gap_exercise_26_2
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t = (x - 2))) → (t ∈ (Set.univ : Set ℝ)))))
  (h3 : (|((x + 2))| + |((x - 2))|) ≤ 12)
  : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t = (x - 2))) → ((|((t + 4))| + |(t)|) ≤ 12))) := by
  sorry

theorem proof_gap_exercise_26_3
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t = (x - 2))) → (t ∈ (Set.univ : Set ℝ)))))
  (h3 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t = (x - 2))) → ((|((t + 4))| + |(t)|) ≤ 12))))
  : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t = (x - 2))) → (|((t + 4))| ≤ (12 - |(t)|)))) := by
  sorry

theorem proof_gap_exercise_26_4
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t = (x - 2))) → (t ∈ (Set.univ : Set ℝ)))))
  (h3 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t = (x - 2))) → ((|((t + 4))| + |(t)|) ≤ 12))))
  (h4 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t = (x - 2))) → (|((t + 4))| ≤ (12 - |(t)|)))))
  : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t = (x - 2))) → (((t + 4) ^ (2 : ℕ)) ≤ ((12 - |(t)|) ^ (2 : ℕ))))) := by
  sorry

theorem proof_gap_exercise_26_5
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t = (x - 2))) → (t ∈ (Set.univ : Set ℝ)))))
  (h3 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t = (x - 2))) → ((|((t + 4))| + |(t)|) ≤ 12))))
  (h4 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t = (x - 2))) → (|((t + 4))| ≤ (12 - |(t)|)))))
  (h5 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t = (x - 2))) → (((t + 4) ^ (2 : ℕ)) ≤ ((12 - |(t)|) ^ (2 : ℕ))))))
  : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t = (x - 2))) → ((((t ^ (2 : ℕ)) + (8 * t)) + 16) ≤ ((144 - (24 * |(t)|)) + (t ^ (2 : ℕ)))))) := by
  sorry

theorem proof_gap_exercise_26_6
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t = (x - 2))) → (t ∈ (Set.univ : Set ℝ)))))
  (h3 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t = (x - 2))) → ((|((t + 4))| + |(t)|) ≤ 12))))
  (h4 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t = (x - 2))) → (|((t + 4))| ≤ (12 - |(t)|)))))
  (h5 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t = (x - 2))) → (((t + 4) ^ (2 : ℕ)) ≤ ((12 - |(t)|) ^ (2 : ℕ))))))
  (h6 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t = (x - 2))) → ((((t ^ (2 : ℕ)) + (8 * t)) + 16) ≤ ((144 - (24 * |(t)|)) + (t ^ (2 : ℕ)))))))
  : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t = (x - 2))) → ((3 * |(t)|) ≤ (16 - t)))) := by
  sorry

theorem proof_gap_exercise_26_7
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t = (x - 2))) → (t ∈ (Set.univ : Set ℝ)))))
  (h3 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t = (x - 2))) → ((|((t + 4))| + |(t)|) ≤ 12))))
  (h4 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t = (x - 2))) → (|((t + 4))| ≤ (12 - |(t)|)))))
  (h5 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t = (x - 2))) → (((t + 4) ^ (2 : ℕ)) ≤ ((12 - |(t)|) ^ (2 : ℕ))))))
  (h6 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t = (x - 2))) → ((((t ^ (2 : ℕ)) + (8 * t)) + 16) ≤ ((144 - (24 * |(t)|)) + (t ^ (2 : ℕ)))))))
  (h7 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t = (x - 2))) → ((3 * |(t)|) ≤ (16 - t)))))
  : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t = (x - 2))) → ((9 * (t ^ (2 : ℕ))) ≤ ((16 - t) ^ (2 : ℕ))))) := by
  sorry

theorem proof_gap_exercise_26_8
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t = (x - 2))) → (t ∈ (Set.univ : Set ℝ)))))
  (h3 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t = (x - 2))) → ((|((t + 4))| + |(t)|) ≤ 12))))
  (h4 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t = (x - 2))) → (|((t + 4))| ≤ (12 - |(t)|)))))
  (h5 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t = (x - 2))) → (((t + 4) ^ (2 : ℕ)) ≤ ((12 - |(t)|) ^ (2 : ℕ))))))
  (h6 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t = (x - 2))) → ((((t ^ (2 : ℕ)) + (8 * t)) + 16) ≤ ((144 - (24 * |(t)|)) + (t ^ (2 : ℕ)))))))
  (h7 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t = (x - 2))) → ((3 * |(t)|) ≤ (16 - t)))))
  (h8 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t = (x - 2))) → ((9 * (t ^ (2 : ℕ))) ≤ ((16 - t) ^ (2 : ℕ))))))
  : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t = (x - 2))) → ((((t ^ (2 : ℕ)) + (4 * t)) - 32) ≤ 0))) := by
  sorry

theorem proof_gap_exercise_26_9
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t = (x - 2))) → (t ∈ (Set.univ : Set ℝ)))))
  (h3 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t = (x - 2))) → ((|((t + 4))| + |(t)|) ≤ 12))))
  (h4 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t = (x - 2))) → (|((t + 4))| ≤ (12 - |(t)|)))))
  (h5 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t = (x - 2))) → (((t + 4) ^ (2 : ℕ)) ≤ ((12 - |(t)|) ^ (2 : ℕ))))))
  (h6 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t = (x - 2))) → ((((t ^ (2 : ℕ)) + (8 * t)) + 16) ≤ ((144 - (24 * |(t)|)) + (t ^ (2 : ℕ)))))))
  (h7 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t = (x - 2))) → ((3 * |(t)|) ≤ (16 - t)))))
  (h8 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t = (x - 2))) → ((9 * (t ^ (2 : ℕ))) ≤ ((16 - t) ^ (2 : ℕ))))))
  (h9 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t = (x - 2))) → ((((t ^ (2 : ℕ)) + (4 * t)) - 32) ≤ 0))))
  : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t = (x - 2))) → ((-(8 : ℝ)) ≤ t))) := by
  sorry

theorem proof_gap_exercise_26_10
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t = (x - 2))) → (t ∈ (Set.univ : Set ℝ)))))
  (h3 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t = (x - 2))) → ((|((t + 4))| + |(t)|) ≤ 12))))
  (h4 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t = (x - 2))) → (|((t + 4))| ≤ (12 - |(t)|)))))
  (h5 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t = (x - 2))) → (((t + 4) ^ (2 : ℕ)) ≤ ((12 - |(t)|) ^ (2 : ℕ))))))
  (h6 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t = (x - 2))) → ((((t ^ (2 : ℕ)) + (8 * t)) + 16) ≤ ((144 - (24 * |(t)|)) + (t ^ (2 : ℕ)))))))
  (h7 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t = (x - 2))) → ((3 * |(t)|) ≤ (16 - t)))))
  (h8 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t = (x - 2))) → ((9 * (t ^ (2 : ℕ))) ≤ ((16 - t) ^ (2 : ℕ))))))
  (h9 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t = (x - 2))) → ((((t ^ (2 : ℕ)) + (4 * t)) - 32) ≤ 0))))
  (h10 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t = (x - 2))) → ((-(8 : ℝ)) ≤ t))))
  : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t = (x - 2))) → (t ≤ 4))) := by
  sorry

theorem proof_gap_exercise_26_11
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t = (x - 2))) → (t ∈ (Set.univ : Set ℝ)))))
  (h3 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t = (x - 2))) → ((|((t + 4))| + |(t)|) ≤ 12))))
  (h4 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t = (x - 2))) → (|((t + 4))| ≤ (12 - |(t)|)))))
  (h5 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t = (x - 2))) → (((t + 4) ^ (2 : ℕ)) ≤ ((12 - |(t)|) ^ (2 : ℕ))))))
  (h6 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t = (x - 2))) → ((((t ^ (2 : ℕ)) + (8 * t)) + 16) ≤ ((144 - (24 * |(t)|)) + (t ^ (2 : ℕ)))))))
  (h7 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t = (x - 2))) → ((3 * |(t)|) ≤ (16 - t)))))
  (h8 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t = (x - 2))) → ((9 * (t ^ (2 : ℕ))) ≤ ((16 - t) ^ (2 : ℕ))))))
  (h9 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t = (x - 2))) → ((((t ^ (2 : ℕ)) + (4 * t)) - 32) ≤ 0))))
  (h10 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t = (x - 2))) → ((-(8 : ℝ)) ≤ t))))
  (h11 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t = (x - 2))) → (t ≤ 4))))
  : (-(8 : ℝ)) ≤ (x - 2) := by
  sorry

theorem proof_gap_exercise_26_12
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t = (x - 2))) → (t ∈ (Set.univ : Set ℝ)))))
  (h3 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t = (x - 2))) → ((|((t + 4))| + |(t)|) ≤ 12))))
  (h4 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t = (x - 2))) → (|((t + 4))| ≤ (12 - |(t)|)))))
  (h5 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t = (x - 2))) → (((t + 4) ^ (2 : ℕ)) ≤ ((12 - |(t)|) ^ (2 : ℕ))))))
  (h6 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t = (x - 2))) → ((((t ^ (2 : ℕ)) + (8 * t)) + 16) ≤ ((144 - (24 * |(t)|)) + (t ^ (2 : ℕ)))))))
  (h7 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t = (x - 2))) → ((3 * |(t)|) ≤ (16 - t)))))
  (h8 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t = (x - 2))) → ((9 * (t ^ (2 : ℕ))) ≤ ((16 - t) ^ (2 : ℕ))))))
  (h9 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t = (x - 2))) → ((((t ^ (2 : ℕ)) + (4 * t)) - 32) ≤ 0))))
  (h10 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t = (x - 2))) → ((-(8 : ℝ)) ≤ t))))
  (h11 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t = (x - 2))) → (t ≤ 4))))
  (h12 : (-(8 : ℝ)) ≤ (x - 2))
  : (x - 2) ≤ 4 := by
  sorry

theorem proof_gap_exercise_26_13
  (x : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t = (x - 2))) → (t ∈ (Set.univ : Set ℝ)))))
  (h3 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t = (x - 2))) → ((|((t + 4))| + |(t)|) ≤ 12))))
  (h4 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t = (x - 2))) → (|((t + 4))| ≤ (12 - |(t)|)))))
  (h5 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t = (x - 2))) → (((t + 4) ^ (2 : ℕ)) ≤ ((12 - |(t)|) ^ (2 : ℕ))))))
  (h6 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t = (x - 2))) → ((((t ^ (2 : ℕ)) + (8 * t)) + 16) ≤ ((144 - (24 * |(t)|)) + (t ^ (2 : ℕ)))))))
  (h7 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t = (x - 2))) → ((3 * |(t)|) ≤ (16 - t)))))
  (h8 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t = (x - 2))) → ((9 * (t ^ (2 : ℕ))) ≤ ((16 - t) ^ (2 : ℕ))))))
  (h9 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t = (x - 2))) → ((((t ^ (2 : ℕ)) + (4 * t)) - 32) ≤ 0))))
  (h10 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t = (x - 2))) → ((-(8 : ℝ)) ≤ t))))
  (h11 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t = (x - 2))) → (t ≤ 4))))
  (h12 : (-(8 : ℝ)) ≤ (x - 2))
  (h13 : (x - 2) ≤ 4)
  : (x ∈ ({x_1 | (x_1 ∈ (Set.univ : Set ℝ)) ∧ ((-(6 : ℝ)) ≤ x_1) ∧ (x_1 ≤ 6)})) ↔ ((|((x + 2))| + |((x - 2))|) ≤ 12) := by
  sorry
