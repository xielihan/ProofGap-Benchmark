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

-- exercise: exercise_3180

theorem proof_gap_exercise_3180_1
  (f : (ℝ × ℝ -> ℝ))
  (h1 : (forall (s : ℝ) (t : ℝ), ((((s ∈ (Set.univ : Set ℝ)) ∧ (t ∈ (Set.univ : Set ℝ))) ∧ (s ≠ 0)) → ((f ((s + t), (t /. s))) = ((s ^ (2 : ℕ)) - (t ^ (2 : ℕ)))))))
  : (forall (s : ℝ) (t : ℝ), ((((s ∈ (Set.univ : Set ℝ)) ∧ (t ∈ (Set.univ : Set ℝ))) ∧ (s ≠ 0)) → (((f ((s + t), (t /. s))) = ((s ^ (2 : ℕ)) - (t ^ (2 : ℕ)))) ∧ (((s ^ (2 : ℕ)) - (t ^ (2 : ℕ))) = ((s + t) * (s - t)))))) := by
  sorry

theorem proof_gap_exercise_3180_2
  (f : (ℝ × ℝ -> ℝ))
  (h1 : (forall (s : ℝ) (t : ℝ), ((((s ∈ (Set.univ : Set ℝ)) ∧ (t ∈ (Set.univ : Set ℝ))) ∧ (s ≠ 0)) → ((f ((s + t), (t /. s))) = ((s ^ (2 : ℕ)) - (t ^ (2 : ℕ)))))))
  (h2 : (forall (s : ℝ) (t : ℝ), ((((s ∈ (Set.univ : Set ℝ)) ∧ (t ∈ (Set.univ : Set ℝ))) ∧ (s ≠ 0)) → (((f ((s + t), (t /. s))) = ((s ^ (2 : ℕ)) - (t ^ (2 : ℕ)))) ∧ (((s ^ (2 : ℕ)) - (t ^ (2 : ℕ))) = ((s + t) * (s - t)))))))
  : (forall (s : ℝ) (t : ℝ), (((((s ∈ (Set.univ : Set ℝ)) ∧ (t ∈ (Set.univ : Set ℝ))) ∧ (s ≠ 0)) ∧ ((s + t) ≠ 0)) → ((f ((s + t), (t /. s))) = (((s + t) ^ (2 : ℕ)) * ((1 - (t /. s)) /. (1 + (t /. s))))))) := by
  sorry

theorem proof_gap_exercise_3180_3
  (f : (ℝ × ℝ -> ℝ))
  (h1 : (forall (s : ℝ) (t : ℝ), ((((s ∈ (Set.univ : Set ℝ)) ∧ (t ∈ (Set.univ : Set ℝ))) ∧ (s ≠ 0)) → ((f ((s + t), (t /. s))) = ((s ^ (2 : ℕ)) - (t ^ (2 : ℕ)))))))
  (h2 : (forall (s : ℝ) (t : ℝ), ((((s ∈ (Set.univ : Set ℝ)) ∧ (t ∈ (Set.univ : Set ℝ))) ∧ (s ≠ 0)) → (((f ((s + t), (t /. s))) = ((s ^ (2 : ℕ)) - (t ^ (2 : ℕ)))) ∧ (((s ^ (2 : ℕ)) - (t ^ (2 : ℕ))) = ((s + t) * (s - t)))))))
  (h3 : (forall (s : ℝ) (t : ℝ), (((((s ∈ (Set.univ : Set ℝ)) ∧ (t ∈ (Set.univ : Set ℝ))) ∧ (s ≠ 0)) ∧ ((s + t) ≠ 0)) → ((f ((s + t), (t /. s))) = (((s + t) ^ (2 : ℕ)) * ((1 - (t /. s)) /. (1 + (t /. s))))))))
  (h4 : u = (s + t))
  (h5 : v = (t /. s))
  : (v ≠ (-(1 : ℝ))) → ((f (u, v)) = ((u ^ (2 : ℕ)) * ((1 - v) /. (1 + v)))) := by
  sorry

theorem proof_gap_exercise_3180_4
  (f : (ℝ × ℝ -> ℝ))
  (h1 : (forall (s : ℝ) (t : ℝ), ((((s ∈ (Set.univ : Set ℝ)) ∧ (t ∈ (Set.univ : Set ℝ))) ∧ (s ≠ 0)) → ((f ((s + t), (t /. s))) = ((s ^ (2 : ℕ)) - (t ^ (2 : ℕ)))))))
  (h2 : (forall (s : ℝ) (t : ℝ), ((((s ∈ (Set.univ : Set ℝ)) ∧ (t ∈ (Set.univ : Set ℝ))) ∧ (s ≠ 0)) → (((f ((s + t), (t /. s))) = ((s ^ (2 : ℕ)) - (t ^ (2 : ℕ)))) ∧ (((s ^ (2 : ℕ)) - (t ^ (2 : ℕ))) = ((s + t) * (s - t)))))))
  (h3 : (forall (s : ℝ) (t : ℝ), (((((s ∈ (Set.univ : Set ℝ)) ∧ (t ∈ (Set.univ : Set ℝ))) ∧ (s ≠ 0)) ∧ ((s + t) ≠ 0)) → ((f ((s + t), (t /. s))) = (((s + t) ^ (2 : ℕ)) * ((1 - (t /. s)) /. (1 + (t /. s))))))))
  (h4 : u = (s + t))
  (h5 : v = (t /. s))
  (h6 : (v ≠ (-(1 : ℝ))) → ((f (u, v)) = ((u ^ (2 : ℕ)) * ((1 - v) /. (1 + v)))))
  : (forall (x : ℝ) (y : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (y ≠ (-(1 : ℝ)))) → ((f (x, y)) = ((x ^ (2 : ℕ)) * ((1 - y) /. (1 + y)))))) := by
  sorry
