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

-- exercise: exercise_185

theorem proof_gap_exercise_185_1
  (y : (ℝ -> ℝ))
  (x : ℝ)
  (E_x : (Set ℝ))
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : E_x ⊆ (Set.univ : Set ℝ))
  (h3 : E_x = ({x_1 | (x_1 ∈ (Set.univ : Set ℝ)) ∧ (((0 < x_1) ∧ (x_1 < 1)) ∧ (x_1 ≠ (1 /. 2)))}))
  (h4 : (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ E_x)) → ((y x_1) = (x_1 /. ((2 * x_1) - 1))))))
  : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((y x_1) = ((1 /. 2) + ((1 /. 2) * (1 /. ((2 * x_1) - 1))))))) := by
  sorry

theorem proof_gap_exercise_185_2
  (y : (ℝ -> ℝ))
  (x : ℝ)
  (E_x : (Set ℝ))
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : E_x ⊆ (Set.univ : Set ℝ))
  (h3 : E_x = ({x_1 | (x_1 ∈ (Set.univ : Set ℝ)) ∧ (((0 < x_1) ∧ (x_1 < 1)) ∧ (x_1 ≠ (1 /. 2)))}))
  (h4 : (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ E_x)) → ((y x_1) = (x_1 /. ((2 * x_1) - 1))))))
  (h5 : (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≠ (1 /. 2))) → ((y x_1) = ((1 /. 2) + ((1 /. 2) * (1 /. ((2 * x_1) - 1))))))))
  : E_x = ((Set.Ioo 0 (1 /. 2)) ∪ (Set.Ioo (1 /. 2) 1)) := by
  sorry

theorem proof_gap_exercise_185_3
  (y : (ℝ -> ℝ))
  (x : ℝ)
  (E_x : (Set ℝ))
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : E_x ⊆ (Set.univ : Set ℝ))
  (h3 : E_x = ({x_1 | (x_1 ∈ (Set.univ : Set ℝ)) ∧ (((0 < x_1) ∧ (x_1 < 1)) ∧ (x_1 ≠ (1 /. 2)))}))
  (h4 : (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ E_x)) → ((y x_1) = (x_1 /. ((2 * x_1) - 1))))))
  (h5 : (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≠ (1 /. 2))) → ((y x_1) = ((1 /. 2) + ((1 /. 2) * (1 /. ((2 * x_1) - 1))))))))
  (h6 : E_x = ((Set.Ioo 0 (1 /. 2)) ∪ (Set.Ioo (1 /. 2) 1)))
  : Tendsto (fun x_1 : ℝ => (y x_1)) (𝓝[>] 0) (𝓝 0) := by
  sorry

theorem proof_gap_exercise_185_4
  (y : (ℝ -> ℝ))
  (x : ℝ)
  (E_x : (Set ℝ))
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : E_x ⊆ (Set.univ : Set ℝ))
  (h3 : E_x = ({x_1 | (x_1 ∈ (Set.univ : Set ℝ)) ∧ (((0 < x_1) ∧ (x_1 < 1)) ∧ (x_1 ≠ (1 /. 2)))}))
  (h4 : (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ E_x)) → ((y x_1) = (x_1 /. ((2 * x_1) - 1))))))
  (h5 : (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≠ (1 /. 2))) → ((y x_1) = ((1 /. 2) + ((1 /. 2) * (1 /. ((2 * x_1) - 1))))))))
  (h6 : E_x = ((Set.Ioo 0 (1 /. 2)) ∪ (Set.Ioo (1 /. 2) 1)))
  (h7 : Tendsto (fun x_1 : ℝ => (y x_1)) (𝓝[>] 0) (𝓝 0))
  : Tendsto (fun x_1 : ℝ => ((y x_1) : EReal)) (𝓝[<] (1 /. 2)) (𝓝 ⊥) := by
  sorry

theorem proof_gap_exercise_185_5
  (y : (ℝ -> ℝ))
  (x : ℝ)
  (E_x : (Set ℝ))
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : E_x ⊆ (Set.univ : Set ℝ))
  (h3 : E_x = ({x_1 | (x_1 ∈ (Set.univ : Set ℝ)) ∧ (((0 < x_1) ∧ (x_1 < 1)) ∧ (x_1 ≠ (1 /. 2)))}))
  (h4 : (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ E_x)) → ((y x_1) = (x_1 /. ((2 * x_1) - 1))))))
  (h5 : (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≠ (1 /. 2))) → ((y x_1) = ((1 /. 2) + ((1 /. 2) * (1 /. ((2 * x_1) - 1))))))))
  (h6 : E_x = ((Set.Ioo 0 (1 /. 2)) ∪ (Set.Ioo (1 /. 2) 1)))
  (h7 : Tendsto (fun x_1 : ℝ => (y x_1)) (𝓝[>] 0) (𝓝 0))
  (h8 : Tendsto (fun x_1 : ℝ => ((y x_1) : EReal)) (𝓝[<] (1 /. 2)) (𝓝 ⊥))
  : (y '' (Set.Ioo 0 (1 /. 2))) = (Set.Iio 0) := by
  sorry

theorem proof_gap_exercise_185_6
  (y : (ℝ -> ℝ))
  (x : ℝ)
  (E_x : (Set ℝ))
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : E_x ⊆ (Set.univ : Set ℝ))
  (h3 : E_x = ({x_1 | (x_1 ∈ (Set.univ : Set ℝ)) ∧ (((0 < x_1) ∧ (x_1 < 1)) ∧ (x_1 ≠ (1 /. 2)))}))
  (h4 : (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ E_x)) → ((y x_1) = (x_1 /. ((2 * x_1) - 1))))))
  (h5 : (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≠ (1 /. 2))) → ((y x_1) = ((1 /. 2) + ((1 /. 2) * (1 /. ((2 * x_1) - 1))))))))
  (h6 : E_x = ((Set.Ioo 0 (1 /. 2)) ∪ (Set.Ioo (1 /. 2) 1)))
  (h7 : Tendsto (fun x_1 : ℝ => (y x_1)) (𝓝[>] 0) (𝓝 0))
  (h8 : Tendsto (fun x_1 : ℝ => ((y x_1) : EReal)) (𝓝[<] (1 /. 2)) (𝓝 ⊥))
  (h9 : (y '' (Set.Ioo 0 (1 /. 2))) = (Set.Iio 0))
  : Tendsto (fun x_1 : ℝ => ((y x_1) : EReal)) (𝓝[>] (1 /. 2)) (𝓝 ⊤) := by
  sorry

theorem proof_gap_exercise_185_7
  (y : (ℝ -> ℝ))
  (x : ℝ)
  (E_x : (Set ℝ))
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : E_x ⊆ (Set.univ : Set ℝ))
  (h3 : E_x = ({x_1 | (x_1 ∈ (Set.univ : Set ℝ)) ∧ (((0 < x_1) ∧ (x_1 < 1)) ∧ (x_1 ≠ (1 /. 2)))}))
  (h4 : (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ E_x)) → ((y x_1) = (x_1 /. ((2 * x_1) - 1))))))
  (h5 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((y x_1) = ((1 /. 2) + ((1 /. 2) * (1 /. ((2 * x_1) - 1))))))))
  (h6 : E_x = ((Set.Ioo 0 (1 /. 2)) ∪ (Set.Ioo (1 /. 2) 1)))
  (h7 : Tendsto (fun x_1 : ℝ => (y x_1)) (𝓝[>] 0) (𝓝 0))
  (h8 : Tendsto (fun x_1 : ℝ => ((y x_1) : EReal)) (𝓝[<] (1 /. 2)) (𝓝 ⊥))
  (h9 : (y '' (Set.Ioo 0 (1 /. 2))) = (Set.Iio 0))
  (h10 : Tendsto (fun x_1 : ℝ => ((y x_1) : EReal)) (𝓝[>] (1 /. 2)) (𝓝 ⊤))
  : Tendsto (fun x_1 : ℝ => (y x_1)) (𝓝[<] 1) (𝓝 1) := by
  sorry

theorem proof_gap_exercise_185_8
  (y : (ℝ -> ℝ))
  (x : ℝ)
  (E_x : (Set ℝ))
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : E_x ⊆ (Set.univ : Set ℝ))
  (h3 : E_x = ({x_1 | (x_1 ∈ (Set.univ : Set ℝ)) ∧ (((0 < x_1) ∧ (x_1 < 1)) ∧ (x_1 ≠ (1 /. 2)))}))
  (h4 : (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ E_x)) → ((y x_1) = (x_1 /. ((2 * x_1) - 1))))))
  (h5 : (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ≠ (1 /. 2))) → ((y x_1) = ((1 /. 2) + ((1 /. 2) * (1 /. ((2 * x_1) - 1))))))))
  (h6 : E_x = ((Set.Ioo 0 (1 /. 2)) ∪ (Set.Ioo (1 /. 2) 1)))
  (h7 : Tendsto (fun x_1 : ℝ => (y x_1)) (𝓝[>] 0) (𝓝 0))
  (h8 : Tendsto (fun x_1 : ℝ => ((y x_1) : EReal)) (𝓝[<] (1 /. 2)) (𝓝 ⊥))
  (h9 : (y '' (Set.Ioo 0 (1 /. 2))) = (Set.Iio 0))
  (h10 : Tendsto (fun x_1 : ℝ => ((y x_1) : EReal)) (𝓝[>] (1 /. 2)) (𝓝 ⊤))
  (h11 : Tendsto (fun x_1 : ℝ => (y x_1)) (𝓝[<] 1) (𝓝 1))
  : (y '' (Set.Ioo (1 /. 2) 1)) = (Set.Ioi 1) := by
  sorry

theorem proof_gap_exercise_185_9
  (y : (ℝ -> ℝ))
  (x : ℝ)
  (E_x : (Set ℝ))
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : E_x ⊆ (Set.univ : Set ℝ))
  (h3 : E_x = ({x_1 | (x_1 ∈ (Set.univ : Set ℝ)) ∧ (((0 < x_1) ∧ (x_1 < 1)) ∧ (x_1 ≠ (1 /. 2)))}))
  (h4 : (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ E_x)) → ((y x_1) = (x_1 /. ((2 * x_1) - 1))))))
  (h5 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((y x_1) = ((1 /. 2) + ((1 /. 2) * (1 /. ((2 * x_1) - 1))))))))
  (h6 : E_x = ((Set.Ioo 0 (1 /. 2)) ∪ (Set.Ioo (1 /. 2) 1)))
  (h7 : Tendsto (fun x_1 : ℝ => (y x_1)) (𝓝[>] 0) (𝓝 0))
  (h8 : Tendsto (fun x_1 : ℝ => ((y x_1) : EReal)) (𝓝[<] (1 /. 2)) (𝓝 ⊥))
  (h9 : (y '' (Set.Ioo 0 (1 /. 2))) = (Set.Iio 0))
  (h10 : Tendsto (fun x_1 : ℝ => ((y x_1) : EReal)) (𝓝[>] (1 /. 2)) (𝓝 ⊤))
  (h11 : Tendsto (fun x_1 : ℝ => (y x_1)) (𝓝[<] 1) (𝓝 1))
  (h12 : (y '' (Set.Ioo (1 /. 2) 1)) = (Set.Ioi 1))
  : (y '' E_x) = ((Set.Iio 0) ∪ (Set.Ioi 1)) := by
  sorry
