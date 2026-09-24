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

-- exercise: exercise_181

theorem proof_gap_exercise_181_1
  (y : (ℝ -> ℝ))
  (E_x : (Set ℝ))
  (x : ℝ)
  (h1 : E_x ⊆ (Set.univ : Set ℝ))
  (h2 : x ∈ (Set.univ : Set ℝ))
  (h3 : E_x = ({x_1 | (x_1 ∈ (Set.univ : Set ℝ)) ∧ ((0 < |(x_1)|) ∧ (|(x_1)| ≤ 1))}))
  (h4 : (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ E_x)) → ((y x_1) = ((1 : ℝ) /. (Real.tan ((Real.pi * x_1) /. 4)))))))
  : E_x = ((Set.Ico (-(1 : ℝ)) 0) ∪ (Set.Ioc 0 1)) := by
  sorry

theorem proof_gap_exercise_181_2
  (y : (ℝ -> ℝ))
  (E_x : (Set ℝ))
  (x : ℝ)
  (h1 : E_x ⊆ (Set.univ : Set ℝ))
  (h2 : x ∈ (Set.univ : Set ℝ))
  (h3 : E_x = ({x_1 | (x_1 ∈ (Set.univ : Set ℝ)) ∧ ((0 < |(x_1)|) ∧ (|(x_1)| ≤ 1))}))
  (h4 : (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ E_x)) → ((y x_1) = ((1 : ℝ) /. (Real.tan ((Real.pi * x_1) /. 4)))))))
  (h5 : E_x = ((Set.Ico (-(1 : ℝ)) 0) ∪ (Set.Ioc 0 1)))
  : (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Ioc 0 1))) → (((Real.pi * x_1) /. 4) ∈ (Set.Ioc 0 (Real.pi /. 4))))) := by
  sorry

theorem proof_gap_exercise_181_3
  (y : (ℝ -> ℝ))
  (E_x : (Set ℝ))
  (x : ℝ)
  (h1 : E_x ⊆ (Set.univ : Set ℝ))
  (h2 : x ∈ (Set.univ : Set ℝ))
  (h3 : E_x = ({x_1 | (x_1 ∈ (Set.univ : Set ℝ)) ∧ ((0 < |(x_1)|) ∧ (|(x_1)| ≤ 1))}))
  (h4 : (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ E_x)) → ((y x_1) = ((1 : ℝ) /. (Real.tan ((Real.pi * x_1) /. 4)))))))
  (h5 : E_x = ((Set.Ico (-(1 : ℝ)) 0) ∪ (Set.Ioc 0 1)))
  (h6 : (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Ioc 0 1))) → (((Real.pi * x_1) /. 4) ∈ (Set.Ioc 0 (Real.pi /. 4))))))
  : (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Ioc 0 1))) → (AntitoneOn y (Set.Ioc 0 1)))) := by
  sorry

theorem proof_gap_exercise_181_4
  (y : (ℝ -> ℝ))
  (E_x : (Set ℝ))
  (x : ℝ)
  (h1 : E_x ⊆ (Set.univ : Set ℝ))
  (h2 : x ∈ (Set.univ : Set ℝ))
  (h3 : E_x = ({x_1 | (x_1 ∈ (Set.univ : Set ℝ)) ∧ ((0 < |(x_1)|) ∧ (|(x_1)| ≤ 1))}))
  (h4 : (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ E_x)) → ((y x_1) = ((1 : ℝ) /. (Real.tan ((Real.pi * x_1) /. 4)))))))
  (h5 : E_x = ((Set.Ico (-(1 : ℝ)) 0) ∪ (Set.Ioc 0 1)))
  (h6 : (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Ioc 0 1))) → (((Real.pi * x_1) /. 4) ∈ (Set.Ioc 0 (Real.pi /. 4))))))
  (h7 : (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Ioc 0 1))) → (AntitoneOn y (Set.Ioc 0 1)))))
  : (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Ioc 0 1))) → ((y '' (Set.Ioc 0 1)) = (Set.Ici 1)))) := by
  sorry

theorem proof_gap_exercise_181_5
  (y : (ℝ -> ℝ))
  (E_x : (Set ℝ))
  (x : ℝ)
  (h1 : E_x ⊆ (Set.univ : Set ℝ))
  (h2 : x ∈ (Set.univ : Set ℝ))
  (h3 : E_x = ({x_1 | (x_1 ∈ (Set.univ : Set ℝ)) ∧ ((0 < |(x_1)|) ∧ (|(x_1)| ≤ 1))}))
  (h4 : (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ E_x)) → ((y x_1) = ((1 : ℝ) /. (Real.tan ((Real.pi * x_1) /. 4)))))))
  (h5 : E_x = ((Set.Ico (-(1 : ℝ)) 0) ∪ (Set.Ioc 0 1)))
  (h6 : (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Ioc 0 1))) → (((Real.pi * x_1) /. 4) ∈ (Set.Ioc 0 (Real.pi /. 4))))))
  (h7 : (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Ioc 0 1))) → (AntitoneOn y (Set.Ioc 0 1)))))
  (h8 : (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Ioc 0 1))) → ((y '' (Set.Ioc 0 1)) = (Set.Ici 1)))))
  : (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Ico (-(1 : ℝ)) 0))) → (((Real.pi * x_1) /. 4) ∈ (Set.Ico (-(Real.pi /. 4)) 0)))) := by
  sorry

theorem proof_gap_exercise_181_6
  (y : (ℝ -> ℝ))
  (E_x : (Set ℝ))
  (x : ℝ)
  (h1 : E_x ⊆ (Set.univ : Set ℝ))
  (h2 : x ∈ (Set.univ : Set ℝ))
  (h3 : E_x = ({x_1 | (x_1 ∈ (Set.univ : Set ℝ)) ∧ ((0 < |(x_1)|) ∧ (|(x_1)| ≤ 1))}))
  (h4 : (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ E_x)) → ((y x_1) = ((1 : ℝ) /. (Real.tan ((Real.pi * x_1) /. 4)))))))
  (h5 : E_x = ((Set.Ico (-(1 : ℝ)) 0) ∪ (Set.Ioc 0 1)))
  (h6 : (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Ioc 0 1))) → (((Real.pi * x_1) /. 4) ∈ (Set.Ioc 0 (Real.pi /. 4))))))
  (h7 : (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Ioc 0 1))) → (AntitoneOn y (Set.Ioc 0 1)))))
  (h8 : (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Ioc 0 1))) → ((y '' (Set.Ioc 0 1)) = (Set.Ici 1)))))
  (h9 : (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Ico (-(1 : ℝ)) 0))) → (((Real.pi * x_1) /. 4) ∈ (Set.Ico (-(Real.pi /. 4)) 0)))))
  : (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Ico (-(1 : ℝ)) 0))) → ((y x_1) < 0))) := by
  sorry

theorem proof_gap_exercise_181_7
  (y : (ℝ -> ℝ))
  (E_x : (Set ℝ))
  (x : ℝ)
  (h1 : E_x ⊆ (Set.univ : Set ℝ))
  (h2 : x ∈ (Set.univ : Set ℝ))
  (h3 : E_x = ({x_1 | (x_1 ∈ (Set.univ : Set ℝ)) ∧ ((0 < |(x_1)|) ∧ (|(x_1)| ≤ 1))}))
  (h4 : (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ E_x)) → ((y x_1) = ((1 : ℝ) /. (Real.tan ((Real.pi * x_1) /. 4)))))))
  (h5 : E_x = ((Set.Ico (-(1 : ℝ)) 0) ∪ (Set.Ioc 0 1)))
  (h6 : (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Ioc 0 1))) → (((Real.pi * x_1) /. 4) ∈ (Set.Ioc 0 (Real.pi /. 4))))))
  (h7 : (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Ioc 0 1))) → (AntitoneOn y (Set.Ioc 0 1)))))
  (h8 : (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Ioc 0 1))) → ((y '' (Set.Ioc 0 1)) = (Set.Ici 1)))))
  (h9 : (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Ico (-(1 : ℝ)) 0))) → (((Real.pi * x_1) /. 4) ∈ (Set.Ico (-(Real.pi /. 4)) 0)))))
  (h10 : (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Ico (-(1 : ℝ)) 0))) → ((y x_1) < 0))))
  : (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Ico (-(1 : ℝ)) 0))) → (AntitoneOn y (Set.Ico (-(1 : ℝ)) 0)))) := by
  sorry

theorem proof_gap_exercise_181_8
  (y : (ℝ -> ℝ))
  (E_x : (Set ℝ))
  (x : ℝ)
  (h1 : E_x ⊆ (Set.univ : Set ℝ))
  (h2 : x ∈ (Set.univ : Set ℝ))
  (h3 : E_x = ({x_1 | (x_1 ∈ (Set.univ : Set ℝ)) ∧ ((0 < |(x_1)|) ∧ (|(x_1)| ≤ 1))}))
  (h4 : (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ E_x)) → ((y x_1) = ((1 : ℝ) /. (Real.tan ((Real.pi * x_1) /. 4)))))))
  (h5 : E_x = ((Set.Ico (-(1 : ℝ)) 0) ∪ (Set.Ioc 0 1)))
  (h6 : (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Ioc 0 1))) → (((Real.pi * x_1) /. 4) ∈ (Set.Ioc 0 (Real.pi /. 4))))))
  (h7 : (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Ioc 0 1))) → (AntitoneOn y (Set.Ioc 0 1)))))
  (h8 : (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Ioc 0 1))) → ((y '' (Set.Ioc 0 1)) = (Set.Ici 1)))))
  (h9 : (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Ico (-(1 : ℝ)) 0))) → (((Real.pi * x_1) /. 4) ∈ (Set.Ico (-(Real.pi /. 4)) 0)))))
  (h10 : (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Ico (-(1 : ℝ)) 0))) → ((y x_1) < 0))))
  (h11 : (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Ico (-(1 : ℝ)) 0))) → (AntitoneOn y (Set.Ico (-(1 : ℝ)) 0)))))
  : (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Ico (-(1 : ℝ)) 0))) → ((y '' (Set.Ico (-(1 : ℝ)) 0)) = (Set.Iic (-(1 : ℝ)))))) := by
  sorry

theorem proof_gap_exercise_181_9
  (y : (ℝ -> ℝ))
  (E_x : (Set ℝ))
  (x : ℝ)
  (h1 : E_x ⊆ (Set.univ : Set ℝ))
  (h2 : x ∈ (Set.univ : Set ℝ))
  (h3 : E_x = ({x_1 | (x_1 ∈ (Set.univ : Set ℝ)) ∧ ((0 < |(x_1)|) ∧ (|(x_1)| ≤ 1))}))
  (h4 : (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ E_x)) → ((y x_1) = ((1 : ℝ) /. (Real.tan ((Real.pi * x_1) /. 4)))))))
  (h5 : E_x = ((Set.Ico (-(1 : ℝ)) 0) ∪ (Set.Ioc 0 1)))
  (h6 : (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Ioc 0 1))) → (((Real.pi * x_1) /. 4) ∈ (Set.Ioc 0 (Real.pi /. 4))))))
  (h7 : (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Ioc 0 1))) → (AntitoneOn y (Set.Ioc 0 1)))))
  (h8 : (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Ioc 0 1))) → ((y '' (Set.Ioc 0 1)) = (Set.Ici 1)))))
  (h9 : (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Ico (-(1 : ℝ)) 0))) → (((Real.pi * x_1) /. 4) ∈ (Set.Ico (-(Real.pi /. 4)) 0)))))
  (h10 : (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Ico (-(1 : ℝ)) 0))) → ((y x_1) < 0))))
  (h11 : (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Ico (-(1 : ℝ)) 0))) → (AntitoneOn y (Set.Ico (-(1 : ℝ)) 0)))))
  (h12 : (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Ico (-(1 : ℝ)) 0))) → ((y '' (Set.Ico (-(1 : ℝ)) 0)) = (Set.Iic (-(1 : ℝ)))))))
  : (y '' E_x) = ((Set.Iic (-(1 : ℝ))) ∪ (Set.Ici 1)) := by
  sorry

theorem proof_gap_exercise_181_10
  (y : (ℝ -> ℝ))
  (E_x : (Set ℝ))
  (x : ℝ)
  (h1 : E_x ⊆ (Set.univ : Set ℝ))
  (h2 : x ∈ (Set.univ : Set ℝ))
  (h3 : E_x = ({x_1 | (x_1 ∈ (Set.univ : Set ℝ)) ∧ ((0 < |(x_1)|) ∧ (|(x_1)| ≤ 1))}))
  (h4 : (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ E_x)) → ((y x_1) = ((1 : ℝ) /. (Real.tan ((Real.pi * x_1) /. 4)))))))
  (h5 : E_x = ((Set.Ico (-(1 : ℝ)) 0) ∪ (Set.Ioc 0 1)))
  (h6 : (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Ioc 0 1))) → (((Real.pi * x_1) /. 4) ∈ (Set.Ioc 0 (Real.pi /. 4))))))
  (h7 : (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Ioc 0 1))) → (AntitoneOn y (Set.Ioc 0 1)))))
  (h8 : (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Ioc 0 1))) → ((y '' (Set.Ioc 0 1)) = (Set.Ici 1)))))
  (h9 : (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Ico (-(1 : ℝ)) 0))) → (((Real.pi * x_1) /. 4) ∈ (Set.Ico (-(Real.pi /. 4)) 0)))))
  (h10 : (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Ico (-(1 : ℝ)) 0))) → ((y x_1) < 0))))
  (h11 : (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Ico (-(1 : ℝ)) 0))) → (AntitoneOn y (Set.Ico (-(1 : ℝ)) 0)))))
  (h12 : (forall (x_1 : ℝ), (((x_1 ∈ (Set.univ : Set ℝ)) ∧ (x_1 ∈ (Set.Ico (-(1 : ℝ)) 0))) → ((y '' (Set.Ico (-(1 : ℝ)) 0)) = (Set.Iic (-(1 : ℝ)))))))
  (h13 : (y '' E_x) = ((Set.Iic (-(1 : ℝ))) ∪ (Set.Ici 1)))
  : (y '' E_x) = ({t | (t ∈ (Set.univ : Set ℝ)) ∧ (|(t)| ≥ 1)}) := by
  sorry
