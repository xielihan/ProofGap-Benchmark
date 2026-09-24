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

-- exercise: exercise_1188

theorem proof_gap_exercise_1188_1
  (y : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (c : ℝ)
  (d : ℝ)
  (n : ℕ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : c ∈ (Set.univ : Set ℝ))
  (h4 : d ∈ (Set.univ : Set ℝ))
  (h5 : n ∈ (Set.univ : Set ℕ))
  (h6 : c ≠ 0)
  (h7 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  (h8 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ (-(d /. c)))) → ((y x) = (((a * x) + b) /. ((c * x) + d))))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ (-(d /. c)))) → ((iteratedDeriv 1 (fun t => y t) x) = (((a * ((c * x) + d)) - (c * ((a * x) + b))) /. (((c * x) + d) ^ (2 : ℕ)))))) := by
  sorry

theorem proof_gap_exercise_1188_2
  (y : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (c : ℝ)
  (d : ℝ)
  (n : ℕ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : c ∈ (Set.univ : Set ℝ))
  (h4 : d ∈ (Set.univ : Set ℝ))
  (h5 : n ∈ (Set.univ : Set ℕ))
  (h6 : c ≠ 0)
  (h7 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  (h8 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ (-(d /. c)))) → ((y x) = (((a * x) + b) /. ((c * x) + d))))))
  (h9 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ (-(d /. c)))) → ((iteratedDeriv 1 (fun t => y t) x) = (((a * ((c * x) + d)) - (c * ((a * x) + b))) /. (((c * x) + d) ^ (2 : ℕ)))))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ (-(d /. c)))) → ((((a * ((c * x) + d)) - (c * ((a * x) + b))) /. (((c * x) + d) ^ (2 : ℕ))) = (((a * d) - (b * c)) /. (((c * x) + d) ^ (2 : ℕ)))))) := by
  sorry

theorem proof_gap_exercise_1188_3
  (y : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (c : ℝ)
  (d : ℝ)
  (n : ℕ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : c ∈ (Set.univ : Set ℝ))
  (h4 : d ∈ (Set.univ : Set ℝ))
  (h5 : n ∈ (Set.univ : Set ℕ))
  (h6 : c ≠ 0)
  (h7 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  (h8 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ (-(d /. c)))) → ((y x) = (((a * x) + b) /. ((c * x) + d))))))
  (h9 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ (-(d /. c)))) → ((iteratedDeriv 1 (fun t => y t) x) = (((a * ((c * x) + d)) - (c * ((a * x) + b))) /. (((c * x) + d) ^ (2 : ℕ)))))))
  (h10 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ (-(d /. c)))) → ((((a * ((c * x) + d)) - (c * ((a * x) + b))) /. (((c * x) + d) ^ (2 : ℕ))) = (((a * d) - (b * c)) /. (((c * x) + d) ^ (2 : ℕ)))))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ (-(d /. c)))) → ((iteratedDeriv 1 (fun t => y t) x) = (((a * d) - (b * c)) /. (((c * x) + d) ^ (2 : ℕ)))))) := by
  sorry

theorem proof_gap_exercise_1188_4
  (y : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (c : ℝ)
  (d : ℝ)
  (n : ℕ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : c ∈ (Set.univ : Set ℝ))
  (h4 : d ∈ (Set.univ : Set ℝ))
  (h5 : n ∈ (Set.univ : Set ℕ))
  (h6 : c ≠ 0)
  (h7 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  (h8 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ (-(d /. c)))) → ((y x) = (((a * x) + b) /. ((c * x) + d))))))
  (h9 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ (-(d /. c)))) → ((iteratedDeriv 1 (fun t => y t) x) = (((a * ((c * x) + d)) - (c * ((a * x) + b))) /. (((c * x) + d) ^ (2 : ℕ)))))))
  (h10 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ (-(d /. c)))) → ((((a * ((c * x) + d)) - (c * ((a * x) + b))) /. (((c * x) + d) ^ (2 : ℕ))) = (((a * d) - (b * c)) /. (((c * x) + d) ^ (2 : ℕ)))))))
  (h11 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ (-(d /. c)))) → ((iteratedDeriv 1 (fun t => y t) x) = (((a * d) - (b * c)) /. (((c * x) + d) ^ (2 : ℕ)))))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ (-(d /. c)))) → ((iteratedDeriv 2 (fun t => y t) x) = (-(((2 * c) * ((a * d) - (b * c))) /. (((c * x) + d) ^ (3 : ℕ))))))) := by
  sorry

theorem proof_gap_exercise_1188_5
  (y : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (c : ℝ)
  (d : ℝ)
  (n : ℕ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : c ∈ (Set.univ : Set ℝ))
  (h4 : d ∈ (Set.univ : Set ℝ))
  (h5 : n ∈ (Set.univ : Set ℕ))
  (h6 : c ≠ 0)
  (h7 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  (h8 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ (-(d /. c)))) → ((y x) = (((a * x) + b) /. ((c * x) + d))))))
  (h9 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ (-(d /. c)))) → ((iteratedDeriv 1 (fun t => y t) x) = (((a * ((c * x) + d)) - (c * ((a * x) + b))) /. (((c * x) + d) ^ (2 : ℕ)))))))
  (h10 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ (-(d /. c)))) → ((((a * ((c * x) + d)) - (c * ((a * x) + b))) /. (((c * x) + d) ^ (2 : ℕ))) = (((a * d) - (b * c)) /. (((c * x) + d) ^ (2 : ℕ)))))))
  (h11 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ (-(d /. c)))) → ((iteratedDeriv 1 (fun t => y t) x) = (((a * d) - (b * c)) /. (((c * x) + d) ^ (2 : ℕ)))))))
  (h12 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ (-(d /. c)))) → ((iteratedDeriv 2 (fun t => y t) x) = (-(((2 * c) * ((a * d) - (b * c))) /. (((c * x) + d) ^ (3 : ℕ))))))))
  : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ (-(d /. c)))) ∧ (n = 2)) → ((iteratedDeriv n (fun t => y t) x) = ((((((-(1 : ℤ)) ^ (n - 1)) * (c ^ (n - 1))) * ((a * d) - (b * c))) * (n)!) /. (((c * x) + d) ^ (n + 1)))))) := by
  sorry

theorem proof_gap_exercise_1188_6
  (y : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (c : ℝ)
  (d : ℝ)
  (n : ℕ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : c ∈ (Set.univ : Set ℝ))
  (h4 : d ∈ (Set.univ : Set ℝ))
  (h5 : n ∈ (Set.univ : Set ℕ))
  (h6 : c ≠ 0)
  (h7 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  (h8 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ (-(d /. c)))) → ((y x) = (((a * x) + b) /. ((c * x) + d))))))
  (h9 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ (-(d /. c)))) → ((iteratedDeriv 1 (fun t => y t) x) = (((a * ((c * x) + d)) - (c * ((a * x) + b))) /. (((c * x) + d) ^ (2 : ℕ)))))))
  (h10 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ (-(d /. c)))) → ((((a * ((c * x) + d)) - (c * ((a * x) + b))) /. (((c * x) + d) ^ (2 : ℕ))) = (((a * d) - (b * c)) /. (((c * x) + d) ^ (2 : ℕ)))))))
  (h11 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ (-(d /. c)))) → ((iteratedDeriv 1 (fun t => y t) x) = (((a * d) - (b * c)) /. (((c * x) + d) ^ (2 : ℕ)))))))
  (h12 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ (-(d /. c)))) → ((iteratedDeriv 2 (fun t => y t) x) = (-(((2 * c) * ((a * d) - (b * c))) /. (((c * x) + d) ^ (3 : ℕ))))))))
  (h13 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ (-(d /. c)))) ∧ (n = 2)) → ((iteratedDeriv n (fun t => y t) x) = ((((((-(1 : ℤ)) ^ (n - 1)) * (c ^ (n - 1))) * ((a * d) - (b * c))) * (n)!) /. (((c * x) + d) ^ (n + 1)))))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ (-(d /. c)))) → (forall (k : ℕ), (((((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (k ≥ 2)) ∧ ((iteratedDeriv k (fun t => y t) x) = ((((((-(1 : ℤ)) ^ (k - 1)) * (c ^ (k - 1))) * ((a * d) - (b * c))) * (k)!) /. (((c * x) + d) ^ (k + 1))))) → ((iteratedDeriv (k + 1) (fun t => y t) x) = ((((((((-((-(1 : ℝ)) ^ (k - 1))) * (c ^ (k - 1))) * ((a * d) - (b * c))) * (k)!) * (k + 1)) * (((c * x) + d) ^ k)) * c) /. (((c * x) + d) ^ (2 * (k + 1))))))))) := by
  sorry

theorem proof_gap_exercise_1188_7
  (y : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (c : ℝ)
  (d : ℝ)
  (n : ℕ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : c ∈ (Set.univ : Set ℝ))
  (h4 : d ∈ (Set.univ : Set ℝ))
  (h5 : n ∈ (Set.univ : Set ℕ))
  (h6 : c ≠ 0)
  (h7 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  (h8 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ (-(d /. c)))) → ((y x) = (((a * x) + b) /. ((c * x) + d))))))
  (h9 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ (-(d /. c)))) → ((iteratedDeriv 1 (fun t => y t) x) = (((a * ((c * x) + d)) - (c * ((a * x) + b))) /. (((c * x) + d) ^ (2 : ℕ)))))))
  (h10 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ (-(d /. c)))) → ((((a * ((c * x) + d)) - (c * ((a * x) + b))) /. (((c * x) + d) ^ (2 : ℕ))) = (((a * d) - (b * c)) /. (((c * x) + d) ^ (2 : ℕ)))))))
  (h11 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ (-(d /. c)))) → ((iteratedDeriv 1 (fun t => y t) x) = (((a * d) - (b * c)) /. (((c * x) + d) ^ (2 : ℕ)))))))
  (h12 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ (-(d /. c)))) → ((iteratedDeriv 2 (fun t => y t) x) = (-(((2 * c) * ((a * d) - (b * c))) /. (((c * x) + d) ^ (3 : ℕ))))))))
  (h13 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ (-(d /. c)))) ∧ (n = 2)) → ((iteratedDeriv n (fun t => y t) x) = ((((((-(1 : ℤ)) ^ (n - 1)) * (c ^ (n - 1))) * ((a * d) - (b * c))) * (n)!) /. (((c * x) + d) ^ (n + 1)))))))
  (h14 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ (-(d /. c)))) → (forall (k : ℕ), (((((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (k ≥ 2)) ∧ ((iteratedDeriv k (fun t => y t) x) = ((((((-(1 : ℤ)) ^ (k - 1)) * (c ^ (k - 1))) * ((a * d) - (b * c))) * (k)!) /. (((c * x) + d) ^ (k + 1))))) → ((iteratedDeriv (k + 1) (fun t => y t) x) = ((((((((-((-(1 : ℝ)) ^ (k - 1))) * (c ^ (k - 1))) * ((a * d) - (b * c))) * (k)!) * (k + 1)) * (((c * x) + d) ^ k)) * c) /. (((c * x) + d) ^ (2 * (k + 1))))))))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ (-(d /. c)))) → (forall (k : ℕ), (((((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (k ≥ 2)) ∧ ((iteratedDeriv k (fun t => y t) x) = ((((((-(1 : ℤ)) ^ (k - 1)) * (c ^ (k - 1))) * ((a * d) - (b * c))) * (k)!) /. (((c * x) + d) ^ (k + 1))))) → ((iteratedDeriv (k + 1) (fun t => y t) x) = ((((((-(1 : ℤ)) ^ ((k + 1) - 1)) * (c ^ ((k + 1) - 1))) * ((a * d) - (b * c))) * ((k + 1))!) /. (((c * x) + d) ^ ((k + 1) + 1)))))))) := by
  sorry

theorem proof_gap_exercise_1188_8
  (y : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (c : ℝ)
  (d : ℝ)
  (n : ℕ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : c ∈ (Set.univ : Set ℝ))
  (h4 : d ∈ (Set.univ : Set ℝ))
  (h5 : n ∈ (Set.univ : Set ℕ))
  (h6 : c ≠ 0)
  (h7 : n ∈ ({n_1 : ℕ | 0 < n_1}))
  (h8 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ (-(d /. c)))) → ((y x) = (((a * x) + b) /. ((c * x) + d))))))
  (h9 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ (-(d /. c)))) → ((iteratedDeriv 1 (fun t => y t) x) = (((a * ((c * x) + d)) - (c * ((a * x) + b))) /. (((c * x) + d) ^ (2 : ℕ)))))))
  (h10 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ (-(d /. c)))) → ((((a * ((c * x) + d)) - (c * ((a * x) + b))) /. (((c * x) + d) ^ (2 : ℕ))) = (((a * d) - (b * c)) /. (((c * x) + d) ^ (2 : ℕ)))))))
  (h11 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ (-(d /. c)))) → ((iteratedDeriv 1 (fun t => y t) x) = (((a * d) - (b * c)) /. (((c * x) + d) ^ (2 : ℕ)))))))
  (h12 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ (-(d /. c)))) → ((iteratedDeriv 2 (fun t => y t) x) = (-(((2 * c) * ((a * d) - (b * c))) /. (((c * x) + d) ^ (3 : ℕ))))))))
  (h13 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ (-(d /. c)))) ∧ (n = 2)) → ((iteratedDeriv n (fun t => y t) x) = ((((((-(1 : ℤ)) ^ (n - 1)) * (c ^ (n - 1))) * ((a * d) - (b * c))) * (n)!) /. (((c * x) + d) ^ (n + 1)))))))
  (h14 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ (-(d /. c)))) → (forall (k : ℕ), (((((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (k ≥ 2)) ∧ ((iteratedDeriv k (fun t => y t) x) = ((((((-(1 : ℤ)) ^ (k - 1)) * (c ^ (k - 1))) * ((a * d) - (b * c))) * (k)!) /. (((c * x) + d) ^ (k + 1))))) → ((iteratedDeriv (k + 1) (fun t => y t) x) = ((((((((-((-(1 : ℝ)) ^ (k - 1))) * (c ^ (k - 1))) * ((a * d) - (b * c))) * (k)!) * (k + 1)) * (((c * x) + d) ^ k)) * c) /. (((c * x) + d) ^ (2 * (k + 1))))))))))
  (h15 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ (-(d /. c)))) → (forall (k : ℕ), (((((k ∈ (Set.univ : Set ℕ)) ∧ (k ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (k ≥ 2)) ∧ ((iteratedDeriv k (fun t => y t) x) = ((((((-(1 : ℤ)) ^ (k - 1)) * (c ^ (k - 1))) * ((a * d) - (b * c))) * (k)!) /. (((c * x) + d) ^ (k + 1))))) → ((iteratedDeriv (k + 1) (fun t => y t) x) = ((((((-(1 : ℤ)) ^ ((k + 1) - 1)) * (c ^ ((k + 1) - 1))) * ((a * d) - (b * c))) * ((k + 1))!) /. (((c * x) + d) ^ ((k + 1) + 1)))))))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ (-(d /. c)))) → ((iteratedDeriv n (fun t => y t) x) = ((((((-(1 : ℤ)) ^ (n - 1)) * (c ^ (n - 1))) * ((a * d) - (b * c))) * (n)!) /. (((c * x) + d) ^ (n + 1)))))) := by
  sorry
