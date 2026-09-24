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

-- exercise: exercise_3856

theorem proof_gap_exercise_3856_1
  (B : (ℝ × ℝ -> ℝ))
  (m : ℝ)
  (n : ℝ)
  (h1 : m ∈ (Set.univ : Set ℝ))
  (h2 : n ∈ (Set.univ : Set ℝ))
  (h3 : t = (Real.sin x))
  : 0 ≤ t := by
  sorry

theorem proof_gap_exercise_3856_2
  (B : (ℝ × ℝ -> ℝ))
  (m : ℝ)
  (n : ℝ)
  (h1 : m ∈ (Set.univ : Set ℝ))
  (h2 : n ∈ (Set.univ : Set ℝ))
  (h3 : t = (Real.sin x))
  (h4 : 0 ≤ t)
  : t ≤ 1 := by
  sorry

theorem proof_gap_exercise_3856_3
  (B : (ℝ × ℝ -> ℝ))
  (m : ℝ)
  (n : ℝ)
  (h1 : m ∈ (Set.univ : Set ℝ))
  (h2 : n ∈ (Set.univ : Set ℝ))
  (h3 : t = (Real.sin x))
  (h4 : 0 ≤ t)
  (h5 : t ≤ 1)
  (h6 : u = (t ^ (2 : ℕ)))
  : 0 ≤ u := by
  sorry

theorem proof_gap_exercise_3856_4
  (B : (ℝ × ℝ -> ℝ))
  (m : ℝ)
  (n : ℝ)
  (h1 : m ∈ (Set.univ : Set ℝ))
  (h2 : n ∈ (Set.univ : Set ℝ))
  (h3 : t = (Real.sin x))
  (h4 : 0 ≤ t)
  (h5 : t ≤ 1)
  (h6 : u = (t ^ (2 : ℕ)))
  (h7 : 0 ≤ u)
  : u ≤ 1 := by
  sorry

theorem proof_gap_exercise_3856_5
  (B : (ℝ × ℝ -> ℝ))
  (m : ℝ)
  (n : ℝ)
  (h1 : m ∈ (Set.univ : Set ℝ))
  (h2 : n ∈ (Set.univ : Set ℝ))
  (h3 : t = (Real.sin x))
  (h4 : 0 ≤ t)
  (h5 : t ≤ 1)
  (h6 : u = (t ^ (2 : ℕ)))
  (h7 : 0 ≤ u)
  (h8 : u ≤ 1)
  : (∫ x in (0 : ℝ)..(Real.pi /. 2), (((Real.rpow (Real.sin x) m) * (Real.rpow (Real.cos x) n)) * (1 : ℝ))) = (∫ t in (0 : ℝ)..(1 : ℝ), (((Real.rpow t m) * (Real.rpow (1 - (t ^ (2 : ℕ))) ((n - 1) /. 2))) * (1 : ℝ))) := by
  sorry

theorem proof_gap_exercise_3856_6
  (B : (ℝ × ℝ -> ℝ))
  (m : ℝ)
  (n : ℝ)
  (h1 : m ∈ (Set.univ : Set ℝ))
  (h2 : n ∈ (Set.univ : Set ℝ))
  (h3 : t = (Real.sin x))
  (h4 : 0 ≤ t)
  (h5 : t ≤ 1)
  (h6 : u = (t ^ (2 : ℕ)))
  (h7 : 0 ≤ u)
  (h8 : u ≤ 1)
  (h9 : (∫ x in (0 : ℝ)..(Real.pi /. 2), (((Real.rpow (Real.sin x) m) * (Real.rpow (Real.cos x) n)) * (1 : ℝ))) = (∫ t in (0 : ℝ)..(1 : ℝ), (((Real.rpow t m) * (Real.rpow (1 - (t ^ (2 : ℕ))) ((n - 1) /. 2))) * (1 : ℝ))))
  : (∫ t in (0 : ℝ)..(1 : ℝ), (((Real.rpow t m) * (Real.rpow (1 - (t ^ (2 : ℕ))) ((n - 1) /. 2))) * (1 : ℝ))) = ((1 /. 2) * (∫ u in (0 : ℝ)..(1 : ℝ), (((Real.rpow u ((m - 1) /. 2)) * (Real.rpow (1 - u) ((n - 1) /. 2))) * (1 : ℝ)))) := by
  sorry

theorem proof_gap_exercise_3856_7
  (B : (ℝ × ℝ -> ℝ))
  (m : ℝ)
  (n : ℝ)
  (h1 : m ∈ (Set.univ : Set ℝ))
  (h2 : n ∈ (Set.univ : Set ℝ))
  (h3 : t = (Real.sin x))
  (h4 : 0 ≤ t)
  (h5 : t ≤ 1)
  (h6 : u = (t ^ (2 : ℕ)))
  (h7 : 0 ≤ u)
  (h8 : u ≤ 1)
  (h9 : (∫ x in (0 : ℝ)..(Real.pi /. 2), (((Real.rpow (Real.sin x) m) * (Real.rpow (Real.cos x) n)) * (1 : ℝ))) = (∫ t in (0 : ℝ)..(1 : ℝ), (((Real.rpow t m) * (Real.rpow (1 - (t ^ (2 : ℕ))) ((n - 1) /. 2))) * (1 : ℝ))))
  (h10 : (∫ t in (0 : ℝ)..(1 : ℝ), (((Real.rpow t m) * (Real.rpow (1 - (t ^ (2 : ℕ))) ((n - 1) /. 2))) * (1 : ℝ))) = ((1 /. 2) * (∫ u in (0 : ℝ)..(1 : ℝ), (((Real.rpow u ((m - 1) /. 2)) * (Real.rpow (1 - u) ((n - 1) /. 2))) * (1 : ℝ)))))
  : ((1 /. 2) * (∫ u in (0 : ℝ)..(1 : ℝ), (((Real.rpow u ((m - 1) /. 2)) * (Real.rpow (1 - u) ((n - 1) /. 2))) * (1 : ℝ)))) = ((1 /. 2) * (B (((m + 1) /. 2), ((n + 1) /. 2)))) := by
  sorry

theorem proof_gap_exercise_3856_8
  (B : (ℝ × ℝ -> ℝ))
  (m : ℝ)
  (n : ℝ)
  (h1 : m ∈ (Set.univ : Set ℝ))
  (h2 : n ∈ (Set.univ : Set ℝ))
  (h3 : t = (Real.sin x))
  (h4 : 0 ≤ t)
  (h5 : t ≤ 1)
  (h6 : u = (t ^ (2 : ℕ)))
  (h7 : 0 ≤ u)
  (h8 : u ≤ 1)
  (h9 : (∫ x in (0 : ℝ)..(Real.pi /. 2), (((Real.rpow (Real.sin x) m) * (Real.rpow (Real.cos x) n)) * (1 : ℝ))) = (∫ t in (0 : ℝ)..(1 : ℝ), (((Real.rpow t m) * (Real.rpow (1 - (t ^ (2 : ℕ))) ((n - 1) /. 2))) * (1 : ℝ))))
  (h10 : (∫ t in (0 : ℝ)..(1 : ℝ), (((Real.rpow t m) * (Real.rpow (1 - (t ^ (2 : ℕ))) ((n - 1) /. 2))) * (1 : ℝ))) = ((1 /. 2) * (∫ u in (0 : ℝ)..(1 : ℝ), (((Real.rpow u ((m - 1) /. 2)) * (Real.rpow (1 - u) ((n - 1) /. 2))) * (1 : ℝ)))))
  (h11 : ((1 /. 2) * (∫ u in (0 : ℝ)..(1 : ℝ), (((Real.rpow u ((m - 1) /. 2)) * (Real.rpow (1 - u) ((n - 1) /. 2))) * (1 : ℝ)))) = ((1 /. 2) * (B (((m + 1) /. 2), ((n + 1) /. 2)))))
  : (∫ x in (0 : ℝ)..(Real.pi /. 2), (((Real.rpow (Real.sin x) m) * (Real.rpow (Real.cos x) n)) * (1 : ℝ))) = ((1 /. 2) * (B (((m + 1) /. 2), ((n + 1) /. 2)))) := by
  sorry

theorem proof_gap_exercise_3856_9
  (B : (ℝ × ℝ -> ℝ))
  (m : ℝ)
  (n : ℝ)
  (h1 : m ∈ (Set.univ : Set ℝ))
  (h2 : n ∈ (Set.univ : Set ℝ))
  (h3 : t = (Real.sin x))
  (h4 : 0 ≤ t)
  (h5 : t ≤ 1)
  (h6 : u = (t ^ (2 : ℕ)))
  (h7 : 0 ≤ u)
  (h8 : u ≤ 1)
  (h9 : (∫ x in (0 : ℝ)..(Real.pi /. 2), (((Real.rpow (Real.sin x) m) * (Real.rpow (Real.cos x) n)) * (1 : ℝ))) = (∫ t in (0 : ℝ)..(1 : ℝ), (((Real.rpow t m) * (Real.rpow (1 - (t ^ (2 : ℕ))) ((n - 1) /. 2))) * (1 : ℝ))))
  (h10 : (∫ t in (0 : ℝ)..(1 : ℝ), (((Real.rpow t m) * (Real.rpow (1 - (t ^ (2 : ℕ))) ((n - 1) /. 2))) * (1 : ℝ))) = ((1 /. 2) * (∫ u in (0 : ℝ)..(1 : ℝ), (((Real.rpow u ((m - 1) /. 2)) * (Real.rpow (1 - u) ((n - 1) /. 2))) * (1 : ℝ)))))
  (h11 : ((1 /. 2) * (∫ u in (0 : ℝ)..(1 : ℝ), (((Real.rpow u ((m - 1) /. 2)) * (Real.rpow (1 - u) ((n - 1) /. 2))) * (1 : ℝ)))) = ((1 /. 2) * (B (((m + 1) /. 2), ((n + 1) /. 2)))))
  (h12 : (∫ x in (0 : ℝ)..(Real.pi /. 2), (((Real.rpow (Real.sin x) m) * (Real.rpow (Real.cos x) n)) * (1 : ℝ))) = ((1 /. 2) * (B (((m + 1) /. 2), ((n + 1) /. 2)))))
  : m > (-(1 : ℝ)) := by
  sorry

theorem proof_gap_exercise_3856_10
  (B : (ℝ × ℝ -> ℝ))
  (m : ℝ)
  (n : ℝ)
  (h1 : m ∈ (Set.univ : Set ℝ))
  (h2 : n ∈ (Set.univ : Set ℝ))
  (h3 : t = (Real.sin x))
  (h4 : 0 ≤ t)
  (h5 : t ≤ 1)
  (h6 : u = (t ^ (2 : ℕ)))
  (h7 : 0 ≤ u)
  (h8 : u ≤ 1)
  (h9 : (∫ x in (0 : ℝ)..(Real.pi /. 2), (((Real.rpow (Real.sin x) m) * (Real.rpow (Real.cos x) n)) * (1 : ℝ))) = (∫ t in (0 : ℝ)..(1 : ℝ), (((Real.rpow t m) * (Real.rpow (1 - (t ^ (2 : ℕ))) ((n - 1) /. 2))) * (1 : ℝ))))
  (h10 : (∫ t in (0 : ℝ)..(1 : ℝ), (((Real.rpow t m) * (Real.rpow (1 - (t ^ (2 : ℕ))) ((n - 1) /. 2))) * (1 : ℝ))) = ((1 /. 2) * (∫ u in (0 : ℝ)..(1 : ℝ), (((Real.rpow u ((m - 1) /. 2)) * (Real.rpow (1 - u) ((n - 1) /. 2))) * (1 : ℝ)))))
  (h11 : ((1 /. 2) * (∫ u in (0 : ℝ)..(1 : ℝ), (((Real.rpow u ((m - 1) /. 2)) * (Real.rpow (1 - u) ((n - 1) /. 2))) * (1 : ℝ)))) = ((1 /. 2) * (B (((m + 1) /. 2), ((n + 1) /. 2)))))
  (h12 : (∫ x in (0 : ℝ)..(Real.pi /. 2), (((Real.rpow (Real.sin x) m) * (Real.rpow (Real.cos x) n)) * (1 : ℝ))) = ((1 /. 2) * (B (((m + 1) /. 2), ((n + 1) /. 2)))))
  (h13 : m > (-(1 : ℝ)))
  : n > (-(1 : ℝ)) := by
  sorry

theorem proof_gap_exercise_3856_11
  (B : (ℝ × ℝ -> ℝ))
  (m : ℝ)
  (n : ℝ)
  (h1 : m ∈ (Set.univ : Set ℝ))
  (h2 : n ∈ (Set.univ : Set ℝ))
  (h3 : t = (Real.sin x))
  (h4 : 0 ≤ t)
  (h5 : t ≤ 1)
  (h6 : u = (t ^ (2 : ℕ)))
  (h7 : 0 ≤ u)
  (h8 : u ≤ 1)
  (h9 : (∫ x in (0 : ℝ)..(Real.pi /. 2), (((Real.rpow (Real.sin x) m) * (Real.rpow (Real.cos x) n)) * (1 : ℝ))) = (∫ t in (0 : ℝ)..(1 : ℝ), (((Real.rpow t m) * (Real.rpow (1 - (t ^ (2 : ℕ))) ((n - 1) /. 2))) * (1 : ℝ))))
  (h10 : (∫ t in (0 : ℝ)..(1 : ℝ), (((Real.rpow t m) * (Real.rpow (1 - (t ^ (2 : ℕ))) ((n - 1) /. 2))) * (1 : ℝ))) = ((1 /. 2) * (∫ u in (0 : ℝ)..(1 : ℝ), (((Real.rpow u ((m - 1) /. 2)) * (Real.rpow (1 - u) ((n - 1) /. 2))) * (1 : ℝ)))))
  (h11 : ((1 /. 2) * (∫ u in (0 : ℝ)..(1 : ℝ), (((Real.rpow u ((m - 1) /. 2)) * (Real.rpow (1 - u) ((n - 1) /. 2))) * (1 : ℝ)))) = ((1 /. 2) * (B (((m + 1) /. 2), ((n + 1) /. 2)))))
  (h12 : (∫ x in (0 : ℝ)..(Real.pi /. 2), (((Real.rpow (Real.sin x) m) * (Real.rpow (Real.cos x) n)) * (1 : ℝ))) = ((1 /. 2) * (B (((m + 1) /. 2), ((n + 1) /. 2)))))
  (h13 : m > (-(1 : ℝ)))
  (h14 : n > (-(1 : ℝ)))
  : (∫ x in (0 : ℝ)..(Real.pi /. 2), (((Real.rpow (Real.sin x) m) * (Real.rpow (Real.cos x) n)) * (1 : ℝ))) = ((1 /. 2) * (B (((m + 1) /. 2), ((n + 1) /. 2)))) := by
  sorry

theorem proof_gap_exercise_3856_12
  (B : (ℝ × ℝ -> ℝ))
  (m : ℝ)
  (n : ℝ)
  (h1 : m ∈ (Set.univ : Set ℝ))
  (h2 : n ∈ (Set.univ : Set ℝ))
  (h3 : t = (Real.sin x))
  (h4 : 0 ≤ t)
  (h5 : t ≤ 1)
  (h6 : u = (t ^ (2 : ℕ)))
  (h7 : 0 ≤ u)
  (h8 : u ≤ 1)
  (h9 : (∫ x in (0 : ℝ)..(Real.pi /. 2), (((Real.rpow (Real.sin x) m) * (Real.rpow (Real.cos x) n)) * (1 : ℝ))) = (∫ t in (0 : ℝ)..(1 : ℝ), (((Real.rpow t m) * (Real.rpow (1 - (t ^ (2 : ℕ))) ((n - 1) /. 2))) * (1 : ℝ))))
  (h10 : (∫ t in (0 : ℝ)..(1 : ℝ), (((Real.rpow t m) * (Real.rpow (1 - (t ^ (2 : ℕ))) ((n - 1) /. 2))) * (1 : ℝ))) = ((1 /. 2) * (∫ u in (0 : ℝ)..(1 : ℝ), (((Real.rpow u ((m - 1) /. 2)) * (Real.rpow (1 - u) ((n - 1) /. 2))) * (1 : ℝ)))))
  (h11 : ((1 /. 2) * (∫ u in (0 : ℝ)..(1 : ℝ), (((Real.rpow u ((m - 1) /. 2)) * (Real.rpow (1 - u) ((n - 1) /. 2))) * (1 : ℝ)))) = ((1 /. 2) * (B (((m + 1) /. 2), ((n + 1) /. 2)))))
  (h12 : (∫ x in (0 : ℝ)..(Real.pi /. 2), (((Real.rpow (Real.sin x) m) * (Real.rpow (Real.cos x) n)) * (1 : ℝ))) = ((1 /. 2) * (B (((m + 1) /. 2), ((n + 1) /. 2)))))
  (h13 : m > (-(1 : ℝ)))
  (h14 : n > (-(1 : ℝ)))
  (h15 : (∫ x in (0 : ℝ)..(Real.pi /. 2), (((Real.rpow (Real.sin x) m) * (Real.rpow (Real.cos x) n)) * (1 : ℝ))) = ((1 /. 2) * (B (((m + 1) /. 2), ((n + 1) /. 2)))))
  : m > (-(1 : ℝ)) := by
  sorry

theorem proof_gap_exercise_3856_13
  (B : (ℝ × ℝ -> ℝ))
  (m : ℝ)
  (n : ℝ)
  (h1 : m ∈ (Set.univ : Set ℝ))
  (h2 : n ∈ (Set.univ : Set ℝ))
  (h3 : t = (Real.sin x))
  (h4 : 0 ≤ t)
  (h5 : t ≤ 1)
  (h6 : u = (t ^ (2 : ℕ)))
  (h7 : 0 ≤ u)
  (h8 : u ≤ 1)
  (h9 : (∫ x in (0 : ℝ)..(Real.pi /. 2), (((Real.rpow (Real.sin x) m) * (Real.rpow (Real.cos x) n)) * (1 : ℝ))) = (∫ t in (0 : ℝ)..(1 : ℝ), (((Real.rpow t m) * (Real.rpow (1 - (t ^ (2 : ℕ))) ((n - 1) /. 2))) * (1 : ℝ))))
  (h10 : (∫ t in (0 : ℝ)..(1 : ℝ), (((Real.rpow t m) * (Real.rpow (1 - (t ^ (2 : ℕ))) ((n - 1) /. 2))) * (1 : ℝ))) = ((1 /. 2) * (∫ u in (0 : ℝ)..(1 : ℝ), (((Real.rpow u ((m - 1) /. 2)) * (Real.rpow (1 - u) ((n - 1) /. 2))) * (1 : ℝ)))))
  (h11 : ((1 /. 2) * (∫ u in (0 : ℝ)..(1 : ℝ), (((Real.rpow u ((m - 1) /. 2)) * (Real.rpow (1 - u) ((n - 1) /. 2))) * (1 : ℝ)))) = ((1 /. 2) * (B (((m + 1) /. 2), ((n + 1) /. 2)))))
  (h12 : (∫ x in (0 : ℝ)..(Real.pi /. 2), (((Real.rpow (Real.sin x) m) * (Real.rpow (Real.cos x) n)) * (1 : ℝ))) = ((1 /. 2) * (B (((m + 1) /. 2), ((n + 1) /. 2)))))
  (h13 : m > (-(1 : ℝ)))
  (h14 : n > (-(1 : ℝ)))
  (h15 : (∫ x in (0 : ℝ)..(Real.pi /. 2), (((Real.rpow (Real.sin x) m) * (Real.rpow (Real.cos x) n)) * (1 : ℝ))) = ((1 /. 2) * (B (((m + 1) /. 2), ((n + 1) /. 2)))))
  (h16 : m > (-(1 : ℝ)))
  : n > (-(1 : ℝ)) := by
  sorry
