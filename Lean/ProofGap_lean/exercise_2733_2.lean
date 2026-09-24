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

-- exercise: exercise_2733_2

theorem proof_gap_exercise_2733_2_1
  (a : (ℕ -> ℝ))
  (x : ℝ)
  (y : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (y ∈ (Set.univ : Set ℝ)) ∧ (y ∈ ({x_1 : ℝ | 0 <= x_1})))
  (h3 : x = 1)
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = ((x ^ n) /. (n + (y ^ n)))))))
  : (y > 1) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((|((a n))| = (1 /. (n + (y ^ n)))) ∧ ((1 /. (n + (y ^ n))) < ((1 /. y) ^ n))))) := by
  sorry

theorem proof_gap_exercise_2733_2_2
  (a : (ℕ -> ℝ))
  (x : ℝ)
  (y : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (y ∈ (Set.univ : Set ℝ)) ∧ (y ∈ ({x_1 : ℝ | 0 <= x_1})))
  (h3 : x = 1)
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = ((x ^ n) /. (n + (y ^ n)))))))
  (h5 : (y > 1) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((|((a n))| = (1 /. (n + (y ^ n)))) ∧ ((1 /. (n + (y ^ n))) < ((1 /. y) ^ n))))))
  : (y > 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ((1 /. y) ^ n) else 0)) := by
  sorry

theorem proof_gap_exercise_2733_2_3
  (a : (ℕ -> ℝ))
  (x : ℝ)
  (y : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (y ∈ (Set.univ : Set ℝ)) ∧ (y ∈ ({x_1 : ℝ | 0 <= x_1})))
  (h3 : x = 1)
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = ((x ^ n) /. (n + (y ^ n)))))))
  (h5 : (y > 1) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((|((a n))| = (1 /. (n + (y ^ n)))) ∧ ((1 /. (n + (y ^ n))) < ((1 /. y) ^ n))))))
  (h6 : (y > 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ((1 /. y) ^ n) else 0)))
  : (y > 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((a n))‖ else 0)) := by
  sorry

theorem proof_gap_exercise_2733_2_4
  (a : (ℕ -> ℝ))
  (x : ℝ)
  (y : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (y ∈ (Set.univ : Set ℝ)) ∧ (y ∈ ({x_1 : ℝ | 0 <= x_1})))
  (h3 : x = 1)
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = ((x ^ n) /. (n + (y ^ n)))))))
  (h5 : (y > 1) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((|((a n))| = (1 /. (n + (y ^ n)))) ∧ ((1 /. (n + (y ^ n))) < ((1 /. y) ^ n))))))
  (h6 : (y > 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ((1 /. y) ^ n) else 0)))
  (h7 : (y > 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((a n))‖ else 0)))
  : (0 ≤ y) → ((y ≤ 1) → (∃ L : ℝ, Tendsto (fun n : ℕ => (n /. (n + (Real.rpow y n)))) atTop (𝓝 L) ∧ (Tendsto (fun n : ℕ => ((a n) /. (1 /. n))) atTop (𝓝 (atTop.limUnder (fun n : ℕ => (n /. (n + (Real.rpow y n))))))))) := by
  sorry

theorem proof_gap_exercise_2733_2_5
  (a : (ℕ -> ℝ))
  (x : ℝ)
  (y : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (y ∈ (Set.univ : Set ℝ)) ∧ (y ∈ ({x_1 : ℝ | 0 <= x_1})))
  (h3 : x = 1)
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = ((x ^ n) /. (n + (y ^ n)))))))
  (h5 : (y > 1) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((|((a n))| = (1 /. (n + (y ^ n)))) ∧ ((1 /. (n + (y ^ n))) < ((1 /. y) ^ n))))))
  (h6 : (y > 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ((1 /. y) ^ n) else 0)))
  (h7 : (y > 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((a n))‖ else 0)))
  (h8 : (0 ≤ y) → ((y ≤ 1) → (Tendsto (fun n : ℕ => ((a n) /. (1 /. n))) atTop (𝓝 (atTop.limUnder (fun n : ℕ => (n /. (n + (Real.rpow y n)))))))))
  (h9 : ∃ L : ℝ, Tendsto (fun n : ℕ => (n /. (n + (Real.rpow y n)))) atTop (𝓝 L))
  : (0 ≤ y) → ((y ≤ 1) → (Tendsto (fun n : ℕ => (n /. (n + (Real.rpow y n)))) atTop (𝓝 1))) := by
  sorry

theorem proof_gap_exercise_2733_2_6
  (a : (ℕ -> ℝ))
  (x : ℝ)
  (y : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (y ∈ (Set.univ : Set ℝ)) ∧ (y ∈ ({x_1 : ℝ | 0 <= x_1})))
  (h3 : x = 1)
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = ((x ^ n) /. (n + (y ^ n)))))))
  (h5 : (y > 1) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((|((a n))| = (1 /. (n + (y ^ n)))) ∧ ((1 /. (n + (y ^ n))) < ((1 /. y) ^ n))))))
  (h6 : (y > 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ((1 /. y) ^ n) else 0)))
  (h7 : (y > 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((a n))‖ else 0)))
  (h8 : (0 ≤ y) → ((y ≤ 1) → (Tendsto (fun n : ℕ => ((a n) /. (1 /. n))) atTop (𝓝 (atTop.limUnder (fun n : ℕ => (n /. (n + (Real.rpow y n)))))))))
  (h9 : (0 ≤ y) → ((y ≤ 1) → (Tendsto (fun n : ℕ => (n /. (n + (Real.rpow y n)))) atTop (𝓝 1))))
  (h10 : ∃ L : ℝ, Tendsto (fun n : ℕ => (n /. (n + (Real.rpow y n)))) atTop (𝓝 L))
  : (0 ≤ y) → ((y ≤ 1) → (Tendsto (fun n : ℕ => ((a n) /. (1 /. n))) atTop (𝓝 1))) := by
  sorry

theorem proof_gap_exercise_2733_2_7
  (a : (ℕ -> ℝ))
  (x : ℝ)
  (y : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (y ∈ (Set.univ : Set ℝ)) ∧ (y ∈ ({x_1 : ℝ | 0 <= x_1})))
  (h3 : x = 1)
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = ((x ^ n) /. (n + (y ^ n)))))))
  (h5 : (y > 1) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((|((a n))| = (1 /. (n + (y ^ n)))) ∧ ((1 /. (n + (y ^ n))) < ((1 /. y) ^ n))))))
  (h6 : (y > 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ((1 /. y) ^ n) else 0)))
  (h7 : (y > 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((a n))‖ else 0)))
  (h8 : (0 ≤ y) → ((y ≤ 1) → (Tendsto (fun n : ℕ => ((a n) /. (1 /. n))) atTop (𝓝 (atTop.limUnder (fun n : ℕ => (n /. (n + (Real.rpow y n)))))))))
  (h9 : (0 ≤ y) → ((y ≤ 1) → (Tendsto (fun n : ℕ => (n /. (n + (Real.rpow y n)))) atTop (𝓝 1))))
  (h10 : (0 ≤ y) → ((y ≤ 1) → (Tendsto (fun n : ℕ => ((a n) /. (1 /. n))) atTop (𝓝 1))))
  (h11 : ∃ L : ℝ, Tendsto (fun n : ℕ => (n /. (n + (Real.rpow y n)))) atTop (𝓝 L))
  : (0 ≤ y) → ((y ≤ 1) → (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (1 /. n) else 0))) := by
  sorry

theorem proof_gap_exercise_2733_2_8
  (a : (ℕ -> ℝ))
  (x : ℝ)
  (y : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (y ∈ (Set.univ : Set ℝ)) ∧ (y ∈ ({x_1 : ℝ | 0 <= x_1})))
  (h3 : x = 1)
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = ((x ^ n) /. (n + (y ^ n)))))))
  (h5 : (y > 1) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((|((a n))| = (1 /. (n + (y ^ n)))) ∧ ((1 /. (n + (y ^ n))) < ((1 /. y) ^ n))))))
  (h6 : (y > 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ((1 /. y) ^ n) else 0)))
  (h7 : (y > 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((a n))‖ else 0)))
  (h8 : (0 ≤ y) → ((y ≤ 1) → (Tendsto (fun n : ℕ => ((a n) /. (1 /. n))) atTop (𝓝 (atTop.limUnder (fun n : ℕ => (n /. (n + (Real.rpow y n)))))))))
  (h9 : (0 ≤ y) → ((y ≤ 1) → (Tendsto (fun n : ℕ => (n /. (n + (Real.rpow y n)))) atTop (𝓝 1))))
  (h10 : (0 ≤ y) → ((y ≤ 1) → (Tendsto (fun n : ℕ => ((a n) /. (1 /. n))) atTop (𝓝 1))))
  (h11 : (0 ≤ y) → ((y ≤ 1) → (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (1 /. n) else 0))))
  (h12 : ∃ L : ℝ, Tendsto (fun n : ℕ => (n /. (n + (Real.rpow y n)))) atTop (𝓝 L))
  : (0 ≤ y) → ((y ≤ 1) → (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (a n) else 0))) := by
  sorry

theorem proof_gap_exercise_2733_2_9
  (a : (ℕ -> ℝ))
  (x : ℝ)
  (y : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : (y ∈ (Set.univ : Set ℝ)) ∧ (y ∈ ({x_1 : ℝ | 0 <= x_1})))
  (h3 : x = 1)
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = ((x ^ n) /. (n + (y ^ n)))))))
  (h5 : (y > 1) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((|((a n))| = (1 /. (n + (y ^ n)))) ∧ ((1 /. (n + (y ^ n))) < ((1 /. y) ^ n))))))
  (h6 : (y > 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ((1 /. y) ^ n) else 0)))
  (h7 : (y > 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((a n))‖ else 0)))
  (h8 : (0 ≤ y) → ((y ≤ 1) → (Tendsto (fun n : ℕ => ((a n) /. (1 /. n))) atTop (𝓝 (atTop.limUnder (fun n : ℕ => (n /. (n + (Real.rpow y n)))))))))
  (h9 : (0 ≤ y) → ((y ≤ 1) → (Tendsto (fun n : ℕ => (n /. (n + (Real.rpow y n)))) atTop (𝓝 1))))
  (h10 : (0 ≤ y) → ((y ≤ 1) → (Tendsto (fun n : ℕ => ((a n) /. (1 /. n))) atTop (𝓝 1))))
  (h11 : (0 ≤ y) → ((y ≤ 1) → (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (1 /. n) else 0))))
  (h12 : (0 ≤ y) → ((y ≤ 1) → (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (a n) else 0))))
  (h13 : ∃ L : ℝ, Tendsto (fun n : ℕ => (n /. (n + (Real.rpow y n)))) atTop (𝓝 L))
  : (y ∈ ({y_1 | (y_1 ∈ (Set.univ : Set ℝ)) ∧ (y_1 > 1)})) ↔ (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (a n) else 0)) := by
  sorry
