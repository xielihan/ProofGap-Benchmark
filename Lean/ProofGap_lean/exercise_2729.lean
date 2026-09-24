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

-- exercise: exercise_2729

theorem proof_gap_exercise_2729_1
  (b : (ℕ -> ℝ))
  (a : ℝ)
  (x : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : x ∈ (Set.univ : Set ℝ))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((b n) = ((1 /. (Real.rpow ((n)! : ℝ) (((n : ℝ))⁻¹))) * (1 /. (1 + ((a ^ (2 * n)) * (x ^ (2 : ℕ))))))))))
  : (x = 0) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((b n) = (1 /. (Real.rpow ((n)! : ℝ) (((n : ℝ))⁻¹)))))) := by
  sorry

theorem proof_gap_exercise_2729_2
  (b : (ℕ -> ℝ))
  (a : ℝ)
  (x : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : x ∈ (Set.univ : Set ℝ))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((b n) = ((1 /. (Real.rpow ((n)! : ℝ) (((n : ℝ))⁻¹))) * (1 /. (1 + ((a ^ (2 * n)) * (x ^ (2 : ℕ))))))))))
  (h4 : (x = 0) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((b n) = (1 /. (Real.rpow ((n)! : ℝ) (((n : ℝ))⁻¹)))))))
  : (x = 0) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (((b n) > (1 /. (Real.rpow ((n : ℝ) ^ n) (((n : ℝ))⁻¹)))) ∧ ((1 /. (Real.rpow ((n : ℝ) ^ n) (((n : ℝ))⁻¹))) = (1 /. n))))) := by
  sorry

theorem proof_gap_exercise_2729_3
  (b : (ℕ -> ℝ))
  (a : ℝ)
  (x : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : x ∈ (Set.univ : Set ℝ))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((b n) = ((1 /. (Real.rpow ((n)! : ℝ) (((n : ℝ))⁻¹))) * (1 /. (1 + ((a ^ (2 * n)) * (x ^ (2 : ℕ))))))))))
  (h4 : (x = 0) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((b n) = (1 /. (Real.rpow ((n)! : ℝ) (((n : ℝ))⁻¹)))))))
  (h5 : (x = 0) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (((b n) > (1 /. (Real.rpow ((n : ℝ) ^ n) (((n : ℝ))⁻¹)))) ∧ ((1 /. (Real.rpow ((n : ℝ) ^ n) (((n : ℝ))⁻¹))) = (1 /. n))))))
  : (x = 0) → (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (b n) else 0)) := by
  sorry

theorem proof_gap_exercise_2729_4
  (b : (ℕ -> ℝ))
  (a : ℝ)
  (x : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : x ∈ (Set.univ : Set ℝ))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((b n) = ((1 /. (Real.rpow ((n)! : ℝ) (((n : ℝ))⁻¹))) * (1 /. (1 + ((a ^ (2 * n)) * (x ^ (2 : ℕ))))))))))
  (h4 : (x = 0) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((b n) = (1 /. (Real.rpow ((n)! : ℝ) (((n : ℝ))⁻¹)))))))
  (h5 : (x = 0) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (((b n) > (1 /. (Real.rpow ((n : ℝ) ^ n) (((n : ℝ))⁻¹)))) ∧ ((1 /. (Real.rpow ((n : ℝ) ^ n) (((n : ℝ))⁻¹))) = (1 /. n))))))
  (h6 : (x = 0) → (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (b n) else 0)))
  : (x ≠ 0) → ((|(a)| > 1) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (((0 < (b n)) ∧ ((b n) < (1 /. ((a ^ (2 * n)) * (x ^ (2 : ℕ)))))) ∧ ((1 /. ((a ^ (2 * n)) * (x ^ (2 : ℕ)))) = ((1 /. (x ^ (2 : ℕ))) * ((1 /. |(a)|) ^ (2 * n)))))))) := by
  sorry

theorem proof_gap_exercise_2729_5
  (b : (ℕ -> ℝ))
  (a : ℝ)
  (x : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : x ∈ (Set.univ : Set ℝ))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((b n) = ((1 /. (Real.rpow ((n)! : ℝ) (((n : ℝ))⁻¹))) * (1 /. (1 + ((a ^ (2 * n)) * (x ^ (2 : ℕ))))))))))
  (h4 : (x = 0) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((b n) = (1 /. (Real.rpow ((n)! : ℝ) (((n : ℝ))⁻¹)))))))
  (h5 : (x = 0) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (((b n) > (1 /. (Real.rpow ((n : ℝ) ^ n) (((n : ℝ))⁻¹)))) ∧ ((1 /. (Real.rpow ((n : ℝ) ^ n) (((n : ℝ))⁻¹))) = (1 /. n))))))
  (h6 : (x = 0) → (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (b n) else 0)))
  (h7 : (x ≠ 0) → ((|(a)| > 1) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (((0 < (b n)) ∧ ((b n) < (1 /. ((a ^ (2 * n)) * (x ^ (2 : ℕ)))))) ∧ ((1 /. ((a ^ (2 * n)) * (x ^ (2 : ℕ)))) = ((1 /. (x ^ (2 : ℕ))) * ((1 /. |(a)|) ^ (2 * n)))))))))
  : (x ≠ 0) → ((|(a)| > 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ((1 /. (x ^ (2 : ℕ))) * ((1 /. |(a)|) ^ (2 * n))) else 0))) := by
  sorry

theorem proof_gap_exercise_2729_6
  (b : (ℕ -> ℝ))
  (a : ℝ)
  (x : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : x ∈ (Set.univ : Set ℝ))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((b n) = ((1 /. (Real.rpow ((n)! : ℝ) (((n : ℝ))⁻¹))) * (1 /. (1 + ((a ^ (2 * n)) * (x ^ (2 : ℕ))))))))))
  (h4 : (x = 0) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((b n) = (1 /. (Real.rpow ((n)! : ℝ) (((n : ℝ))⁻¹)))))))
  (h5 : (x = 0) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (((b n) > (1 /. (Real.rpow ((n : ℝ) ^ n) (((n : ℝ))⁻¹)))) ∧ ((1 /. (Real.rpow ((n : ℝ) ^ n) (((n : ℝ))⁻¹))) = (1 /. n))))))
  (h6 : (x = 0) → (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (b n) else 0)))
  (h7 : (x ≠ 0) → ((|(a)| > 1) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (((0 < (b n)) ∧ ((b n) < (1 /. ((a ^ (2 * n)) * (x ^ (2 : ℕ)))))) ∧ ((1 /. ((a ^ (2 * n)) * (x ^ (2 : ℕ)))) = ((1 /. (x ^ (2 : ℕ))) * ((1 /. |(a)|) ^ (2 * n)))))))))
  (h8 : (x ≠ 0) → ((|(a)| > 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ((1 /. (x ^ (2 : ℕ))) * ((1 /. |(a)|) ^ (2 * n))) else 0))))
  : (x ≠ 0) → ((|(a)| > 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((b n))‖ else 0))) := by
  sorry

theorem proof_gap_exercise_2729_7
  (b : (ℕ -> ℝ))
  (a : ℝ)
  (x : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : x ∈ (Set.univ : Set ℝ))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((b n) = ((1 /. (Real.rpow ((n)! : ℝ) (((n : ℝ))⁻¹))) * (1 /. (1 + ((a ^ (2 * n)) * (x ^ (2 : ℕ))))))))))
  (h4 : (x = 0) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((b n) = (1 /. (Real.rpow ((n)! : ℝ) (((n : ℝ))⁻¹)))))))
  (h5 : (x = 0) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (((b n) > (1 /. (Real.rpow ((n : ℝ) ^ n) (((n : ℝ))⁻¹)))) ∧ ((1 /. (Real.rpow ((n : ℝ) ^ n) (((n : ℝ))⁻¹))) = (1 /. n))))))
  (h6 : (x = 0) → (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (b n) else 0)))
  (h7 : (x ≠ 0) → ((|(a)| > 1) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (((0 < (b n)) ∧ ((b n) < (1 /. ((a ^ (2 * n)) * (x ^ (2 : ℕ)))))) ∧ ((1 /. ((a ^ (2 * n)) * (x ^ (2 : ℕ)))) = ((1 /. (x ^ (2 : ℕ))) * ((1 /. |(a)|) ^ (2 * n)))))))))
  (h8 : (x ≠ 0) → ((|(a)| > 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ((1 /. (x ^ (2 : ℕ))) * ((1 /. |(a)|) ^ (2 * n))) else 0))))
  (h9 : (x ≠ 0) → ((|(a)| > 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((b n))‖ else 0))))
  : (x ≠ 0) → ((|(a)| ≤ 1) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((|((b n))| ≥ ((1 /. (1 + (x ^ (2 : ℕ)))) * (1 /. (Real.rpow (n : ℝ) (((n : ℝ))⁻¹))))) ∧ (((1 /. (1 + (x ^ (2 : ℕ)))) * (1 /. (Real.rpow (n : ℝ) (((n : ℝ))⁻¹)))) > ((1 /. (1 + (x ^ (2 : ℕ)))) * (1 /. n))))))) := by
  sorry

theorem proof_gap_exercise_2729_8
  (b : (ℕ -> ℝ))
  (a : ℝ)
  (x : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : x ∈ (Set.univ : Set ℝ))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((b n) = ((1 /. (Real.rpow ((n)! : ℝ) (((n : ℝ))⁻¹))) * (1 /. (1 + ((a ^ (2 * n)) * (x ^ (2 : ℕ))))))))))
  (h4 : (x = 0) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((b n) = (1 /. (Real.rpow ((n)! : ℝ) (((n : ℝ))⁻¹)))))))
  (h5 : (x = 0) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (((b n) > (1 /. (Real.rpow ((n : ℝ) ^ n) (((n : ℝ))⁻¹)))) ∧ ((1 /. (Real.rpow ((n : ℝ) ^ n) (((n : ℝ))⁻¹))) = (1 /. n))))))
  (h6 : (x = 0) → (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (b n) else 0)))
  (h7 : (x ≠ 0) → ((|(a)| > 1) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (((0 < (b n)) ∧ ((b n) < (1 /. ((a ^ (2 * n)) * (x ^ (2 : ℕ)))))) ∧ ((1 /. ((a ^ (2 * n)) * (x ^ (2 : ℕ)))) = ((1 /. (x ^ (2 : ℕ))) * ((1 /. |(a)|) ^ (2 * n)))))))))
  (h8 : (x ≠ 0) → ((|(a)| > 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ((1 /. (x ^ (2 : ℕ))) * ((1 /. |(a)|) ^ (2 * n))) else 0))))
  (h9 : (x ≠ 0) → ((|(a)| > 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((b n))‖ else 0))))
  (h10 : (x ≠ 0) → ((|(a)| ≤ 1) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((|((b n))| ≥ ((1 /. (1 + (x ^ (2 : ℕ)))) * (1 /. (Real.rpow (n : ℝ) (((n : ℝ))⁻¹))))) ∧ (((1 /. (1 + (x ^ (2 : ℕ)))) * (1 /. (Real.rpow (n : ℝ) (((n : ℝ))⁻¹)))) > ((1 /. (1 + (x ^ (2 : ℕ)))) * (1 /. n))))))))
  : (x ≠ 0) → ((|(a)| ≤ 1) → (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (b n) else 0))) := by
  sorry

theorem proof_gap_exercise_2729_9
  (b : (ℕ -> ℝ))
  (a : ℝ)
  (x : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : x ∈ (Set.univ : Set ℝ))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((b n) = ((1 /. (Real.rpow ((n)! : ℝ) (((n : ℝ))⁻¹))) * (1 /. (1 + ((a ^ (2 * n)) * (x ^ (2 : ℕ))))))))))
  (h4 : (x = 0) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((b n) = (1 /. (Real.rpow ((n)! : ℝ) (((n : ℝ))⁻¹)))))))
  (h5 : (x = 0) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (((b n) > (1 /. (Real.rpow ((n : ℝ) ^ n) (((n : ℝ))⁻¹)))) ∧ ((1 /. (Real.rpow ((n : ℝ) ^ n) (((n : ℝ))⁻¹))) = (1 /. n))))))
  (h6 : (x = 0) → (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (b n) else 0)))
  (h7 : (x ≠ 0) → ((|(a)| > 1) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (((0 < (b n)) ∧ ((b n) < (1 /. ((a ^ (2 * n)) * (x ^ (2 : ℕ)))))) ∧ ((1 /. ((a ^ (2 * n)) * (x ^ (2 : ℕ)))) = ((1 /. (x ^ (2 : ℕ))) * ((1 /. |(a)|) ^ (2 * n)))))))))
  (h8 : (x ≠ 0) → ((|(a)| > 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ((1 /. (x ^ (2 : ℕ))) * ((1 /. |(a)|) ^ (2 * n))) else 0))))
  (h9 : (x ≠ 0) → ((|(a)| > 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((b n))‖ else 0))))
  (h10 : (x ≠ 0) → ((|(a)| ≤ 1) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((|((b n))| ≥ ((1 /. (1 + (x ^ (2 : ℕ)))) * (1 /. (Real.rpow (n : ℝ) (((n : ℝ))⁻¹))))) ∧ (((1 /. (1 + (x ^ (2 : ℕ)))) * (1 /. (Real.rpow (n : ℝ) (((n : ℝ))⁻¹)))) > ((1 /. (1 + (x ^ (2 : ℕ)))) * (1 /. n))))))))
  (h11 : (x ≠ 0) → ((|(a)| ≤ 1) → (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (b n) else 0))))
  : ((a, x) ∈ ({p : ℝ × ℝ | (p.1 ∈ (Set.univ : Set ℝ)) ∧ (p.2 ∈ (Set.univ : Set ℝ)) ∧ ((|(p.1)| > 1) ∧ (p.2 ≠ 0))})) ↔ (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (b n) else 0)) := by
  sorry
