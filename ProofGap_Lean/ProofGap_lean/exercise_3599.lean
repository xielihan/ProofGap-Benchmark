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

-- exercise: exercise_3599

theorem proof_gap_exercise_3599_1
  (f : (ℝ × ℝ -> ℝ))
  (h1 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((f (x, y)) = (Real.sin ((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))))))))
  : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((Real.sin ((x ^ (2 : ℕ)) + (y ^ (2 : ℕ)))) = (∑' n, if (0 : ℕ) ≤ n then (((-(1 : ℤ)) ^ n) * ((((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) ^ ((2 * n) + 1)) /. (((2 * n) + 1))!)) else 0)))) := by
  sorry

theorem proof_gap_exercise_3599_2
  (f : (ℝ × ℝ -> ℝ))
  (h1 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((f (x, y)) = (Real.sin ((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))))))))
  (h2 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((Real.sin ((x ^ (2 : ℕ)) + (y ^ (2 : ℕ)))) = (∑' n, if (0 : ℕ) ≤ n then (((-(1 : ℤ)) ^ n) * ((((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) ^ ((2 * n) + 1)) /. (((2 * n) + 1))!)) else 0)))))
  : (forall (x : ℝ) (y : ℝ) (n : ℕ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (n ∈ (Set.univ : Set ℕ))) → ((((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) ^ ((2 * n) + 1)) = (∑ k ∈ Finset.Icc (0 : ℕ) ((2 * n) + 1), ((((((2 * n) + 1))! * (x ^ (2 * k))) * (y ^ (2 * (((2 * n) + 1) - k)))) /. ((k)! * ((((2 * n) + 1) - k))!)))))) := by
  sorry

theorem proof_gap_exercise_3599_3
  (f : (ℝ × ℝ -> ℝ))
  (h1 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((f (x, y)) = (Real.sin ((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))))))))
  (h2 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((Real.sin ((x ^ (2 : ℕ)) + (y ^ (2 : ℕ)))) = (∑' n, if (0 : ℕ) ≤ n then (((-(1 : ℤ)) ^ n) * ((((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) ^ ((2 * n) + 1)) /. (((2 * n) + 1))!)) else 0)))))
  (h3 : (forall (x : ℝ) (y : ℝ) (n : ℕ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (n ∈ (Set.univ : Set ℕ))) → ((((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) ^ ((2 * n) + 1)) = (∑ k ∈ Finset.Icc (0 : ℕ) ((2 * n) + 1), ((((((2 * n) + 1))! * (x ^ (2 * k))) * (y ^ (2 * (((2 * n) + 1) - k)))) /. ((k)! * ((((2 * n) + 1) - k))!)))))))
  : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((f (x, y)) = (∑' n, if (0 : ℕ) ≤ n then (∑ k ∈ Finset.Icc (0 : ℕ) ((2 * n) + 1), (((-(1 : ℤ)) ^ n) * (((x ^ (2 * k)) * (y ^ (2 * (((2 * n) + 1) - k)))) /. ((k)! * ((((2 * n) + 1) - k))!)))) else 0)))) := by
  sorry

theorem proof_gap_exercise_3599_4
  (f : (ℝ × ℝ -> ℝ))
  (h1 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((f (x, y)) = (Real.sin ((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))))))))
  (h2 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((Real.sin ((x ^ (2 : ℕ)) + (y ^ (2 : ℕ)))) = (∑' n, if (0 : ℕ) ≤ n then (((-(1 : ℤ)) ^ n) * ((((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) ^ ((2 * n) + 1)) /. (((2 * n) + 1))!)) else 0)))))
  (h3 : (forall (x : ℝ) (y : ℝ) (n : ℕ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (n ∈ (Set.univ : Set ℕ))) → ((((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) ^ ((2 * n) + 1)) = (∑ k ∈ Finset.Icc (0 : ℕ) ((2 * n) + 1), ((((((2 * n) + 1))! * (x ^ (2 * k))) * (y ^ (2 * (((2 * n) + 1) - k)))) /. ((k)! * ((((2 * n) + 1) - k))!)))))))
  (h4 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((f (x, y)) = (∑' n, if (0 : ℕ) ≤ n then (∑ k ∈ Finset.Icc (0 : ℕ) ((2 * n) + 1), (((-(1 : ℤ)) ^ n) * (((x ^ (2 * k)) * (y ^ (2 * (((2 * n) + 1) - k)))) /. ((k)! * ((((2 * n) + 1) - k))!)))) else 0)))))
  : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((f (x, y)) = (∑' n, if (0 : ℕ) ≤ n then (∑ k ∈ Finset.Icc (0 : ℕ) ((2 * n) + 1), (((-(1 : ℤ)) ^ n) * (((x ^ (2 * k)) * (y ^ (2 * (((2 * n) + 1) - k)))) /. ((k)! * ((((2 * n) + 1) - k))!)))) else 0)))) := by
  sorry

theorem proof_gap_exercise_3599_5
  (f : (ℝ × ℝ -> ℝ))
  (h1 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((f (x, y)) = (Real.sin ((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))))))))
  (h2 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((Real.sin ((x ^ (2 : ℕ)) + (y ^ (2 : ℕ)))) = (∑' n, if (0 : ℕ) ≤ n then (((-(1 : ℤ)) ^ n) * ((((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) ^ ((2 * n) + 1)) /. (((2 * n) + 1))!)) else 0)))))
  (h3 : (forall (x : ℝ) (y : ℝ) (n : ℕ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (n ∈ (Set.univ : Set ℕ))) → ((((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) ^ ((2 * n) + 1)) = (∑ k ∈ Finset.Icc (0 : ℕ) ((2 * n) + 1), ((((((2 * n) + 1))! * (x ^ (2 * k))) * (y ^ (2 * (((2 * n) + 1) - k)))) /. ((k)! * ((((2 * n) + 1) - k))!)))))))
  (h4 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((f (x, y)) = (∑' n, if (0 : ℕ) ≤ n then (∑ k ∈ Finset.Icc (0 : ℕ) ((2 * n) + 1), (((-(1 : ℤ)) ^ n) * (((x ^ (2 * k)) * (y ^ (2 * (((2 * n) + 1) - k)))) /. ((k)! * ((((2 * n) + 1) - k))!)))) else 0)))))
  (h5 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((f (x, y)) = (∑' n, if (0 : ℕ) ≤ n then (∑ k ∈ Finset.Icc (0 : ℕ) ((2 * n) + 1), (((-(1 : ℤ)) ^ n) * (((x ^ (2 * k)) * (y ^ (2 * (((2 * n) + 1) - k)))) /. ((k)! * ((((2 * n) + 1) - k))!)))) else 0)))))
  : (forall (x : ℝ), (x ∈ (Set.univ : Set ℝ))) := by
  sorry

theorem proof_gap_exercise_3599_6
  (f : (ℝ × ℝ -> ℝ))
  (h1 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((f (x, y)) = (Real.sin ((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))))))))
  (h2 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((Real.sin ((x ^ (2 : ℕ)) + (y ^ (2 : ℕ)))) = (∑' n, if (0 : ℕ) ≤ n then (((-(1 : ℤ)) ^ n) * ((((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) ^ ((2 * n) + 1)) /. (((2 * n) + 1))!)) else 0)))))
  (h3 : (forall (x : ℝ) (y : ℝ) (n : ℕ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) ∧ (n ∈ (Set.univ : Set ℕ))) → ((((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) ^ ((2 * n) + 1)) = (∑ k ∈ Finset.Icc (0 : ℕ) ((2 * n) + 1), ((((((2 * n) + 1))! * (x ^ (2 * k))) * (y ^ (2 * (((2 * n) + 1) - k)))) /. ((k)! * ((((2 * n) + 1) - k))!)))))))
  (h4 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((f (x, y)) = (∑' n, if (0 : ℕ) ≤ n then (∑ k ∈ Finset.Icc (0 : ℕ) ((2 * n) + 1), (((-(1 : ℤ)) ^ n) * (((x ^ (2 * k)) * (y ^ (2 * (((2 * n) + 1) - k)))) /. ((k)! * ((((2 * n) + 1) - k))!)))) else 0)))))
  (h5 : (forall (x : ℝ) (y : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) → ((f (x, y)) = (∑' n, if (0 : ℕ) ≤ n then (∑ k ∈ Finset.Icc (0 : ℕ) ((2 * n) + 1), (((-(1 : ℤ)) ^ n) * (((x ^ (2 * k)) * (y ^ (2 * (((2 * n) + 1) - k)))) /. ((k)! * ((((2 * n) + 1) - k))!)))) else 0)))))
  (h6 : (forall (x : ℝ), (x ∈ (Set.univ : Set ℝ))))
  : (forall (y : ℝ), (y ∈ (Set.univ : Set ℝ))) := by
  sorry
