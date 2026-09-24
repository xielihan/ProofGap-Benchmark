import Mathlib

set_option linter.style.longLine false

open scoped BigOperators Topology Nat

open Filter

open scoped RealInnerProductSpace

noncomputable def lpFunDeri {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] (f g : E -> ℝ) : E -> ℝ :=
  fun x => (inner ℝ (gradient f x) (gradient g x)) / (‖gradient g x‖ ^ 2)

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

-- exercise: exercise_2791

theorem proof_gap_exercise_2791_1
  (a : (ℕ -> ℝ))
  (S : (ℕ × ℝ -> ℝ))
  (n : ℕ)
  (h1 : True)
  (h2 : n ∈ (Set.univ : Set ℕ))
  (h3 : Summable (fun (n_1 : ℕ) => if (1 : ℕ) ≤ n_1 then (a n_1) else 0))
  (h4 : S = (fun p : ℕ × ℝ => ∑ n_1 ∈ Finset.Icc (1 : ℕ) p.1, ((a n_1) * (Real.exp (-(n_1 * p.2))))))
  : (forall (n_1 : ℕ) (x : ℝ), (((((n_1 ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ (x ∈ (Set.Ici 0))) → ((0 < (Real.exp (-(n_1 * x)))) ∧ ((Real.exp (-(n_1 * x))) ≤ 1)))) := by
  sorry

theorem proof_gap_exercise_2791_2
  (a : (ℕ -> ℝ))
  (S : (ℕ × ℝ -> ℝ))
  (n : ℕ)
  (h1 : True)
  (h2 : n ∈ (Set.univ : Set ℕ))
  (h3 : Summable (fun (n_1 : ℕ) => if (1 : ℕ) ≤ n_1 then (a n_1) else 0))
  (h4 : S = (fun p : ℕ × ℝ => ∑ n_1 ∈ Finset.Icc (1 : ℕ) p.1, ((a n_1) * (Real.exp (-(n_1 * p.2))))))
  (h5 : (forall (n_1 : ℕ) (x : ℝ), (((((n_1 ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ (x ∈ (Set.Ici 0))) → ((0 < (Real.exp (-(n_1 * x)))) ∧ ((Real.exp (-(n_1 * x))) ≤ 1)))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Ici 0))) → (Antitone (fun (n_1 : ℕ) => (Real.exp (-(n_1 * x))))))) := by
  sorry

theorem proof_gap_exercise_2791_3
  (a : (ℕ -> ℝ))
  (S : (ℕ × ℝ -> ℝ))
  (n : ℕ)
  (h1 : True)
  (h2 : n ∈ (Set.univ : Set ℕ))
  (h3 : Summable (fun (n_1 : ℕ) => if (1 : ℕ) ≤ n_1 then (a n_1) else 0))
  (h4 : S = (fun p : ℕ × ℝ => ∑ n_1 ∈ Finset.Icc (1 : ℕ) p.1, ((a n_1) * (Real.exp (-(n_1 * p.2))))))
  (h5 : (forall (n_1 : ℕ) (x : ℝ), (((((n_1 ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ (x ∈ (Set.Ici 0))) → ((0 < (Real.exp (-(n_1 * x)))) ∧ ((Real.exp (-(n_1 * x))) ≤ 1)))))
  (h6 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Ici 0))) → (Antitone (fun (n_1 : ℕ) => (Real.exp (-(n_1 * x))))))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Ici 0))) → (Summable (fun (n_1 : ℕ) => if (1 : ℕ) ≤ n_1 then (a n_1) else 0)))) := by
  sorry

theorem proof_gap_exercise_2791_4
  (a : (ℕ -> ℝ))
  (S : (ℕ × ℝ -> ℝ))
  (n : ℕ)
  (h1 : True)
  (h2 : n ∈ (Set.univ : Set ℕ))
  (h3 : Summable (fun (n_1 : ℕ) => if (1 : ℕ) ≤ n_1 then (a n_1) else 0))
  (h4 : S = (fun p : ℕ × ℝ => ∑ n_1 ∈ Finset.Icc (1 : ℕ) p.1, ((a n_1) * (Real.exp (-(n_1 * p.2))))))
  (h5 : (forall (n_1 : ℕ) (x : ℝ), (((((n_1 ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ (x ∈ (Set.Ici 0))) → ((0 < (Real.exp (-(n_1 * x)))) ∧ ((Real.exp (-(n_1 * x))) ≤ 1)))))
  (h6 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Ici 0))) → (Antitone (fun (n_1 : ℕ) => (Real.exp (-(n_1 * x))))))))
  (h7 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Ici 0))) → (Summable (fun (n_1 : ℕ) => if (1 : ℕ) ≤ n_1 then (a n_1) else 0)))))
  : TendstoUniformlyOn (fun N x_1 => S (N, x_1)) (fun (x_1 : ℝ) => (∑' n_1, if (1 : ℕ) ≤ n_1 then ((a n_1) * (Real.exp (-(n_1 * x_1)))) else 0)) Filter.atTop (Set.Ici 0) := by
  sorry

theorem proof_gap_exercise_2791_5
  (a : (ℕ -> ℝ))
  (S : (ℕ × ℝ -> ℝ))
  (n : ℕ)
  (h1 : True)
  (h2 : n ∈ (Set.univ : Set ℕ))
  (h3 : Summable (fun (n_1 : ℕ) => if (1 : ℕ) ≤ n_1 then (a n_1) else 0))
  (h4 : S = (fun p : ℕ × ℝ => ∑ n_1 ∈ Finset.Icc (1 : ℕ) p.1, ((a n_1) * (Real.exp (-(n_1 * p.2))))))
  (h5 : (forall (n_1 : ℕ) (x : ℝ), (((((n_1 ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (n_1 ∈ ({n_2 : ℕ | 0 < n_2}))) ∧ (x ∈ (Set.Ici 0))) → ((0 < (Real.exp (-(n_1 * x)))) ∧ ((Real.exp (-(n_1 * x))) ≤ 1)))))
  (h6 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Ici 0))) → (Antitone (fun (n_1 : ℕ) => (Real.exp (-(n_1 * x))))))))
  (h7 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Ici 0))) → (Summable (fun (n_1 : ℕ) => if (1 : ℕ) ≤ n_1 then (a n_1) else 0)))))
  (h8 : TendstoUniformlyOn (fun N x_1 => S (N, x_1)) (fun (x_1 : ℝ) => (∑' n_1, if (1 : ℕ) ≤ n_1 then ((a n_1) * (Real.exp (-(n_1 * x_1)))) else 0)) Filter.atTop (Set.Ici 0))
  : TendstoUniformlyOn (fun N x_1 => S (N, x_1)) (fun (x_1 : ℝ) => (∑' n_1, if (1 : ℕ) ≤ n_1 then ((a n_1) * (Real.exp (-(n_1 * x_1)))) else 0)) Filter.atTop (Set.Ici 0) := by
  sorry
