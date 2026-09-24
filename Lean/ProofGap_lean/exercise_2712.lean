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

-- exercise: exercise_2712

theorem proof_gap_exercise_2712_1
  (q : ℝ)
  (h1 : q ∈ (Set.univ : Set ℝ))
  (h2 : |(q)| < 1)
  : Summable (fun (n : ℕ) => if (0 : ℕ) ≤ n then ‖((q ^ n))‖ else 0) := by
  sorry

theorem proof_gap_exercise_2712_2
  (q : ℝ)
  (h1 : q ∈ (Set.univ : Set ℝ))
  (h2 : |(q)| < 1)
  (h3 : Summable (fun (n : ℕ) => if (0 : ℕ) ≤ n then ‖((q ^ n))‖ else 0))
  (h4 : c = (fun (n : ℕ) => (∑ i ∈ Finset.Icc (0 : ℕ) n, ((q ^ i) * (q ^ (n - i))))))
  : ((∑' n, if (0 : ℕ) ≤ n then (q ^ n) else 0) ^ (2 : ℕ)) = (∑' n, if (0 : ℕ) ≤ n then (c n) else 0) := by
  sorry

theorem proof_gap_exercise_2712_3
  (q : ℝ)
  (h1 : q ∈ (Set.univ : Set ℝ))
  (h2 : |(q)| < 1)
  (h3 : Summable (fun (n : ℕ) => if (0 : ℕ) ≤ n then ‖((q ^ n))‖ else 0))
  (h4 : c = (fun (n : ℕ) => (∑ i ∈ Finset.Icc (0 : ℕ) n, ((q ^ i) * (q ^ (n - i))))))
  (h5 : ((∑' n, if (0 : ℕ) ≤ n then (q ^ n) else 0) ^ (2 : ℕ)) = (∑' n, if (0 : ℕ) ≤ n then (c n) else 0))
  : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → ((((c n) = (∑ i ∈ Finset.Icc (0 : ℕ) n, ((q ^ i) * (q ^ (n - i))))) ∧ ((∑ i ∈ Finset.Icc (0 : ℕ) n, ((q ^ i) * (q ^ (n - i)))) = ((q ^ n) * (∑ i ∈ Finset.Icc (0 : ℕ) n, 1)))) ∧ (((q ^ n) * (∑ i ∈ Finset.Icc (0 : ℕ) n, 1)) = ((n + 1) * (q ^ n)))))) := by
  sorry

theorem proof_gap_exercise_2712_4
  (q : ℝ)
  (h1 : q ∈ (Set.univ : Set ℝ))
  (h2 : |(q)| < 1)
  (h3 : Summable (fun (n : ℕ) => if (0 : ℕ) ≤ n then ‖((q ^ n))‖ else 0))
  (h4 : c = (fun (n : ℕ) => (∑ i ∈ Finset.Icc (0 : ℕ) n, ((q ^ i) * (q ^ (n - i))))))
  (h5 : ((∑' n, if (0 : ℕ) ≤ n then (q ^ n) else 0) ^ (2 : ℕ)) = (∑' n, if (0 : ℕ) ≤ n then (c n) else 0))
  (h6 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → ((((c n) = (∑ i ∈ Finset.Icc (0 : ℕ) n, ((q ^ i) * (q ^ (n - i))))) ∧ ((∑ i ∈ Finset.Icc (0 : ℕ) n, ((q ^ i) * (q ^ (n - i)))) = ((q ^ n) * (∑ i ∈ Finset.Icc (0 : ℕ) n, 1)))) ∧ (((q ^ n) * (∑ i ∈ Finset.Icc (0 : ℕ) n, 1)) = ((n + 1) * (q ^ n)))))))
  : ((∑' n, if (0 : ℕ) ≤ n then (q ^ n) else 0) ^ (2 : ℕ)) = (∑' n, if (0 : ℕ) ≤ n then ((n + 1) * (q ^ n)) else 0) := by
  sorry

theorem proof_gap_exercise_2712_5
  (q : ℝ)
  (h1 : q ∈ (Set.univ : Set ℝ))
  (h2 : |(q)| < 1)
  (h3 : Summable (fun (n : ℕ) => if (0 : ℕ) ≤ n then ‖((q ^ n))‖ else 0))
  (h4 : c = (fun (n : ℕ) => (∑ i ∈ Finset.Icc (0 : ℕ) n, ((q ^ i) * (q ^ (n - i))))))
  (h5 : ((∑' n, if (0 : ℕ) ≤ n then (q ^ n) else 0) ^ (2 : ℕ)) = (∑' n, if (0 : ℕ) ≤ n then (c n) else 0))
  (h6 : (forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) → ((((c n) = (∑ i ∈ Finset.Icc (0 : ℕ) n, ((q ^ i) * (q ^ (n - i))))) ∧ ((∑ i ∈ Finset.Icc (0 : ℕ) n, ((q ^ i) * (q ^ (n - i)))) = ((q ^ n) * (∑ i ∈ Finset.Icc (0 : ℕ) n, 1)))) ∧ (((q ^ n) * (∑ i ∈ Finset.Icc (0 : ℕ) n, 1)) = ((n + 1) * (q ^ n)))))))
  (h7 : ((∑' n, if (0 : ℕ) ≤ n then (q ^ n) else 0) ^ (2 : ℕ)) = (∑' n, if (0 : ℕ) ≤ n then ((n + 1) * (q ^ n)) else 0))
  : ((∑' n, if (0 : ℕ) ≤ n then (q ^ n) else 0) ^ (2 : ℕ)) = (∑' n, if (0 : ℕ) ≤ n then ((n + 1) * (q ^ n)) else 0) := by
  sorry
