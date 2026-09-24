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

-- exercise: exercise_2693

theorem proof_gap_exercise_2693_1
  (a : (ℕ -> ℝ))
  (p : ℝ)
  (q : ℝ)
  (h1 : p ∈ (Set.univ : Set ℝ))
  (h2 : q ∈ (Set.univ : Set ℝ))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = (if (Odd n) then (1 /. (Real.rpow (n : ℝ) p)) else (if (Even n) then (-(1 /. (Real.rpow (n : ℝ) q))) else (-(1 /. (Real.rpow (n : ℝ) q)))))))))
  : (p > 1) → ((q > 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((a n))‖ else 0))) := by
  sorry

theorem proof_gap_exercise_2693_2
  (a : (ℕ -> ℝ))
  (p : ℝ)
  (q : ℝ)
  (h1 : p ∈ (Set.univ : Set ℝ))
  (h2 : q ∈ (Set.univ : Set ℝ))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = (if (Odd n) then (1 /. (Real.rpow (n : ℝ) p)) else (if (Even n) then (-(1 /. (Real.rpow (n : ℝ) q))) else (-(1 /. (Real.rpow (n : ℝ) q)))))))))
  (h4 : (p > 1) → ((q > 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((a n))‖ else 0))))
  : (p > 1) → ((q > 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (a n) else 0))) := by
  sorry

theorem proof_gap_exercise_2693_3
  (a : (ℕ -> ℝ))
  (p : ℝ)
  (q : ℝ)
  (h1 : p ∈ (Set.univ : Set ℝ))
  (h2 : q ∈ (Set.univ : Set ℝ))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = (if (Odd n) then (1 /. (Real.rpow (n : ℝ) p)) else (if (Even n) then (-(1 /. (Real.rpow (n : ℝ) q))) else (-(1 /. (Real.rpow (n : ℝ) q)))))))))
  (h4 : (p > 1) → ((q > 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((a n))‖ else 0))))
  (h5 : (p > 1) → ((q > 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (a n) else 0))))
  : (0 < p) → ((p = q) → ((q ≤ 1) → (Not (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((a n))‖ else 0))))) := by
  sorry

theorem proof_gap_exercise_2693_4
  (a : (ℕ -> ℝ))
  (p : ℝ)
  (q : ℝ)
  (h1 : p ∈ (Set.univ : Set ℝ))
  (h2 : q ∈ (Set.univ : Set ℝ))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = (if (Odd n) then (1 /. (Real.rpow (n : ℝ) p)) else (if (Even n) then (-(1 /. (Real.rpow (n : ℝ) q))) else (-(1 /. (Real.rpow (n : ℝ) q)))))))))
  (h4 : (p > 1) → ((q > 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((a n))‖ else 0))))
  (h5 : (p > 1) → ((q > 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (a n) else 0))))
  (h6 : (0 < p) → ((p = q) → ((q ≤ 1) → (Not (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((a n))‖ else 0))))))
  : (0 < p) → ((p = q) → ((q ≤ 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (a n) else 0)))) := by
  sorry

theorem proof_gap_exercise_2693_5
  (a : (ℕ -> ℝ))
  (p : ℝ)
  (q : ℝ)
  (h1 : p ∈ (Set.univ : Set ℝ))
  (h2 : q ∈ (Set.univ : Set ℝ))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = (if (Odd n) then (1 /. (Real.rpow (n : ℝ) p)) else (if (Even n) then (-(1 /. (Real.rpow (n : ℝ) q))) else (-(1 /. (Real.rpow (n : ℝ) q)))))))))
  (h4 : (p > 1) → ((q > 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((a n))‖ else 0))))
  (h5 : (p > 1) → ((q > 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (a n) else 0))))
  (h6 : (0 < p) → ((p = q) → ((q ≤ 1) → (Not (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((a n))‖ else 0))))))
  (h7 : (0 < p) → ((p = q) → ((q ≤ 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (a n) else 0)))))
  : (0 < p) → ((p = q) → ((q ≤ 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (a n) else 0) ∧ ¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((a n))‖ else 0)))) := by
  sorry

theorem proof_gap_exercise_2693_6
  (a : (ℕ -> ℝ))
  (p : ℝ)
  (q : ℝ)
  (h1 : p ∈ (Set.univ : Set ℝ))
  (h2 : q ∈ (Set.univ : Set ℝ))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = (if (Odd n) then (1 /. (Real.rpow (n : ℝ) p)) else (if (Even n) then (-(1 /. (Real.rpow (n : ℝ) q))) else (-(1 /. (Real.rpow (n : ℝ) q)))))))))
  (h4 : (p > 1) → ((q > 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((a n))‖ else 0))))
  (h5 : (p > 1) → ((q > 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (a n) else 0))))
  (h6 : (0 < p) → ((p = q) → ((q ≤ 1) → (Not (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((a n))‖ else 0))))))
  (h7 : (0 < p) → ((p = q) → ((q ≤ 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (a n) else 0)))))
  (h8 : (0 < p) → ((p = q) → ((q ≤ 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (a n) else 0) ∧ ¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((a n))‖ else 0)))))
  : ((p ≤ 0) ∨ (q ≤ 0)) → (∃ L : ℝ, Tendsto (fun n : ℕ => (a n)) atTop (𝓝 L) ∧ (atTop.limUnder (fun n : ℕ => (a n)) ≠ 0)) := by
  sorry

theorem proof_gap_exercise_2693_7
  (a : (ℕ -> ℝ))
  (p : ℝ)
  (q : ℝ)
  (h1 : p ∈ (Set.univ : Set ℝ))
  (h2 : q ∈ (Set.univ : Set ℝ))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = (if (Odd n) then (1 /. (Real.rpow (n : ℝ) p)) else (if (Even n) then (-(1 /. (Real.rpow (n : ℝ) q))) else (-(1 /. (Real.rpow (n : ℝ) q)))))))))
  (h4 : (p > 1) → ((q > 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((a n))‖ else 0))))
  (h5 : (p > 1) → ((q > 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (a n) else 0))))
  (h6 : (0 < p) → ((p = q) → ((q ≤ 1) → (Not (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((a n))‖ else 0))))))
  (h7 : (0 < p) → ((p = q) → ((q ≤ 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (a n) else 0)))))
  (h8 : (0 < p) → ((p = q) → ((q ≤ 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (a n) else 0) ∧ ¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((a n))‖ else 0)))))
  (h9 : ((p ≤ 0) ∨ (q ≤ 0)) → (atTop.limUnder (fun n : ℕ => (a n)) ≠ 0))
  (h10 : ∃ L : ℝ, Tendsto (fun n : ℕ => (a n)) atTop (𝓝 L))
  : ((p ≤ 0) ∨ (q ≤ 0)) → (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (a n) else 0)) := by
  sorry

theorem proof_gap_exercise_2693_8
  (a : (ℕ -> ℝ))
  (p : ℝ)
  (q : ℝ)
  (h1 : p ∈ (Set.univ : Set ℝ))
  (h2 : q ∈ (Set.univ : Set ℝ))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = (if (Odd n) then (1 /. (Real.rpow (n : ℝ) p)) else (if (Even n) then (-(1 /. (Real.rpow (n : ℝ) q))) else (-(1 /. (Real.rpow (n : ℝ) q)))))))))
  (h4 : (p > 1) → ((q > 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((a n))‖ else 0))))
  (h5 : (p > 1) → ((q > 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (a n) else 0))))
  (h6 : (0 < p) → ((p = q) → ((q ≤ 1) → (Not (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((a n))‖ else 0))))))
  (h7 : (0 < p) → ((p = q) → ((q ≤ 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (a n) else 0)))))
  (h8 : (0 < p) → ((p = q) → ((q ≤ 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (a n) else 0) ∧ ¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((a n))‖ else 0)))))
  (h9 : ((p ≤ 0) ∨ (q ≤ 0)) → (atTop.limUnder (fun n : ℕ => (a n)) ≠ 0))
  (h10 : ((p ≤ 0) ∨ (q ≤ 0)) → (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (a n) else 0)))
  (h11 : ∃ L : ℝ, Tendsto (fun n : ℕ => (a n)) atTop (𝓝 L))
  : (p > 0) → ((q > 0) → ((Not ((p > 1) ∧ (q > 1))) → ((p ≠ q) → (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (a n) else 0))))) := by
  sorry

theorem proof_gap_exercise_2693_9
  (a : (ℕ -> ℝ))
  (p : ℝ)
  (q : ℝ)
  (h1 : p ∈ (Set.univ : Set ℝ))
  (h2 : q ∈ (Set.univ : Set ℝ))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = (if (Odd n) then (1 /. (Real.rpow (n : ℝ) p)) else (if (Even n) then (-(1 /. (Real.rpow (n : ℝ) q))) else (-(1 /. (Real.rpow (n : ℝ) q)))))))))
  (h4 : (p > 1) → ((q > 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((a n))‖ else 0))))
  (h5 : (p > 1) → ((q > 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (a n) else 0))))
  (h6 : (0 < p) → ((p = q) → ((q ≤ 1) → (Not (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((a n))‖ else 0))))))
  (h7 : (0 < p) → ((p = q) → ((q ≤ 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (a n) else 0)))))
  (h8 : (0 < p) → ((p = q) → ((q ≤ 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (a n) else 0) ∧ ¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((a n))‖ else 0)))))
  (h9 : ((p ≤ 0) ∨ (q ≤ 0)) → (atTop.limUnder (fun n : ℕ => (a n)) ≠ 0))
  (h10 : ((p ≤ 0) ∨ (q ≤ 0)) → (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (a n) else 0)))
  (h11 : (p > 0) → ((q > 0) → ((Not ((p > 1) ∧ (q > 1))) → ((p ≠ q) → (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (a n) else 0))))))
  (h12 : ∃ L : ℝ, Tendsto (fun n : ℕ => (a n)) atTop (𝓝 L))
  : (((((p > 1) ∧ (q > 1)) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((a n))‖ else 0))) ∧ ((((0 < p) ∧ (p = q)) ∧ (q ≤ 1)) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (a n) else 0) ∧ ¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((a n))‖ else 0)))) ∧ ((((p ≤ 0) ∨ (q ≤ 0)) ∨ ((((p > 0) ∧ (q > 0)) ∧ (Not ((p > 1) ∧ (q > 1)))) ∧ (p ≠ q))) → (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (a n) else 0)))) ↔ ((Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (a n) else 0)) ∧ (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (a n) else 0))) := by
  sorry
