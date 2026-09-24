import Mathlib

attribute [local instance] Classical.propDecidable

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

-- exercise: exercise_3097

theorem proof_gap_exercise_3097_1
  (p : (ℕ -> ℝ))
  (q : (ℕ -> ℝ))
  (v_uCE_uB2 : (ℕ -> ℝ))
  (v_uCE_uB3 : (ℕ -> ℝ))
  (v_uCE_uB1 : ℝ)
  (h1 : v_uCE_uB1 ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((q n) = (if (exists (k : ℕ), ((k ∈ (Set.univ : Set ℕ)) ∧ ((n = ((3 * k) + 1)) ∨ (n = ((3 * k) + 3))))) then (1 + (1 /. (Real.rpow (n : ℝ) v_uCE_uB1))) else (if (exists (k : ℕ), ((k ∈ (Set.univ : Set ℕ)) ∧ (n = ((3 * k) + 2)))) then ((1 - (1 /. (Real.rpow (n : ℝ) v_uCE_uB1))) ^ (2 : ℕ)) else ((1 - (1 /. (Real.rpow (n : ℝ) v_uCE_uB1))) ^ (2 : ℕ))))))))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((q n) = (1 + (v_uCE_uB2 n))))))
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((p n) = (1 + (v_uCE_uB3 n))))))
  : (v_uCE_uB1 > 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then |((v_uCE_uB2 n))| else 0)) := by
  sorry

theorem proof_gap_exercise_3097_2
  (p : (ℕ -> ℝ))
  (q : (ℕ -> ℝ))
  (v_uCE_uB2 : (ℕ -> ℝ))
  (v_uCE_uB3 : (ℕ -> ℝ))
  (v_uCE_uB1 : ℝ)
  (h1 : v_uCE_uB1 ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((q n) = (if (exists (k : ℕ), ((k ∈ (Set.univ : Set ℕ)) ∧ ((n = ((3 * k) + 1)) ∨ (n = ((3 * k) + 3))))) then (1 + (1 /. (Real.rpow (n : ℝ) v_uCE_uB1))) else (if (exists (k : ℕ), ((k ∈ (Set.univ : Set ℕ)) ∧ (n = ((3 * k) + 2)))) then ((1 - (1 /. (Real.rpow (n : ℝ) v_uCE_uB1))) ^ (2 : ℕ)) else ((1 - (1 /. (Real.rpow (n : ℝ) v_uCE_uB1))) ^ (2 : ℕ))))))))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((q n) = (1 + (v_uCE_uB2 n))))))
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((p n) = (1 + (v_uCE_uB3 n))))))
  (h5 : (v_uCE_uB1 > 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then |((v_uCE_uB2 n))| else 0)))
  : (v_uCE_uB1 > 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((Real.log (q n)))‖ else 0)) := by
  sorry

theorem proof_gap_exercise_3097_3
  (p : (ℕ -> ℝ))
  (q : (ℕ -> ℝ))
  (v_uCE_uB2 : (ℕ -> ℝ))
  (v_uCE_uB3 : (ℕ -> ℝ))
  (v_uCE_uB1 : ℝ)
  (h1 : v_uCE_uB1 ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((q n) = (if (exists (k : ℕ), ((k ∈ (Set.univ : Set ℕ)) ∧ ((n = ((3 * k) + 1)) ∨ (n = ((3 * k) + 3))))) then (1 + (1 /. (Real.rpow (n : ℝ) v_uCE_uB1))) else (if (exists (k : ℕ), ((k ∈ (Set.univ : Set ℕ)) ∧ (n = ((3 * k) + 2)))) then ((1 - (1 /. (Real.rpow (n : ℝ) v_uCE_uB1))) ^ (2 : ℕ)) else ((1 - (1 /. (Real.rpow (n : ℝ) v_uCE_uB1))) ^ (2 : ℕ))))))))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((q n) = (1 + (v_uCE_uB2 n))))))
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((p n) = (1 + (v_uCE_uB3 n))))))
  (h5 : (v_uCE_uB1 > 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then |((v_uCE_uB2 n))| else 0)))
  (h6 : (v_uCE_uB1 > 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((Real.log (q n)))‖ else 0)))
  : (v_uCE_uB1 ≤ 0) → (Not (Filter.Tendsto q Filter.atTop (𝓝 1))) := by
  sorry

theorem proof_gap_exercise_3097_4
  (p : (ℕ -> ℝ))
  (q : (ℕ -> ℝ))
  (v_uCE_uB2 : (ℕ -> ℝ))
  (v_uCE_uB3 : (ℕ -> ℝ))
  (v_uCE_uB1 : ℝ)
  (h1 : v_uCE_uB1 ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((q n) = (if (exists (k : ℕ), ((k ∈ (Set.univ : Set ℕ)) ∧ ((n = ((3 * k) + 1)) ∨ (n = ((3 * k) + 3))))) then (1 + (1 /. (Real.rpow (n : ℝ) v_uCE_uB1))) else (if (exists (k : ℕ), ((k ∈ (Set.univ : Set ℕ)) ∧ (n = ((3 * k) + 2)))) then ((1 - (1 /. (Real.rpow (n : ℝ) v_uCE_uB1))) ^ (2 : ℕ)) else ((1 - (1 /. (Real.rpow (n : ℝ) v_uCE_uB1))) ^ (2 : ℕ))))))))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((q n) = (1 + (v_uCE_uB2 n))))))
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((p n) = (1 + (v_uCE_uB3 n))))))
  (h5 : (v_uCE_uB1 > 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then |((v_uCE_uB2 n))| else 0)))
  (h6 : (v_uCE_uB1 > 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((Real.log (q n)))‖ else 0)))
  (h7 : (v_uCE_uB1 ≤ 0) → (Not (Filter.Tendsto q Filter.atTop (𝓝 1))))
  : (v_uCE_uB1 ≤ 0) → (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (Real.log (q n)) else 0)) := by
  sorry

theorem proof_gap_exercise_3097_5
  (p : (ℕ -> ℝ))
  (q : (ℕ -> ℝ))
  (v_uCE_uB2 : (ℕ -> ℝ))
  (v_uCE_uB3 : (ℕ -> ℝ))
  (v_uCE_uB1 : ℝ)
  (h1 : v_uCE_uB1 ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((q n) = (if (exists (k : ℕ), ((k ∈ (Set.univ : Set ℕ)) ∧ ((n = ((3 * k) + 1)) ∨ (n = ((3 * k) + 3))))) then (1 + (1 /. (Real.rpow (n : ℝ) v_uCE_uB1))) else (if (exists (k : ℕ), ((k ∈ (Set.univ : Set ℕ)) ∧ (n = ((3 * k) + 2)))) then ((1 - (1 /. (Real.rpow (n : ℝ) v_uCE_uB1))) ^ (2 : ℕ)) else ((1 - (1 /. (Real.rpow (n : ℝ) v_uCE_uB1))) ^ (2 : ℕ))))))))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((q n) = (1 + (v_uCE_uB2 n))))))
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((p n) = (1 + (v_uCE_uB3 n))))))
  (h5 : (v_uCE_uB1 > 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then |((v_uCE_uB2 n))| else 0)))
  (h6 : (v_uCE_uB1 > 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((Real.log (q n)))‖ else 0)))
  (h7 : (v_uCE_uB1 ≤ 0) → (Not (Filter.Tendsto q Filter.atTop (𝓝 1))))
  (h8 : (v_uCE_uB1 ≤ 0) → (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (Real.log (q n)) else 0)))
  : (0 < v_uCE_uB1) → ((v_uCE_uB1 ≤ 1) → (forall (k : ℕ), ((k ∈ (Set.univ : Set ℕ)) → (((((v_uCE_uB3 ((4 * k) + 1)) = (1 /. (Real.rpow (1 + (3 * k)) v_uCE_uB1))) ∧ ((v_uCE_uB3 ((4 * k) + 2)) = (-(1 /. (Real.rpow (2 + (3 * k)) v_uCE_uB1))))) ∧ ((v_uCE_uB3 ((4 * k) + 3)) = (-(1 /. (Real.rpow (2 + (3 * k)) v_uCE_uB1))))) ∧ ((v_uCE_uB3 ((4 * k) + 4)) = (1 /. (Real.rpow (3 + (3 * k)) v_uCE_uB1))))))) := by
  sorry

theorem proof_gap_exercise_3097_6
  (p : (ℕ -> ℝ))
  (q : (ℕ -> ℝ))
  (v_uCE_uB2 : (ℕ -> ℝ))
  (v_uCE_uB3 : (ℕ -> ℝ))
  (v_uCE_uB1 : ℝ)
  (h1 : v_uCE_uB1 ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((q n) = (if (exists (k : ℕ), ((k ∈ (Set.univ : Set ℕ)) ∧ ((n = ((3 * k) + 1)) ∨ (n = ((3 * k) + 3))))) then (1 + (1 /. (Real.rpow (n : ℝ) v_uCE_uB1))) else (if (exists (k : ℕ), ((k ∈ (Set.univ : Set ℕ)) ∧ (n = ((3 * k) + 2)))) then ((1 - (1 /. (Real.rpow (n : ℝ) v_uCE_uB1))) ^ (2 : ℕ)) else ((1 - (1 /. (Real.rpow (n : ℝ) v_uCE_uB1))) ^ (2 : ℕ))))))))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((q n) = (1 + (v_uCE_uB2 n))))))
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((p n) = (1 + (v_uCE_uB3 n))))))
  (h5 : (v_uCE_uB1 > 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then |((v_uCE_uB2 n))| else 0)))
  (h6 : (v_uCE_uB1 > 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((Real.log (q n)))‖ else 0)))
  (h7 : (v_uCE_uB1 ≤ 0) → (Not (Filter.Tendsto q Filter.atTop (𝓝 1))))
  (h8 : (v_uCE_uB1 ≤ 0) → (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (Real.log (q n)) else 0)))
  (h9 : (0 < v_uCE_uB1) → ((v_uCE_uB1 ≤ 1) → (forall (k : ℕ), ((k ∈ (Set.univ : Set ℕ)) → (((((v_uCE_uB3 ((4 * k) + 1)) = (1 /. (Real.rpow (1 + (3 * k)) v_uCE_uB1))) ∧ ((v_uCE_uB3 ((4 * k) + 2)) = (-(1 /. (Real.rpow (2 + (3 * k)) v_uCE_uB1))))) ∧ ((v_uCE_uB3 ((4 * k) + 3)) = (-(1 /. (Real.rpow (2 + (3 * k)) v_uCE_uB1))))) ∧ ((v_uCE_uB3 ((4 * k) + 4)) = (1 /. (Real.rpow (3 + (3 * k)) v_uCE_uB1))))))))
  : (0 < v_uCE_uB1) → ((v_uCE_uB1 ≤ 1) → (forall (k : ℕ), ((k ∈ (Set.univ : Set ℕ)) → (((((v_uCE_uB3 ((4 * k) + 1)) + (v_uCE_uB3 ((4 * k) + 2))) + (v_uCE_uB3 ((4 * k) + 3))) + (v_uCE_uB3 ((4 * k) + 4))) = (((1 /. (Real.rpow (1 + (3 * k)) v_uCE_uB1)) - (2 /. (Real.rpow (2 + (3 * k)) v_uCE_uB1))) + (1 /. (Real.rpow (3 + (3 * k)) v_uCE_uB1))))))) := by
  sorry

theorem proof_gap_exercise_3097_7
  (p : (ℕ -> ℝ))
  (q : (ℕ -> ℝ))
  (v_uCE_uB2 : (ℕ -> ℝ))
  (v_uCE_uB3 : (ℕ -> ℝ))
  (v_uCE_uB1 : ℝ)
  (h1 : v_uCE_uB1 ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((q n) = (if (exists (k : ℕ), ((k ∈ (Set.univ : Set ℕ)) ∧ ((n = ((3 * k) + 1)) ∨ (n = ((3 * k) + 3))))) then (1 + (1 /. (Real.rpow (n : ℝ) v_uCE_uB1))) else (if (exists (k : ℕ), ((k ∈ (Set.univ : Set ℕ)) ∧ (n = ((3 * k) + 2)))) then ((1 - (1 /. (Real.rpow (n : ℝ) v_uCE_uB1))) ^ (2 : ℕ)) else ((1 - (1 /. (Real.rpow (n : ℝ) v_uCE_uB1))) ^ (2 : ℕ))))))))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((q n) = (1 + (v_uCE_uB2 n))))))
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((p n) = (1 + (v_uCE_uB3 n))))))
  (h5 : (v_uCE_uB1 > 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then |((v_uCE_uB2 n))| else 0)))
  (h6 : (v_uCE_uB1 > 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((Real.log (q n)))‖ else 0)))
  (h7 : (v_uCE_uB1 ≤ 0) → (Not (Filter.Tendsto q Filter.atTop (𝓝 1))))
  (h8 : (v_uCE_uB1 ≤ 0) → (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (Real.log (q n)) else 0)))
  (h9 : (0 < v_uCE_uB1) → ((v_uCE_uB1 ≤ 1) → (forall (k : ℕ), ((k ∈ (Set.univ : Set ℕ)) → (((((v_uCE_uB3 ((4 * k) + 1)) = (1 /. (Real.rpow (1 + (3 * k)) v_uCE_uB1))) ∧ ((v_uCE_uB3 ((4 * k) + 2)) = (-(1 /. (Real.rpow (2 + (3 * k)) v_uCE_uB1))))) ∧ ((v_uCE_uB3 ((4 * k) + 3)) = (-(1 /. (Real.rpow (2 + (3 * k)) v_uCE_uB1))))) ∧ ((v_uCE_uB3 ((4 * k) + 4)) = (1 /. (Real.rpow (3 + (3 * k)) v_uCE_uB1))))))))
  (h10 : (0 < v_uCE_uB1) → ((v_uCE_uB1 ≤ 1) → (forall (k : ℕ), ((k ∈ (Set.univ : Set ℕ)) → (((((v_uCE_uB3 ((4 * k) + 1)) + (v_uCE_uB3 ((4 * k) + 2))) + (v_uCE_uB3 ((4 * k) + 3))) + (v_uCE_uB3 ((4 * k) + 4))) = (((1 /. (Real.rpow (1 + (3 * k)) v_uCE_uB1)) - (2 /. (Real.rpow (2 + (3 * k)) v_uCE_uB1))) + (1 /. (Real.rpow (3 + (3 * k)) v_uCE_uB1))))))))
  : (0 < v_uCE_uB1) → ((v_uCE_uB1 ≤ 1) → (forall (k : ℕ), ((k ∈ (Set.univ : Set ℕ)) → ((0 < ((((v_uCE_uB3 ((4 * k) + 1)) + (v_uCE_uB3 ((4 * k) + 2))) + (v_uCE_uB3 ((4 * k) + 3))) + (v_uCE_uB3 ((4 * k) + 4)))) ∧ (((((v_uCE_uB3 ((4 * k) + 1)) + (v_uCE_uB3 ((4 * k) + 2))) + (v_uCE_uB3 ((4 * k) + 3))) + (v_uCE_uB3 ((4 * k) + 4))) ≤ (((2 * v_uCE_uB1) * (v_uCE_uB1 + 1)) /. (Real.rpow ((3 * k) + 1) (v_uCE_uB1 + 2)))))))) := by
  sorry

theorem proof_gap_exercise_3097_8
  (p : (ℕ -> ℝ))
  (q : (ℕ -> ℝ))
  (v_uCE_uB2 : (ℕ -> ℝ))
  (v_uCE_uB3 : (ℕ -> ℝ))
  (v_uCE_uB1 : ℝ)
  (h1 : v_uCE_uB1 ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((q n) = (if (exists (k : ℕ), ((k ∈ (Set.univ : Set ℕ)) ∧ ((n = ((3 * k) + 1)) ∨ (n = ((3 * k) + 3))))) then (1 + (1 /. (Real.rpow (n : ℝ) v_uCE_uB1))) else (if (exists (k : ℕ), ((k ∈ (Set.univ : Set ℕ)) ∧ (n = ((3 * k) + 2)))) then ((1 - (1 /. (Real.rpow (n : ℝ) v_uCE_uB1))) ^ (2 : ℕ)) else ((1 - (1 /. (Real.rpow (n : ℝ) v_uCE_uB1))) ^ (2 : ℕ))))))))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((q n) = (1 + (v_uCE_uB2 n))))))
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((p n) = (1 + (v_uCE_uB3 n))))))
  (h5 : (v_uCE_uB1 > 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then |((v_uCE_uB2 n))| else 0)))
  (h6 : (v_uCE_uB1 > 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((Real.log (q n)))‖ else 0)))
  (h7 : (v_uCE_uB1 ≤ 0) → (Not (Filter.Tendsto q Filter.atTop (𝓝 1))))
  (h8 : (v_uCE_uB1 ≤ 0) → (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (Real.log (q n)) else 0)))
  (h9 : (0 < v_uCE_uB1) → ((v_uCE_uB1 ≤ 1) → (forall (k : ℕ), ((k ∈ (Set.univ : Set ℕ)) → (((((v_uCE_uB3 ((4 * k) + 1)) = (1 /. (Real.rpow (1 + (3 * k)) v_uCE_uB1))) ∧ ((v_uCE_uB3 ((4 * k) + 2)) = (-(1 /. (Real.rpow (2 + (3 * k)) v_uCE_uB1))))) ∧ ((v_uCE_uB3 ((4 * k) + 3)) = (-(1 /. (Real.rpow (2 + (3 * k)) v_uCE_uB1))))) ∧ ((v_uCE_uB3 ((4 * k) + 4)) = (1 /. (Real.rpow (3 + (3 * k)) v_uCE_uB1))))))))
  (h10 : (0 < v_uCE_uB1) → ((v_uCE_uB1 ≤ 1) → (forall (k : ℕ), ((k ∈ (Set.univ : Set ℕ)) → (((((v_uCE_uB3 ((4 * k) + 1)) + (v_uCE_uB3 ((4 * k) + 2))) + (v_uCE_uB3 ((4 * k) + 3))) + (v_uCE_uB3 ((4 * k) + 4))) = (((1 /. (Real.rpow (1 + (3 * k)) v_uCE_uB1)) - (2 /. (Real.rpow (2 + (3 * k)) v_uCE_uB1))) + (1 /. (Real.rpow (3 + (3 * k)) v_uCE_uB1))))))))
  (h11 : (0 < v_uCE_uB1) → ((v_uCE_uB1 ≤ 1) → (forall (k : ℕ), ((k ∈ (Set.univ : Set ℕ)) → ((0 < ((((v_uCE_uB3 ((4 * k) + 1)) + (v_uCE_uB3 ((4 * k) + 2))) + (v_uCE_uB3 ((4 * k) + 3))) + (v_uCE_uB3 ((4 * k) + 4)))) ∧ (((((v_uCE_uB3 ((4 * k) + 1)) + (v_uCE_uB3 ((4 * k) + 2))) + (v_uCE_uB3 ((4 * k) + 3))) + (v_uCE_uB3 ((4 * k) + 4))) ≤ (((2 * v_uCE_uB1) * (v_uCE_uB1 + 1)) /. (Real.rpow ((3 * k) + 1) (v_uCE_uB1 + 2)))))))))
  : (0 < v_uCE_uB1) → ((v_uCE_uB1 ≤ 1) → (Summable (fun (k : ℕ) => if (0 : ℕ) ≤ k then ((((v_uCE_uB3 ((4 * k) + 1)) + (v_uCE_uB3 ((4 * k) + 2))) + (v_uCE_uB3 ((4 * k) + 3))) + (v_uCE_uB3 ((4 * k) + 4))) else 0))) := by
  sorry

theorem proof_gap_exercise_3097_9
  (p : (ℕ -> ℝ))
  (q : (ℕ -> ℝ))
  (v_uCE_uB2 : (ℕ -> ℝ))
  (v_uCE_uB3 : (ℕ -> ℝ))
  (v_uCE_uB1 : ℝ)
  (h1 : v_uCE_uB1 ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((q n) = (if (exists (k : ℕ), ((k ∈ (Set.univ : Set ℕ)) ∧ ((n = ((3 * k) + 1)) ∨ (n = ((3 * k) + 3))))) then (1 + (1 /. (Real.rpow (n : ℝ) v_uCE_uB1))) else (if (exists (k : ℕ), ((k ∈ (Set.univ : Set ℕ)) ∧ (n = ((3 * k) + 2)))) then ((1 - (1 /. (Real.rpow (n : ℝ) v_uCE_uB1))) ^ (2 : ℕ)) else ((1 - (1 /. (Real.rpow (n : ℝ) v_uCE_uB1))) ^ (2 : ℕ))))))))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((q n) = (1 + (v_uCE_uB2 n))))))
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((p n) = (1 + (v_uCE_uB3 n))))))
  (h5 : (v_uCE_uB1 > 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then |((v_uCE_uB2 n))| else 0)))
  (h6 : (v_uCE_uB1 > 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((Real.log (q n)))‖ else 0)))
  (h7 : (v_uCE_uB1 ≤ 0) → (Not (Filter.Tendsto q Filter.atTop (𝓝 1))))
  (h8 : (v_uCE_uB1 ≤ 0) → (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (Real.log (q n)) else 0)))
  (h9 : (0 < v_uCE_uB1) → ((v_uCE_uB1 ≤ 1) → (forall (k : ℕ), ((k ∈ (Set.univ : Set ℕ)) → (((((v_uCE_uB3 ((4 * k) + 1)) = (1 /. (Real.rpow (1 + (3 * k)) v_uCE_uB1))) ∧ ((v_uCE_uB3 ((4 * k) + 2)) = (-(1 /. (Real.rpow (2 + (3 * k)) v_uCE_uB1))))) ∧ ((v_uCE_uB3 ((4 * k) + 3)) = (-(1 /. (Real.rpow (2 + (3 * k)) v_uCE_uB1))))) ∧ ((v_uCE_uB3 ((4 * k) + 4)) = (1 /. (Real.rpow (3 + (3 * k)) v_uCE_uB1))))))))
  (h10 : (0 < v_uCE_uB1) → ((v_uCE_uB1 ≤ 1) → (forall (k : ℕ), ((k ∈ (Set.univ : Set ℕ)) → (((((v_uCE_uB3 ((4 * k) + 1)) + (v_uCE_uB3 ((4 * k) + 2))) + (v_uCE_uB3 ((4 * k) + 3))) + (v_uCE_uB3 ((4 * k) + 4))) = (((1 /. (Real.rpow (1 + (3 * k)) v_uCE_uB1)) - (2 /. (Real.rpow (2 + (3 * k)) v_uCE_uB1))) + (1 /. (Real.rpow (3 + (3 * k)) v_uCE_uB1))))))))
  (h11 : (0 < v_uCE_uB1) → ((v_uCE_uB1 ≤ 1) → (forall (k : ℕ), ((k ∈ (Set.univ : Set ℕ)) → ((0 < ((((v_uCE_uB3 ((4 * k) + 1)) + (v_uCE_uB3 ((4 * k) + 2))) + (v_uCE_uB3 ((4 * k) + 3))) + (v_uCE_uB3 ((4 * k) + 4)))) ∧ (((((v_uCE_uB3 ((4 * k) + 1)) + (v_uCE_uB3 ((4 * k) + 2))) + (v_uCE_uB3 ((4 * k) + 3))) + (v_uCE_uB3 ((4 * k) + 4))) ≤ (((2 * v_uCE_uB1) * (v_uCE_uB1 + 1)) /. (Real.rpow ((3 * k) + 1) (v_uCE_uB1 + 2)))))))))
  (h12 : (0 < v_uCE_uB1) → ((v_uCE_uB1 ≤ 1) → (Summable (fun (k : ℕ) => if (0 : ℕ) ≤ k then ((((v_uCE_uB3 ((4 * k) + 1)) + (v_uCE_uB3 ((4 * k) + 2))) + (v_uCE_uB3 ((4 * k) + 3))) + (v_uCE_uB3 ((4 * k) + 4))) else 0))))
  : (0 < v_uCE_uB1) → ((v_uCE_uB1 ≤ 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (v_uCE_uB3 n) else 0))) := by
  sorry

theorem proof_gap_exercise_3097_10
  (p : (ℕ -> ℝ))
  (q : (ℕ -> ℝ))
  (v_uCE_uB2 : (ℕ -> ℝ))
  (v_uCE_uB3 : (ℕ -> ℝ))
  (v_uCE_uB1 : ℝ)
  (h1 : v_uCE_uB1 ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((q n) = (if (exists (k : ℕ), ((k ∈ (Set.univ : Set ℕ)) ∧ ((n = ((3 * k) + 1)) ∨ (n = ((3 * k) + 3))))) then (1 + (1 /. (Real.rpow (n : ℝ) v_uCE_uB1))) else (if (exists (k : ℕ), ((k ∈ (Set.univ : Set ℕ)) ∧ (n = ((3 * k) + 2)))) then ((1 - (1 /. (Real.rpow (n : ℝ) v_uCE_uB1))) ^ (2 : ℕ)) else ((1 - (1 /. (Real.rpow (n : ℝ) v_uCE_uB1))) ^ (2 : ℕ))))))))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((q n) = (1 + (v_uCE_uB2 n))))))
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((p n) = (1 + (v_uCE_uB3 n))))))
  (h5 : (v_uCE_uB1 > 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then |((v_uCE_uB2 n))| else 0)))
  (h6 : (v_uCE_uB1 > 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((Real.log (q n)))‖ else 0)))
  (h7 : (v_uCE_uB1 ≤ 0) → (Not (Filter.Tendsto q Filter.atTop (𝓝 1))))
  (h8 : (v_uCE_uB1 ≤ 0) → (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (Real.log (q n)) else 0)))
  (h9 : (0 < v_uCE_uB1) → ((v_uCE_uB1 ≤ 1) → (forall (k : ℕ), ((k ∈ (Set.univ : Set ℕ)) → (((((v_uCE_uB3 ((4 * k) + 1)) = (1 /. (Real.rpow (1 + (3 * k)) v_uCE_uB1))) ∧ ((v_uCE_uB3 ((4 * k) + 2)) = (-(1 /. (Real.rpow (2 + (3 * k)) v_uCE_uB1))))) ∧ ((v_uCE_uB3 ((4 * k) + 3)) = (-(1 /. (Real.rpow (2 + (3 * k)) v_uCE_uB1))))) ∧ ((v_uCE_uB3 ((4 * k) + 4)) = (1 /. (Real.rpow (3 + (3 * k)) v_uCE_uB1))))))))
  (h10 : (0 < v_uCE_uB1) → ((v_uCE_uB1 ≤ 1) → (forall (k : ℕ), ((k ∈ (Set.univ : Set ℕ)) → (((((v_uCE_uB3 ((4 * k) + 1)) + (v_uCE_uB3 ((4 * k) + 2))) + (v_uCE_uB3 ((4 * k) + 3))) + (v_uCE_uB3 ((4 * k) + 4))) = (((1 /. (Real.rpow (1 + (3 * k)) v_uCE_uB1)) - (2 /. (Real.rpow (2 + (3 * k)) v_uCE_uB1))) + (1 /. (Real.rpow (3 + (3 * k)) v_uCE_uB1))))))))
  (h11 : (0 < v_uCE_uB1) → ((v_uCE_uB1 ≤ 1) → (forall (k : ℕ), ((k ∈ (Set.univ : Set ℕ)) → ((0 < ((((v_uCE_uB3 ((4 * k) + 1)) + (v_uCE_uB3 ((4 * k) + 2))) + (v_uCE_uB3 ((4 * k) + 3))) + (v_uCE_uB3 ((4 * k) + 4)))) ∧ (((((v_uCE_uB3 ((4 * k) + 1)) + (v_uCE_uB3 ((4 * k) + 2))) + (v_uCE_uB3 ((4 * k) + 3))) + (v_uCE_uB3 ((4 * k) + 4))) ≤ (((2 * v_uCE_uB1) * (v_uCE_uB1 + 1)) /. (Real.rpow ((3 * k) + 1) (v_uCE_uB1 + 2)))))))))
  (h12 : (0 < v_uCE_uB1) → ((v_uCE_uB1 ≤ 1) → (Summable (fun (k : ℕ) => if (0 : ℕ) ≤ k then ((((v_uCE_uB3 ((4 * k) + 1)) + (v_uCE_uB3 ((4 * k) + 2))) + (v_uCE_uB3 ((4 * k) + 3))) + (v_uCE_uB3 ((4 * k) + 4))) else 0))))
  (h13 : (0 < v_uCE_uB1) → ((v_uCE_uB1 ≤ 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (v_uCE_uB3 n) else 0))))
  : (0 < v_uCE_uB1) → ((v_uCE_uB1 ≤ (1 /. 2)) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((1 /. (Real.rpow (((3 /. 4) * n) + (9 /. 4)) (2 * v_uCE_uB1))) < ((v_uCE_uB3 n) ^ (2 : ℕ)))))) := by
  sorry

theorem proof_gap_exercise_3097_11
  (p : (ℕ -> ℝ))
  (q : (ℕ -> ℝ))
  (v_uCE_uB2 : (ℕ -> ℝ))
  (v_uCE_uB3 : (ℕ -> ℝ))
  (v_uCE_uB1 : ℝ)
  (h1 : v_uCE_uB1 ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((q n) = (if (exists (k : ℕ), ((k ∈ (Set.univ : Set ℕ)) ∧ ((n = ((3 * k) + 1)) ∨ (n = ((3 * k) + 3))))) then (1 + (1 /. (Real.rpow (n : ℝ) v_uCE_uB1))) else (if (exists (k : ℕ), ((k ∈ (Set.univ : Set ℕ)) ∧ (n = ((3 * k) + 2)))) then ((1 - (1 /. (Real.rpow (n : ℝ) v_uCE_uB1))) ^ (2 : ℕ)) else ((1 - (1 /. (Real.rpow (n : ℝ) v_uCE_uB1))) ^ (2 : ℕ))))))))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((q n) = (1 + (v_uCE_uB2 n))))))
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((p n) = (1 + (v_uCE_uB3 n))))))
  (h5 : (v_uCE_uB1 > 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then |((v_uCE_uB2 n))| else 0)))
  (h6 : (v_uCE_uB1 > 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((Real.log (q n)))‖ else 0)))
  (h7 : (v_uCE_uB1 ≤ 0) → (Not (Filter.Tendsto q Filter.atTop (𝓝 1))))
  (h8 : (v_uCE_uB1 ≤ 0) → (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (Real.log (q n)) else 0)))
  (h9 : (0 < v_uCE_uB1) → ((v_uCE_uB1 ≤ 1) → (forall (k : ℕ), ((k ∈ (Set.univ : Set ℕ)) → (((((v_uCE_uB3 ((4 * k) + 1)) = (1 /. (Real.rpow (1 + (3 * k)) v_uCE_uB1))) ∧ ((v_uCE_uB3 ((4 * k) + 2)) = (-(1 /. (Real.rpow (2 + (3 * k)) v_uCE_uB1))))) ∧ ((v_uCE_uB3 ((4 * k) + 3)) = (-(1 /. (Real.rpow (2 + (3 * k)) v_uCE_uB1))))) ∧ ((v_uCE_uB3 ((4 * k) + 4)) = (1 /. (Real.rpow (3 + (3 * k)) v_uCE_uB1))))))))
  (h10 : (0 < v_uCE_uB1) → ((v_uCE_uB1 ≤ 1) → (forall (k : ℕ), ((k ∈ (Set.univ : Set ℕ)) → (((((v_uCE_uB3 ((4 * k) + 1)) + (v_uCE_uB3 ((4 * k) + 2))) + (v_uCE_uB3 ((4 * k) + 3))) + (v_uCE_uB3 ((4 * k) + 4))) = (((1 /. (Real.rpow (1 + (3 * k)) v_uCE_uB1)) - (2 /. (Real.rpow (2 + (3 * k)) v_uCE_uB1))) + (1 /. (Real.rpow (3 + (3 * k)) v_uCE_uB1))))))))
  (h11 : (0 < v_uCE_uB1) → ((v_uCE_uB1 ≤ 1) → (forall (k : ℕ), ((k ∈ (Set.univ : Set ℕ)) → ((0 < ((((v_uCE_uB3 ((4 * k) + 1)) + (v_uCE_uB3 ((4 * k) + 2))) + (v_uCE_uB3 ((4 * k) + 3))) + (v_uCE_uB3 ((4 * k) + 4)))) ∧ (((((v_uCE_uB3 ((4 * k) + 1)) + (v_uCE_uB3 ((4 * k) + 2))) + (v_uCE_uB3 ((4 * k) + 3))) + (v_uCE_uB3 ((4 * k) + 4))) ≤ (((2 * v_uCE_uB1) * (v_uCE_uB1 + 1)) /. (Real.rpow ((3 * k) + 1) (v_uCE_uB1 + 2)))))))))
  (h12 : (0 < v_uCE_uB1) → ((v_uCE_uB1 ≤ 1) → (Summable (fun (k : ℕ) => if (0 : ℕ) ≤ k then ((((v_uCE_uB3 ((4 * k) + 1)) + (v_uCE_uB3 ((4 * k) + 2))) + (v_uCE_uB3 ((4 * k) + 3))) + (v_uCE_uB3 ((4 * k) + 4))) else 0))))
  (h13 : (0 < v_uCE_uB1) → ((v_uCE_uB1 ≤ 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (v_uCE_uB3 n) else 0))))
  (h14 : (0 < v_uCE_uB1) → ((v_uCE_uB1 ≤ (1 /. 2)) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((1 /. (Real.rpow (((3 /. 4) * n) + (9 /. 4)) (2 * v_uCE_uB1))) < ((v_uCE_uB3 n) ^ (2 : ℕ)))))))
  : (0 < v_uCE_uB1) → ((v_uCE_uB1 ≤ (1 /. 2)) → (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (1 /. (Real.rpow (((3 /. 4) * n) + (9 /. 4)) (2 * v_uCE_uB1))) else 0))) := by
  sorry

theorem proof_gap_exercise_3097_12
  (p : (ℕ -> ℝ))
  (q : (ℕ -> ℝ))
  (v_uCE_uB2 : (ℕ -> ℝ))
  (v_uCE_uB3 : (ℕ -> ℝ))
  (v_uCE_uB1 : ℝ)
  (h1 : v_uCE_uB1 ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((q n) = (if (exists (k : ℕ), ((k ∈ (Set.univ : Set ℕ)) ∧ ((n = ((3 * k) + 1)) ∨ (n = ((3 * k) + 3))))) then (1 + (1 /. (Real.rpow (n : ℝ) v_uCE_uB1))) else (if (exists (k : ℕ), ((k ∈ (Set.univ : Set ℕ)) ∧ (n = ((3 * k) + 2)))) then ((1 - (1 /. (Real.rpow (n : ℝ) v_uCE_uB1))) ^ (2 : ℕ)) else ((1 - (1 /. (Real.rpow (n : ℝ) v_uCE_uB1))) ^ (2 : ℕ))))))))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((q n) = (1 + (v_uCE_uB2 n))))))
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((p n) = (1 + (v_uCE_uB3 n))))))
  (h5 : (v_uCE_uB1 > 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then |((v_uCE_uB2 n))| else 0)))
  (h6 : (v_uCE_uB1 > 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((Real.log (q n)))‖ else 0)))
  (h7 : (v_uCE_uB1 ≤ 0) → (Not (Filter.Tendsto q Filter.atTop (𝓝 1))))
  (h8 : (v_uCE_uB1 ≤ 0) → (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (Real.log (q n)) else 0)))
  (h9 : (0 < v_uCE_uB1) → ((v_uCE_uB1 ≤ 1) → (forall (k : ℕ), ((k ∈ (Set.univ : Set ℕ)) → (((((v_uCE_uB3 ((4 * k) + 1)) = (1 /. (Real.rpow (1 + (3 * k)) v_uCE_uB1))) ∧ ((v_uCE_uB3 ((4 * k) + 2)) = (-(1 /. (Real.rpow (2 + (3 * k)) v_uCE_uB1))))) ∧ ((v_uCE_uB3 ((4 * k) + 3)) = (-(1 /. (Real.rpow (2 + (3 * k)) v_uCE_uB1))))) ∧ ((v_uCE_uB3 ((4 * k) + 4)) = (1 /. (Real.rpow (3 + (3 * k)) v_uCE_uB1))))))))
  (h10 : (0 < v_uCE_uB1) → ((v_uCE_uB1 ≤ 1) → (forall (k : ℕ), ((k ∈ (Set.univ : Set ℕ)) → (((((v_uCE_uB3 ((4 * k) + 1)) + (v_uCE_uB3 ((4 * k) + 2))) + (v_uCE_uB3 ((4 * k) + 3))) + (v_uCE_uB3 ((4 * k) + 4))) = (((1 /. (Real.rpow (1 + (3 * k)) v_uCE_uB1)) - (2 /. (Real.rpow (2 + (3 * k)) v_uCE_uB1))) + (1 /. (Real.rpow (3 + (3 * k)) v_uCE_uB1))))))))
  (h11 : (0 < v_uCE_uB1) → ((v_uCE_uB1 ≤ 1) → (forall (k : ℕ), ((k ∈ (Set.univ : Set ℕ)) → ((0 < ((((v_uCE_uB3 ((4 * k) + 1)) + (v_uCE_uB3 ((4 * k) + 2))) + (v_uCE_uB3 ((4 * k) + 3))) + (v_uCE_uB3 ((4 * k) + 4)))) ∧ (((((v_uCE_uB3 ((4 * k) + 1)) + (v_uCE_uB3 ((4 * k) + 2))) + (v_uCE_uB3 ((4 * k) + 3))) + (v_uCE_uB3 ((4 * k) + 4))) ≤ (((2 * v_uCE_uB1) * (v_uCE_uB1 + 1)) /. (Real.rpow ((3 * k) + 1) (v_uCE_uB1 + 2)))))))))
  (h12 : (0 < v_uCE_uB1) → ((v_uCE_uB1 ≤ 1) → (Summable (fun (k : ℕ) => if (0 : ℕ) ≤ k then ((((v_uCE_uB3 ((4 * k) + 1)) + (v_uCE_uB3 ((4 * k) + 2))) + (v_uCE_uB3 ((4 * k) + 3))) + (v_uCE_uB3 ((4 * k) + 4))) else 0))))
  (h13 : (0 < v_uCE_uB1) → ((v_uCE_uB1 ≤ 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (v_uCE_uB3 n) else 0))))
  (h14 : (0 < v_uCE_uB1) → ((v_uCE_uB1 ≤ (1 /. 2)) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((1 /. (Real.rpow (((3 /. 4) * n) + (9 /. 4)) (2 * v_uCE_uB1))) < ((v_uCE_uB3 n) ^ (2 : ℕ)))))))
  (h15 : (0 < v_uCE_uB1) → ((v_uCE_uB1 ≤ (1 /. 2)) → (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (1 /. (Real.rpow (((3 /. 4) * n) + (9 /. 4)) (2 * v_uCE_uB1))) else 0))))
  : (0 < v_uCE_uB1) → ((v_uCE_uB1 ≤ (1 /. 2)) → (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ((v_uCE_uB3 n) ^ (2 : ℕ)) else 0))) := by
  sorry

theorem proof_gap_exercise_3097_13
  (p : (ℕ -> ℝ))
  (q : (ℕ -> ℝ))
  (v_uCE_uB2 : (ℕ -> ℝ))
  (v_uCE_uB3 : (ℕ -> ℝ))
  (v_uCE_uB1 : ℝ)
  (h1 : v_uCE_uB1 ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((q n) = (if (exists (k : ℕ), ((k ∈ (Set.univ : Set ℕ)) ∧ ((n = ((3 * k) + 1)) ∨ (n = ((3 * k) + 3))))) then (1 + (1 /. (Real.rpow (n : ℝ) v_uCE_uB1))) else (if (exists (k : ℕ), ((k ∈ (Set.univ : Set ℕ)) ∧ (n = ((3 * k) + 2)))) then ((1 - (1 /. (Real.rpow (n : ℝ) v_uCE_uB1))) ^ (2 : ℕ)) else ((1 - (1 /. (Real.rpow (n : ℝ) v_uCE_uB1))) ^ (2 : ℕ))))))))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((q n) = (1 + (v_uCE_uB2 n))))))
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((p n) = (1 + (v_uCE_uB3 n))))))
  (h5 : (v_uCE_uB1 > 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then |((v_uCE_uB2 n))| else 0)))
  (h6 : (v_uCE_uB1 > 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((Real.log (q n)))‖ else 0)))
  (h7 : (v_uCE_uB1 ≤ 0) → (Not (Filter.Tendsto q Filter.atTop (𝓝 1))))
  (h8 : (v_uCE_uB1 ≤ 0) → (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (Real.log (q n)) else 0)))
  (h9 : (0 < v_uCE_uB1) → ((v_uCE_uB1 ≤ 1) → (forall (k : ℕ), ((k ∈ (Set.univ : Set ℕ)) → (((((v_uCE_uB3 ((4 * k) + 1)) = (1 /. (Real.rpow (1 + (3 * k)) v_uCE_uB1))) ∧ ((v_uCE_uB3 ((4 * k) + 2)) = (-(1 /. (Real.rpow (2 + (3 * k)) v_uCE_uB1))))) ∧ ((v_uCE_uB3 ((4 * k) + 3)) = (-(1 /. (Real.rpow (2 + (3 * k)) v_uCE_uB1))))) ∧ ((v_uCE_uB3 ((4 * k) + 4)) = (1 /. (Real.rpow (3 + (3 * k)) v_uCE_uB1))))))))
  (h10 : (0 < v_uCE_uB1) → ((v_uCE_uB1 ≤ 1) → (forall (k : ℕ), ((k ∈ (Set.univ : Set ℕ)) → (((((v_uCE_uB3 ((4 * k) + 1)) + (v_uCE_uB3 ((4 * k) + 2))) + (v_uCE_uB3 ((4 * k) + 3))) + (v_uCE_uB3 ((4 * k) + 4))) = (((1 /. (Real.rpow (1 + (3 * k)) v_uCE_uB1)) - (2 /. (Real.rpow (2 + (3 * k)) v_uCE_uB1))) + (1 /. (Real.rpow (3 + (3 * k)) v_uCE_uB1))))))))
  (h11 : (0 < v_uCE_uB1) → ((v_uCE_uB1 ≤ 1) → (forall (k : ℕ), ((k ∈ (Set.univ : Set ℕ)) → ((0 < ((((v_uCE_uB3 ((4 * k) + 1)) + (v_uCE_uB3 ((4 * k) + 2))) + (v_uCE_uB3 ((4 * k) + 3))) + (v_uCE_uB3 ((4 * k) + 4)))) ∧ (((((v_uCE_uB3 ((4 * k) + 1)) + (v_uCE_uB3 ((4 * k) + 2))) + (v_uCE_uB3 ((4 * k) + 3))) + (v_uCE_uB3 ((4 * k) + 4))) ≤ (((2 * v_uCE_uB1) * (v_uCE_uB1 + 1)) /. (Real.rpow ((3 * k) + 1) (v_uCE_uB1 + 2)))))))))
  (h12 : (0 < v_uCE_uB1) → ((v_uCE_uB1 ≤ 1) → (Summable (fun (k : ℕ) => if (0 : ℕ) ≤ k then ((((v_uCE_uB3 ((4 * k) + 1)) + (v_uCE_uB3 ((4 * k) + 2))) + (v_uCE_uB3 ((4 * k) + 3))) + (v_uCE_uB3 ((4 * k) + 4))) else 0))))
  (h13 : (0 < v_uCE_uB1) → ((v_uCE_uB1 ≤ 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (v_uCE_uB3 n) else 0))))
  (h14 : (0 < v_uCE_uB1) → ((v_uCE_uB1 ≤ (1 /. 2)) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((1 /. (Real.rpow (((3 /. 4) * n) + (9 /. 4)) (2 * v_uCE_uB1))) < ((v_uCE_uB3 n) ^ (2 : ℕ)))))))
  (h15 : (0 < v_uCE_uB1) → ((v_uCE_uB1 ≤ (1 /. 2)) → (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (1 /. (Real.rpow (((3 /. 4) * n) + (9 /. 4)) (2 * v_uCE_uB1))) else 0))))
  (h16 : (0 < v_uCE_uB1) → ((v_uCE_uB1 ≤ (1 /. 2)) → (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ((v_uCE_uB3 n) ^ (2 : ℕ)) else 0))))
  : (0 < v_uCE_uB1) → ((v_uCE_uB1 ≤ (1 /. 2)) → (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (Real.log (q n)) else 0))) := by
  sorry

theorem proof_gap_exercise_3097_14
  (p : (ℕ -> ℝ))
  (q : (ℕ -> ℝ))
  (v_uCE_uB2 : (ℕ -> ℝ))
  (v_uCE_uB3 : (ℕ -> ℝ))
  (v_uCE_uB1 : ℝ)
  (h1 : v_uCE_uB1 ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((q n) = (if (exists (k : ℕ), ((k ∈ (Set.univ : Set ℕ)) ∧ ((n = ((3 * k) + 1)) ∨ (n = ((3 * k) + 3))))) then (1 + (1 /. (Real.rpow (n : ℝ) v_uCE_uB1))) else (if (exists (k : ℕ), ((k ∈ (Set.univ : Set ℕ)) ∧ (n = ((3 * k) + 2)))) then ((1 - (1 /. (Real.rpow (n : ℝ) v_uCE_uB1))) ^ (2 : ℕ)) else ((1 - (1 /. (Real.rpow (n : ℝ) v_uCE_uB1))) ^ (2 : ℕ))))))))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((q n) = (1 + (v_uCE_uB2 n))))))
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((p n) = (1 + (v_uCE_uB3 n))))))
  (h5 : (v_uCE_uB1 > 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then |((v_uCE_uB2 n))| else 0)))
  (h6 : (v_uCE_uB1 > 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((Real.log (q n)))‖ else 0)))
  (h7 : (v_uCE_uB1 ≤ 0) → (Not (Filter.Tendsto q Filter.atTop (𝓝 1))))
  (h8 : (v_uCE_uB1 ≤ 0) → (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (Real.log (q n)) else 0)))
  (h9 : (0 < v_uCE_uB1) → ((v_uCE_uB1 ≤ 1) → (forall (k : ℕ), ((k ∈ (Set.univ : Set ℕ)) → (((((v_uCE_uB3 ((4 * k) + 1)) = (1 /. (Real.rpow (1 + (3 * k)) v_uCE_uB1))) ∧ ((v_uCE_uB3 ((4 * k) + 2)) = (-(1 /. (Real.rpow (2 + (3 * k)) v_uCE_uB1))))) ∧ ((v_uCE_uB3 ((4 * k) + 3)) = (-(1 /. (Real.rpow (2 + (3 * k)) v_uCE_uB1))))) ∧ ((v_uCE_uB3 ((4 * k) + 4)) = (1 /. (Real.rpow (3 + (3 * k)) v_uCE_uB1))))))))
  (h10 : (0 < v_uCE_uB1) → ((v_uCE_uB1 ≤ 1) → (forall (k : ℕ), ((k ∈ (Set.univ : Set ℕ)) → (((((v_uCE_uB3 ((4 * k) + 1)) + (v_uCE_uB3 ((4 * k) + 2))) + (v_uCE_uB3 ((4 * k) + 3))) + (v_uCE_uB3 ((4 * k) + 4))) = (((1 /. (Real.rpow (1 + (3 * k)) v_uCE_uB1)) - (2 /. (Real.rpow (2 + (3 * k)) v_uCE_uB1))) + (1 /. (Real.rpow (3 + (3 * k)) v_uCE_uB1))))))))
  (h11 : (0 < v_uCE_uB1) → ((v_uCE_uB1 ≤ 1) → (forall (k : ℕ), ((k ∈ (Set.univ : Set ℕ)) → ((0 < ((((v_uCE_uB3 ((4 * k) + 1)) + (v_uCE_uB3 ((4 * k) + 2))) + (v_uCE_uB3 ((4 * k) + 3))) + (v_uCE_uB3 ((4 * k) + 4)))) ∧ (((((v_uCE_uB3 ((4 * k) + 1)) + (v_uCE_uB3 ((4 * k) + 2))) + (v_uCE_uB3 ((4 * k) + 3))) + (v_uCE_uB3 ((4 * k) + 4))) ≤ (((2 * v_uCE_uB1) * (v_uCE_uB1 + 1)) /. (Real.rpow ((3 * k) + 1) (v_uCE_uB1 + 2)))))))))
  (h12 : (0 < v_uCE_uB1) → ((v_uCE_uB1 ≤ 1) → (Summable (fun (k : ℕ) => if (0 : ℕ) ≤ k then ((((v_uCE_uB3 ((4 * k) + 1)) + (v_uCE_uB3 ((4 * k) + 2))) + (v_uCE_uB3 ((4 * k) + 3))) + (v_uCE_uB3 ((4 * k) + 4))) else 0))))
  (h13 : (0 < v_uCE_uB1) → ((v_uCE_uB1 ≤ 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (v_uCE_uB3 n) else 0))))
  (h14 : (0 < v_uCE_uB1) → ((v_uCE_uB1 ≤ (1 /. 2)) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((1 /. (Real.rpow (((3 /. 4) * n) + (9 /. 4)) (2 * v_uCE_uB1))) < ((v_uCE_uB3 n) ^ (2 : ℕ)))))))
  (h15 : (0 < v_uCE_uB1) → ((v_uCE_uB1 ≤ (1 /. 2)) → (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (1 /. (Real.rpow (((3 /. 4) * n) + (9 /. 4)) (2 * v_uCE_uB1))) else 0))))
  (h16 : (0 < v_uCE_uB1) → ((v_uCE_uB1 ≤ (1 /. 2)) → (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ((v_uCE_uB3 n) ^ (2 : ℕ)) else 0))))
  (h17 : (0 < v_uCE_uB1) → ((v_uCE_uB1 ≤ (1 /. 2)) → (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (Real.log (q n)) else 0))))
  : ((1 /. 2) < v_uCE_uB1) → ((v_uCE_uB1 ≤ 1) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (((v_uCE_uB3 n) ^ (2 : ℕ)) < (1 /. (Real.rpow (((3 /. 4) * n) + (1 /. 4)) (2 * v_uCE_uB1))))))) := by
  sorry

theorem proof_gap_exercise_3097_15
  (p : (ℕ -> ℝ))
  (q : (ℕ -> ℝ))
  (v_uCE_uB2 : (ℕ -> ℝ))
  (v_uCE_uB3 : (ℕ -> ℝ))
  (v_uCE_uB1 : ℝ)
  (h1 : v_uCE_uB1 ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((q n) = (if (exists (k : ℕ), ((k ∈ (Set.univ : Set ℕ)) ∧ ((n = ((3 * k) + 1)) ∨ (n = ((3 * k) + 3))))) then (1 + (1 /. (Real.rpow (n : ℝ) v_uCE_uB1))) else (if (exists (k : ℕ), ((k ∈ (Set.univ : Set ℕ)) ∧ (n = ((3 * k) + 2)))) then ((1 - (1 /. (Real.rpow (n : ℝ) v_uCE_uB1))) ^ (2 : ℕ)) else ((1 - (1 /. (Real.rpow (n : ℝ) v_uCE_uB1))) ^ (2 : ℕ))))))))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((q n) = (1 + (v_uCE_uB2 n))))))
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((p n) = (1 + (v_uCE_uB3 n))))))
  (h5 : (v_uCE_uB1 > 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then |((v_uCE_uB2 n))| else 0)))
  (h6 : (v_uCE_uB1 > 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((Real.log (q n)))‖ else 0)))
  (h7 : (v_uCE_uB1 ≤ 0) → (Not (Filter.Tendsto q Filter.atTop (𝓝 1))))
  (h8 : (v_uCE_uB1 ≤ 0) → (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (Real.log (q n)) else 0)))
  (h9 : (0 < v_uCE_uB1) → ((v_uCE_uB1 ≤ 1) → (forall (k : ℕ), ((k ∈ (Set.univ : Set ℕ)) → (((((v_uCE_uB3 ((4 * k) + 1)) = (1 /. (Real.rpow (1 + (3 * k)) v_uCE_uB1))) ∧ ((v_uCE_uB3 ((4 * k) + 2)) = (-(1 /. (Real.rpow (2 + (3 * k)) v_uCE_uB1))))) ∧ ((v_uCE_uB3 ((4 * k) + 3)) = (-(1 /. (Real.rpow (2 + (3 * k)) v_uCE_uB1))))) ∧ ((v_uCE_uB3 ((4 * k) + 4)) = (1 /. (Real.rpow (3 + (3 * k)) v_uCE_uB1))))))))
  (h10 : (0 < v_uCE_uB1) → ((v_uCE_uB1 ≤ 1) → (forall (k : ℕ), ((k ∈ (Set.univ : Set ℕ)) → (((((v_uCE_uB3 ((4 * k) + 1)) + (v_uCE_uB3 ((4 * k) + 2))) + (v_uCE_uB3 ((4 * k) + 3))) + (v_uCE_uB3 ((4 * k) + 4))) = (((1 /. (Real.rpow (1 + (3 * k)) v_uCE_uB1)) - (2 /. (Real.rpow (2 + (3 * k)) v_uCE_uB1))) + (1 /. (Real.rpow (3 + (3 * k)) v_uCE_uB1))))))))
  (h11 : (0 < v_uCE_uB1) → ((v_uCE_uB1 ≤ 1) → (forall (k : ℕ), ((k ∈ (Set.univ : Set ℕ)) → ((0 < ((((v_uCE_uB3 ((4 * k) + 1)) + (v_uCE_uB3 ((4 * k) + 2))) + (v_uCE_uB3 ((4 * k) + 3))) + (v_uCE_uB3 ((4 * k) + 4)))) ∧ (((((v_uCE_uB3 ((4 * k) + 1)) + (v_uCE_uB3 ((4 * k) + 2))) + (v_uCE_uB3 ((4 * k) + 3))) + (v_uCE_uB3 ((4 * k) + 4))) ≤ (((2 * v_uCE_uB1) * (v_uCE_uB1 + 1)) /. (Real.rpow ((3 * k) + 1) (v_uCE_uB1 + 2)))))))))
  (h12 : (0 < v_uCE_uB1) → ((v_uCE_uB1 ≤ 1) → (Summable (fun (k : ℕ) => if (0 : ℕ) ≤ k then ((((v_uCE_uB3 ((4 * k) + 1)) + (v_uCE_uB3 ((4 * k) + 2))) + (v_uCE_uB3 ((4 * k) + 3))) + (v_uCE_uB3 ((4 * k) + 4))) else 0))))
  (h13 : (0 < v_uCE_uB1) → ((v_uCE_uB1 ≤ 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (v_uCE_uB3 n) else 0))))
  (h14 : (0 < v_uCE_uB1) → ((v_uCE_uB1 ≤ (1 /. 2)) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((1 /. (Real.rpow (((3 /. 4) * n) + (9 /. 4)) (2 * v_uCE_uB1))) < ((v_uCE_uB3 n) ^ (2 : ℕ)))))))
  (h15 : (0 < v_uCE_uB1) → ((v_uCE_uB1 ≤ (1 /. 2)) → (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (1 /. (Real.rpow (((3 /. 4) * n) + (9 /. 4)) (2 * v_uCE_uB1))) else 0))))
  (h16 : (0 < v_uCE_uB1) → ((v_uCE_uB1 ≤ (1 /. 2)) → (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ((v_uCE_uB3 n) ^ (2 : ℕ)) else 0))))
  (h17 : (0 < v_uCE_uB1) → ((v_uCE_uB1 ≤ (1 /. 2)) → (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (Real.log (q n)) else 0))))
  (h18 : ((1 /. 2) < v_uCE_uB1) → ((v_uCE_uB1 ≤ 1) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (((v_uCE_uB3 n) ^ (2 : ℕ)) < (1 /. (Real.rpow (((3 /. 4) * n) + (1 /. 4)) (2 * v_uCE_uB1))))))))
  : ((1 /. 2) < v_uCE_uB1) → ((v_uCE_uB1 ≤ 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (1 /. (Real.rpow (((3 /. 4) * n) + (1 /. 4)) (2 * v_uCE_uB1))) else 0))) := by
  sorry

theorem proof_gap_exercise_3097_16
  (p : (ℕ -> ℝ))
  (q : (ℕ -> ℝ))
  (v_uCE_uB2 : (ℕ -> ℝ))
  (v_uCE_uB3 : (ℕ -> ℝ))
  (v_uCE_uB1 : ℝ)
  (h1 : v_uCE_uB1 ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((q n) = (if (exists (k : ℕ), ((k ∈ (Set.univ : Set ℕ)) ∧ ((n = ((3 * k) + 1)) ∨ (n = ((3 * k) + 3))))) then (1 + (1 /. (Real.rpow (n : ℝ) v_uCE_uB1))) else (if (exists (k : ℕ), ((k ∈ (Set.univ : Set ℕ)) ∧ (n = ((3 * k) + 2)))) then ((1 - (1 /. (Real.rpow (n : ℝ) v_uCE_uB1))) ^ (2 : ℕ)) else ((1 - (1 /. (Real.rpow (n : ℝ) v_uCE_uB1))) ^ (2 : ℕ))))))))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((q n) = (1 + (v_uCE_uB2 n))))))
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((p n) = (1 + (v_uCE_uB3 n))))))
  (h5 : (v_uCE_uB1 > 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then |((v_uCE_uB2 n))| else 0)))
  (h6 : (v_uCE_uB1 > 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((Real.log (q n)))‖ else 0)))
  (h7 : (v_uCE_uB1 ≤ 0) → (Not (Filter.Tendsto q Filter.atTop (𝓝 1))))
  (h8 : (v_uCE_uB1 ≤ 0) → (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (Real.log (q n)) else 0)))
  (h9 : (0 < v_uCE_uB1) → ((v_uCE_uB1 ≤ 1) → (forall (k : ℕ), ((k ∈ (Set.univ : Set ℕ)) → (((((v_uCE_uB3 ((4 * k) + 1)) = (1 /. (Real.rpow (1 + (3 * k)) v_uCE_uB1))) ∧ ((v_uCE_uB3 ((4 * k) + 2)) = (-(1 /. (Real.rpow (2 + (3 * k)) v_uCE_uB1))))) ∧ ((v_uCE_uB3 ((4 * k) + 3)) = (-(1 /. (Real.rpow (2 + (3 * k)) v_uCE_uB1))))) ∧ ((v_uCE_uB3 ((4 * k) + 4)) = (1 /. (Real.rpow (3 + (3 * k)) v_uCE_uB1))))))))
  (h10 : (0 < v_uCE_uB1) → ((v_uCE_uB1 ≤ 1) → (forall (k : ℕ), ((k ∈ (Set.univ : Set ℕ)) → (((((v_uCE_uB3 ((4 * k) + 1)) + (v_uCE_uB3 ((4 * k) + 2))) + (v_uCE_uB3 ((4 * k) + 3))) + (v_uCE_uB3 ((4 * k) + 4))) = (((1 /. (Real.rpow (1 + (3 * k)) v_uCE_uB1)) - (2 /. (Real.rpow (2 + (3 * k)) v_uCE_uB1))) + (1 /. (Real.rpow (3 + (3 * k)) v_uCE_uB1))))))))
  (h11 : (0 < v_uCE_uB1) → ((v_uCE_uB1 ≤ 1) → (forall (k : ℕ), ((k ∈ (Set.univ : Set ℕ)) → ((0 < ((((v_uCE_uB3 ((4 * k) + 1)) + (v_uCE_uB3 ((4 * k) + 2))) + (v_uCE_uB3 ((4 * k) + 3))) + (v_uCE_uB3 ((4 * k) + 4)))) ∧ (((((v_uCE_uB3 ((4 * k) + 1)) + (v_uCE_uB3 ((4 * k) + 2))) + (v_uCE_uB3 ((4 * k) + 3))) + (v_uCE_uB3 ((4 * k) + 4))) ≤ (((2 * v_uCE_uB1) * (v_uCE_uB1 + 1)) /. (Real.rpow ((3 * k) + 1) (v_uCE_uB1 + 2)))))))))
  (h12 : (0 < v_uCE_uB1) → ((v_uCE_uB1 ≤ 1) → (Summable (fun (k : ℕ) => if (0 : ℕ) ≤ k then ((((v_uCE_uB3 ((4 * k) + 1)) + (v_uCE_uB3 ((4 * k) + 2))) + (v_uCE_uB3 ((4 * k) + 3))) + (v_uCE_uB3 ((4 * k) + 4))) else 0))))
  (h13 : (0 < v_uCE_uB1) → ((v_uCE_uB1 ≤ 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (v_uCE_uB3 n) else 0))))
  (h14 : (0 < v_uCE_uB1) → ((v_uCE_uB1 ≤ (1 /. 2)) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((1 /. (Real.rpow (((3 /. 4) * n) + (9 /. 4)) (2 * v_uCE_uB1))) < ((v_uCE_uB3 n) ^ (2 : ℕ)))))))
  (h15 : (0 < v_uCE_uB1) → ((v_uCE_uB1 ≤ (1 /. 2)) → (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (1 /. (Real.rpow (((3 /. 4) * n) + (9 /. 4)) (2 * v_uCE_uB1))) else 0))))
  (h16 : (0 < v_uCE_uB1) → ((v_uCE_uB1 ≤ (1 /. 2)) → (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ((v_uCE_uB3 n) ^ (2 : ℕ)) else 0))))
  (h17 : (0 < v_uCE_uB1) → ((v_uCE_uB1 ≤ (1 /. 2)) → (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (Real.log (q n)) else 0))))
  (h18 : ((1 /. 2) < v_uCE_uB1) → ((v_uCE_uB1 ≤ 1) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (((v_uCE_uB3 n) ^ (2 : ℕ)) < (1 /. (Real.rpow (((3 /. 4) * n) + (1 /. 4)) (2 * v_uCE_uB1))))))))
  (h19 : ((1 /. 2) < v_uCE_uB1) → ((v_uCE_uB1 ≤ 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (1 /. (Real.rpow (((3 /. 4) * n) + (1 /. 4)) (2 * v_uCE_uB1))) else 0))))
  : ((1 /. 2) < v_uCE_uB1) → ((v_uCE_uB1 ≤ 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ((v_uCE_uB3 n) ^ (2 : ℕ)) else 0))) := by
  sorry

theorem proof_gap_exercise_3097_17
  (p : (ℕ -> ℝ))
  (q : (ℕ -> ℝ))
  (v_uCE_uB2 : (ℕ -> ℝ))
  (v_uCE_uB3 : (ℕ -> ℝ))
  (v_uCE_uB1 : ℝ)
  (h1 : v_uCE_uB1 ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((q n) = (if (exists (k : ℕ), ((k ∈ (Set.univ : Set ℕ)) ∧ ((n = ((3 * k) + 1)) ∨ (n = ((3 * k) + 3))))) then (1 + (1 /. (Real.rpow (n : ℝ) v_uCE_uB1))) else (if (exists (k : ℕ), ((k ∈ (Set.univ : Set ℕ)) ∧ (n = ((3 * k) + 2)))) then ((1 - (1 /. (Real.rpow (n : ℝ) v_uCE_uB1))) ^ (2 : ℕ)) else ((1 - (1 /. (Real.rpow (n : ℝ) v_uCE_uB1))) ^ (2 : ℕ))))))))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((q n) = (1 + (v_uCE_uB2 n))))))
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((p n) = (1 + (v_uCE_uB3 n))))))
  (h5 : (v_uCE_uB1 > 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then |((v_uCE_uB2 n))| else 0)))
  (h6 : (v_uCE_uB1 > 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((Real.log (q n)))‖ else 0)))
  (h7 : (v_uCE_uB1 ≤ 0) → (Not (Filter.Tendsto q Filter.atTop (𝓝 1))))
  (h8 : (v_uCE_uB1 ≤ 0) → (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (Real.log (q n)) else 0)))
  (h9 : (0 < v_uCE_uB1) → ((v_uCE_uB1 ≤ 1) → (forall (k : ℕ), ((k ∈ (Set.univ : Set ℕ)) → (((((v_uCE_uB3 ((4 * k) + 1)) = (1 /. (Real.rpow (1 + (3 * k)) v_uCE_uB1))) ∧ ((v_uCE_uB3 ((4 * k) + 2)) = (-(1 /. (Real.rpow (2 + (3 * k)) v_uCE_uB1))))) ∧ ((v_uCE_uB3 ((4 * k) + 3)) = (-(1 /. (Real.rpow (2 + (3 * k)) v_uCE_uB1))))) ∧ ((v_uCE_uB3 ((4 * k) + 4)) = (1 /. (Real.rpow (3 + (3 * k)) v_uCE_uB1))))))))
  (h10 : (0 < v_uCE_uB1) → ((v_uCE_uB1 ≤ 1) → (forall (k : ℕ), ((k ∈ (Set.univ : Set ℕ)) → (((((v_uCE_uB3 ((4 * k) + 1)) + (v_uCE_uB3 ((4 * k) + 2))) + (v_uCE_uB3 ((4 * k) + 3))) + (v_uCE_uB3 ((4 * k) + 4))) = (((1 /. (Real.rpow (1 + (3 * k)) v_uCE_uB1)) - (2 /. (Real.rpow (2 + (3 * k)) v_uCE_uB1))) + (1 /. (Real.rpow (3 + (3 * k)) v_uCE_uB1))))))))
  (h11 : (0 < v_uCE_uB1) → ((v_uCE_uB1 ≤ 1) → (forall (k : ℕ), ((k ∈ (Set.univ : Set ℕ)) → ((0 < ((((v_uCE_uB3 ((4 * k) + 1)) + (v_uCE_uB3 ((4 * k) + 2))) + (v_uCE_uB3 ((4 * k) + 3))) + (v_uCE_uB3 ((4 * k) + 4)))) ∧ (((((v_uCE_uB3 ((4 * k) + 1)) + (v_uCE_uB3 ((4 * k) + 2))) + (v_uCE_uB3 ((4 * k) + 3))) + (v_uCE_uB3 ((4 * k) + 4))) ≤ (((2 * v_uCE_uB1) * (v_uCE_uB1 + 1)) /. (Real.rpow ((3 * k) + 1) (v_uCE_uB1 + 2)))))))))
  (h12 : (0 < v_uCE_uB1) → ((v_uCE_uB1 ≤ 1) → (Summable (fun (k : ℕ) => if (0 : ℕ) ≤ k then ((((v_uCE_uB3 ((4 * k) + 1)) + (v_uCE_uB3 ((4 * k) + 2))) + (v_uCE_uB3 ((4 * k) + 3))) + (v_uCE_uB3 ((4 * k) + 4))) else 0))))
  (h13 : (0 < v_uCE_uB1) → ((v_uCE_uB1 ≤ 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (v_uCE_uB3 n) else 0))))
  (h14 : (0 < v_uCE_uB1) → ((v_uCE_uB1 ≤ (1 /. 2)) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((1 /. (Real.rpow (((3 /. 4) * n) + (9 /. 4)) (2 * v_uCE_uB1))) < ((v_uCE_uB3 n) ^ (2 : ℕ)))))))
  (h15 : (0 < v_uCE_uB1) → ((v_uCE_uB1 ≤ (1 /. 2)) → (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (1 /. (Real.rpow (((3 /. 4) * n) + (9 /. 4)) (2 * v_uCE_uB1))) else 0))))
  (h16 : (0 < v_uCE_uB1) → ((v_uCE_uB1 ≤ (1 /. 2)) → (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ((v_uCE_uB3 n) ^ (2 : ℕ)) else 0))))
  (h17 : (0 < v_uCE_uB1) → ((v_uCE_uB1 ≤ (1 /. 2)) → (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (Real.log (q n)) else 0))))
  (h18 : ((1 /. 2) < v_uCE_uB1) → ((v_uCE_uB1 ≤ 1) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (((v_uCE_uB3 n) ^ (2 : ℕ)) < (1 /. (Real.rpow (((3 /. 4) * n) + (1 /. 4)) (2 * v_uCE_uB1))))))))
  (h19 : ((1 /. 2) < v_uCE_uB1) → ((v_uCE_uB1 ≤ 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (1 /. (Real.rpow (((3 /. 4) * n) + (1 /. 4)) (2 * v_uCE_uB1))) else 0))))
  (h20 : ((1 /. 2) < v_uCE_uB1) → ((v_uCE_uB1 ≤ 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ((v_uCE_uB3 n) ^ (2 : ℕ)) else 0))))
  : ((1 /. 2) < v_uCE_uB1) → ((v_uCE_uB1 ≤ 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (Real.log (q n)) else 0))) := by
  sorry

theorem proof_gap_exercise_3097_18
  (p : (ℕ -> ℝ))
  (q : (ℕ -> ℝ))
  (v_uCE_uB2 : (ℕ -> ℝ))
  (v_uCE_uB3 : (ℕ -> ℝ))
  (v_uCE_uB1 : ℝ)
  (h1 : v_uCE_uB1 ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((q n) = (if (exists (k : ℕ), ((k ∈ (Set.univ : Set ℕ)) ∧ ((n = ((3 * k) + 1)) ∨ (n = ((3 * k) + 3))))) then (1 + (1 /. (Real.rpow (n : ℝ) v_uCE_uB1))) else (if (exists (k : ℕ), ((k ∈ (Set.univ : Set ℕ)) ∧ (n = ((3 * k) + 2)))) then ((1 - (1 /. (Real.rpow (n : ℝ) v_uCE_uB1))) ^ (2 : ℕ)) else ((1 - (1 /. (Real.rpow (n : ℝ) v_uCE_uB1))) ^ (2 : ℕ))))))))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((q n) = (1 + (v_uCE_uB2 n))))))
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((p n) = (1 + (v_uCE_uB3 n))))))
  (h5 : (v_uCE_uB1 > 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then |((v_uCE_uB2 n))| else 0)))
  (h6 : (v_uCE_uB1 > 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((Real.log (q n)))‖ else 0)))
  (h7 : (v_uCE_uB1 ≤ 0) → (Not (Filter.Tendsto q Filter.atTop (𝓝 1))))
  (h8 : (v_uCE_uB1 ≤ 0) → (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (Real.log (q n)) else 0)))
  (h9 : (0 < v_uCE_uB1) → ((v_uCE_uB1 ≤ 1) → (forall (k : ℕ), ((k ∈ (Set.univ : Set ℕ)) → (((((v_uCE_uB3 ((4 * k) + 1)) = (1 /. (Real.rpow (1 + (3 * k)) v_uCE_uB1))) ∧ ((v_uCE_uB3 ((4 * k) + 2)) = (-(1 /. (Real.rpow (2 + (3 * k)) v_uCE_uB1))))) ∧ ((v_uCE_uB3 ((4 * k) + 3)) = (-(1 /. (Real.rpow (2 + (3 * k)) v_uCE_uB1))))) ∧ ((v_uCE_uB3 ((4 * k) + 4)) = (1 /. (Real.rpow (3 + (3 * k)) v_uCE_uB1))))))))
  (h10 : (0 < v_uCE_uB1) → ((v_uCE_uB1 ≤ 1) → (forall (k : ℕ), ((k ∈ (Set.univ : Set ℕ)) → (((((v_uCE_uB3 ((4 * k) + 1)) + (v_uCE_uB3 ((4 * k) + 2))) + (v_uCE_uB3 ((4 * k) + 3))) + (v_uCE_uB3 ((4 * k) + 4))) = (((1 /. (Real.rpow (1 + (3 * k)) v_uCE_uB1)) - (2 /. (Real.rpow (2 + (3 * k)) v_uCE_uB1))) + (1 /. (Real.rpow (3 + (3 * k)) v_uCE_uB1))))))))
  (h11 : (0 < v_uCE_uB1) → ((v_uCE_uB1 ≤ 1) → (forall (k : ℕ), ((k ∈ (Set.univ : Set ℕ)) → ((0 < ((((v_uCE_uB3 ((4 * k) + 1)) + (v_uCE_uB3 ((4 * k) + 2))) + (v_uCE_uB3 ((4 * k) + 3))) + (v_uCE_uB3 ((4 * k) + 4)))) ∧ (((((v_uCE_uB3 ((4 * k) + 1)) + (v_uCE_uB3 ((4 * k) + 2))) + (v_uCE_uB3 ((4 * k) + 3))) + (v_uCE_uB3 ((4 * k) + 4))) ≤ (((2 * v_uCE_uB1) * (v_uCE_uB1 + 1)) /. (Real.rpow ((3 * k) + 1) (v_uCE_uB1 + 2)))))))))
  (h12 : (0 < v_uCE_uB1) → ((v_uCE_uB1 ≤ 1) → (Summable (fun (k : ℕ) => if (0 : ℕ) ≤ k then ((((v_uCE_uB3 ((4 * k) + 1)) + (v_uCE_uB3 ((4 * k) + 2))) + (v_uCE_uB3 ((4 * k) + 3))) + (v_uCE_uB3 ((4 * k) + 4))) else 0))))
  (h13 : (0 < v_uCE_uB1) → ((v_uCE_uB1 ≤ 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (v_uCE_uB3 n) else 0))))
  (h14 : (0 < v_uCE_uB1) → ((v_uCE_uB1 ≤ (1 /. 2)) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((1 /. (Real.rpow (((3 /. 4) * n) + (9 /. 4)) (2 * v_uCE_uB1))) < ((v_uCE_uB3 n) ^ (2 : ℕ)))))))
  (h15 : (0 < v_uCE_uB1) → ((v_uCE_uB1 ≤ (1 /. 2)) → (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (1 /. (Real.rpow (((3 /. 4) * n) + (9 /. 4)) (2 * v_uCE_uB1))) else 0))))
  (h16 : (0 < v_uCE_uB1) → ((v_uCE_uB1 ≤ (1 /. 2)) → (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ((v_uCE_uB3 n) ^ (2 : ℕ)) else 0))))
  (h17 : (0 < v_uCE_uB1) → ((v_uCE_uB1 ≤ (1 /. 2)) → (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (Real.log (q n)) else 0))))
  (h18 : ((1 /. 2) < v_uCE_uB1) → ((v_uCE_uB1 ≤ 1) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (((v_uCE_uB3 n) ^ (2 : ℕ)) < (1 /. (Real.rpow (((3 /. 4) * n) + (1 /. 4)) (2 * v_uCE_uB1))))))))
  (h19 : ((1 /. 2) < v_uCE_uB1) → ((v_uCE_uB1 ≤ 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (1 /. (Real.rpow (((3 /. 4) * n) + (1 /. 4)) (2 * v_uCE_uB1))) else 0))))
  (h20 : ((1 /. 2) < v_uCE_uB1) → ((v_uCE_uB1 ≤ 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ((v_uCE_uB3 n) ^ (2 : ℕ)) else 0))))
  (h21 : ((1 /. 2) < v_uCE_uB1) → ((v_uCE_uB1 ≤ 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (Real.log (q n)) else 0))))
  : ((1 /. 2) < v_uCE_uB1) → ((v_uCE_uB1 ≤ 1) → (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then |((v_uCE_uB2 n))| else 0))) := by
  sorry

theorem proof_gap_exercise_3097_19
  (p : (ℕ -> ℝ))
  (q : (ℕ -> ℝ))
  (v_uCE_uB2 : (ℕ -> ℝ))
  (v_uCE_uB3 : (ℕ -> ℝ))
  (v_uCE_uB1 : ℝ)
  (h1 : v_uCE_uB1 ∈ (Set.univ : Set ℝ))
  (h2 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((q n) = (if (exists (k : ℕ), ((k ∈ (Set.univ : Set ℕ)) ∧ ((n = ((3 * k) + 1)) ∨ (n = ((3 * k) + 3))))) then (1 + (1 /. (Real.rpow (n : ℝ) v_uCE_uB1))) else (if (exists (k : ℕ), ((k ∈ (Set.univ : Set ℕ)) ∧ (n = ((3 * k) + 2)))) then ((1 - (1 /. (Real.rpow (n : ℝ) v_uCE_uB1))) ^ (2 : ℕ)) else ((1 - (1 /. (Real.rpow (n : ℝ) v_uCE_uB1))) ^ (2 : ℕ))))))))
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((q n) = (1 + (v_uCE_uB2 n))))))
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((p n) = (1 + (v_uCE_uB3 n))))))
  (h5 : (v_uCE_uB1 > 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then |((v_uCE_uB2 n))| else 0)))
  (h6 : (v_uCE_uB1 > 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((Real.log (q n)))‖ else 0)))
  (h7 : (v_uCE_uB1 ≤ 0) → (Not (Filter.Tendsto q Filter.atTop (𝓝 1))))
  (h8 : (v_uCE_uB1 ≤ 0) → (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (Real.log (q n)) else 0)))
  (h9 : (0 < v_uCE_uB1) → ((v_uCE_uB1 ≤ 1) → (forall (k : ℕ), ((k ∈ (Set.univ : Set ℕ)) → (((((v_uCE_uB3 ((4 * k) + 1)) = (1 /. (Real.rpow (1 + (3 * k)) v_uCE_uB1))) ∧ ((v_uCE_uB3 ((4 * k) + 2)) = (-(1 /. (Real.rpow (2 + (3 * k)) v_uCE_uB1))))) ∧ ((v_uCE_uB3 ((4 * k) + 3)) = (-(1 /. (Real.rpow (2 + (3 * k)) v_uCE_uB1))))) ∧ ((v_uCE_uB3 ((4 * k) + 4)) = (1 /. (Real.rpow (3 + (3 * k)) v_uCE_uB1))))))))
  (h10 : (0 < v_uCE_uB1) → ((v_uCE_uB1 ≤ 1) → (forall (k : ℕ), ((k ∈ (Set.univ : Set ℕ)) → (((((v_uCE_uB3 ((4 * k) + 1)) + (v_uCE_uB3 ((4 * k) + 2))) + (v_uCE_uB3 ((4 * k) + 3))) + (v_uCE_uB3 ((4 * k) + 4))) = (((1 /. (Real.rpow (1 + (3 * k)) v_uCE_uB1)) - (2 /. (Real.rpow (2 + (3 * k)) v_uCE_uB1))) + (1 /. (Real.rpow (3 + (3 * k)) v_uCE_uB1))))))))
  (h11 : (0 < v_uCE_uB1) → ((v_uCE_uB1 ≤ 1) → (forall (k : ℕ), ((k ∈ (Set.univ : Set ℕ)) → ((0 < ((((v_uCE_uB3 ((4 * k) + 1)) + (v_uCE_uB3 ((4 * k) + 2))) + (v_uCE_uB3 ((4 * k) + 3))) + (v_uCE_uB3 ((4 * k) + 4)))) ∧ (((((v_uCE_uB3 ((4 * k) + 1)) + (v_uCE_uB3 ((4 * k) + 2))) + (v_uCE_uB3 ((4 * k) + 3))) + (v_uCE_uB3 ((4 * k) + 4))) ≤ (((2 * v_uCE_uB1) * (v_uCE_uB1 + 1)) /. (Real.rpow ((3 * k) + 1) (v_uCE_uB1 + 2)))))))))
  (h12 : (0 < v_uCE_uB1) → ((v_uCE_uB1 ≤ 1) → (Summable (fun (k : ℕ) => if (0 : ℕ) ≤ k then ((((v_uCE_uB3 ((4 * k) + 1)) + (v_uCE_uB3 ((4 * k) + 2))) + (v_uCE_uB3 ((4 * k) + 3))) + (v_uCE_uB3 ((4 * k) + 4))) else 0))))
  (h13 : (0 < v_uCE_uB1) → ((v_uCE_uB1 ≤ 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (v_uCE_uB3 n) else 0))))
  (h14 : (0 < v_uCE_uB1) → ((v_uCE_uB1 ≤ (1 /. 2)) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((1 /. (Real.rpow (((3 /. 4) * n) + (9 /. 4)) (2 * v_uCE_uB1))) < ((v_uCE_uB3 n) ^ (2 : ℕ)))))))
  (h15 : (0 < v_uCE_uB1) → ((v_uCE_uB1 ≤ (1 /. 2)) → (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (1 /. (Real.rpow (((3 /. 4) * n) + (9 /. 4)) (2 * v_uCE_uB1))) else 0))))
  (h16 : (0 < v_uCE_uB1) → ((v_uCE_uB1 ≤ (1 /. 2)) → (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ((v_uCE_uB3 n) ^ (2 : ℕ)) else 0))))
  (h17 : (0 < v_uCE_uB1) → ((v_uCE_uB1 ≤ (1 /. 2)) → (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (Real.log (q n)) else 0))))
  (h18 : ((1 /. 2) < v_uCE_uB1) → ((v_uCE_uB1 ≤ 1) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (((v_uCE_uB3 n) ^ (2 : ℕ)) < (1 /. (Real.rpow (((3 /. 4) * n) + (1 /. 4)) (2 * v_uCE_uB1))))))))
  (h19 : ((1 /. 2) < v_uCE_uB1) → ((v_uCE_uB1 ≤ 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (1 /. (Real.rpow (((3 /. 4) * n) + (1 /. 4)) (2 * v_uCE_uB1))) else 0))))
  (h20 : ((1 /. 2) < v_uCE_uB1) → ((v_uCE_uB1 ≤ 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ((v_uCE_uB3 n) ^ (2 : ℕ)) else 0))))
  (h21 : ((1 /. 2) < v_uCE_uB1) → ((v_uCE_uB1 ≤ 1) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (Real.log (q n)) else 0))))
  (h22 : ((1 /. 2) < v_uCE_uB1) → ((v_uCE_uB1 ≤ 1) → (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then |((v_uCE_uB2 n))| else 0))))
  : (v_uCE_uB1 ∈ ({v_uCE_uB1_1 | ((v_uCE_uB1_1 > 1) ∨ (((1 /. 2) < v_uCE_uB1_1) ∧ (v_uCE_uB1_1 ≤ 1)))})) ↔ (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (Real.log (q n)) else 0)) := by
  sorry
