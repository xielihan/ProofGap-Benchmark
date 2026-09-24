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

-- exercise: exercise_2736

theorem proof_gap_exercise_2736_1
  (a : (ℕ -> ℝ))
  (x : ℝ)
  (y : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : y ∈ (Set.univ : Set ℝ))
  (h3 : (forall (n : ℕ) (m : ℤ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (m ∈ (Set.univ : Set ℤ))) → ((x + (y /. n)) ≠ ((Real.pi /. 2) + (m * Real.pi))))))
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = ((Real.tan (x + (y /. n))) ^ n)))))
  : Tendsto (fun n : ℕ => (Real.rpow |((Real.rpow (Real.tan (x + (y /. n))) n))| ((n)⁻¹))) atTop (𝓝 |((Real.tan x))|) := by
  sorry

theorem proof_gap_exercise_2736_2
  (a : (ℕ -> ℝ))
  (x : ℝ)
  (y : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : y ∈ (Set.univ : Set ℝ))
  (h3 : (forall (n : ℕ) (m : ℤ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (m ∈ (Set.univ : Set ℤ))) → ((x + (y /. n)) ≠ ((Real.pi /. 2) + (m * Real.pi))))))
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = ((Real.tan (x + (y /. n))) ^ n)))))
  (h5 : Tendsto (fun n : ℕ => (Real.rpow |((Real.rpow (Real.tan (x + (y /. n))) n))| ((n)⁻¹))) atTop (𝓝 |((Real.tan x))|))
  : (exists (k : ℤ), ((k ∈ (Set.univ : Set ℤ)) ∧ (|((x - (k * Real.pi)))| < (Real.pi /. 4)))) → (|((Real.tan x))| < 1) := by
  sorry

theorem proof_gap_exercise_2736_3
  (a : (ℕ -> ℝ))
  (x : ℝ)
  (y : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : y ∈ (Set.univ : Set ℝ))
  (h3 : (forall (n : ℕ) (m : ℤ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (m ∈ (Set.univ : Set ℤ))) → ((x + (y /. n)) ≠ ((Real.pi /. 2) + (m * Real.pi))))))
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = ((Real.tan (x + (y /. n))) ^ n)))))
  (h5 : Tendsto (fun n : ℕ => (Real.rpow |((Real.rpow (Real.tan (x + (y /. n))) n))| ((n)⁻¹))) atTop (𝓝 |((Real.tan x))|))
  (h6 : (exists (k : ℤ), ((k ∈ (Set.univ : Set ℤ)) ∧ (|((x - (k * Real.pi)))| < (Real.pi /. 4)))) → (|((Real.tan x))| < 1))
  : (exists (k : ℤ), ((k ∈ (Set.univ : Set ℤ)) ∧ (|((x - (k * Real.pi)))| < (Real.pi /. 4)))) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((a n))‖ else 0)) := by
  sorry

theorem proof_gap_exercise_2736_4
  (a : (ℕ -> ℝ))
  (x : ℝ)
  (y : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : y ∈ (Set.univ : Set ℝ))
  (h3 : (forall (n : ℕ) (m : ℤ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (m ∈ (Set.univ : Set ℤ))) → ((x + (y /. n)) ≠ ((Real.pi /. 2) + (m * Real.pi))))))
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = ((Real.tan (x + (y /. n))) ^ n)))))
  (h5 : Tendsto (fun n : ℕ => (Real.rpow |((Real.rpow (Real.tan (x + (y /. n))) n))| ((n)⁻¹))) atTop (𝓝 |((Real.tan x))|))
  (h6 : (exists (k : ℤ), ((k ∈ (Set.univ : Set ℤ)) ∧ (|((x - (k * Real.pi)))| < (Real.pi /. 4)))) → (|((Real.tan x))| < 1))
  (h7 : (exists (k : ℤ), ((k ∈ (Set.univ : Set ℤ)) ∧ (|((x - (k * Real.pi)))| < (Real.pi /. 4)))) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((a n))‖ else 0)))
  : (exists (k : ℤ), ((k ∈ (Set.univ : Set ℤ)) ∧ (|((x - (k * Real.pi)))| ≥ (Real.pi /. 4)))) → (|((Real.tan x))| ≥ 1) := by
  sorry

theorem proof_gap_exercise_2736_5
  (a : (ℕ -> ℝ))
  (x : ℝ)
  (y : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : y ∈ (Set.univ : Set ℝ))
  (h3 : (forall (n : ℕ) (m : ℤ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (m ∈ (Set.univ : Set ℤ))) → ((x + (y /. n)) ≠ ((Real.pi /. 2) + (m * Real.pi))))))
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = ((Real.tan (x + (y /. n))) ^ n)))))
  (h5 : Tendsto (fun n : ℕ => (Real.rpow |((Real.rpow (Real.tan (x + (y /. n))) n))| ((n)⁻¹))) atTop (𝓝 |((Real.tan x))|))
  (h6 : (exists (k : ℤ), ((k ∈ (Set.univ : Set ℤ)) ∧ (|((x - (k * Real.pi)))| < (Real.pi /. 4)))) → (|((Real.tan x))| < 1))
  (h7 : (exists (k : ℤ), ((k ∈ (Set.univ : Set ℤ)) ∧ (|((x - (k * Real.pi)))| < (Real.pi /. 4)))) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((a n))‖ else 0)))
  (h8 : (exists (k : ℤ), ((k ∈ (Set.univ : Set ℤ)) ∧ (|((x - (k * Real.pi)))| ≥ (Real.pi /. 4)))) → (|((Real.tan x))| ≥ 1))
  : (exists (k : ℤ), ((k ∈ (Set.univ : Set ℤ)) ∧ (|((x - (k * Real.pi)))| ≥ (Real.pi /. 4)))) → (Tendsto (fun n : ℕ => ((a n) : EReal)) atTop (𝓝 ⊤)) := by
  sorry

theorem proof_gap_exercise_2736_6
  (a : (ℕ -> ℝ))
  (x : ℝ)
  (y : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : y ∈ (Set.univ : Set ℝ))
  (h3 : (forall (n : ℕ) (m : ℤ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (m ∈ (Set.univ : Set ℤ))) → ((x + (y /. n)) ≠ ((Real.pi /. 2) + (m * Real.pi))))))
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = ((Real.tan (x + (y /. n))) ^ n)))))
  (h5 : Tendsto (fun n : ℕ => (Real.rpow |((Real.rpow (Real.tan (x + (y /. n))) n))| ((n)⁻¹))) atTop (𝓝 |((Real.tan x))|))
  (h6 : (exists (k : ℤ), ((k ∈ (Set.univ : Set ℤ)) ∧ (|((x - (k * Real.pi)))| < (Real.pi /. 4)))) → (|((Real.tan x))| < 1))
  (h7 : (exists (k : ℤ), ((k ∈ (Set.univ : Set ℤ)) ∧ (|((x - (k * Real.pi)))| < (Real.pi /. 4)))) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((a n))‖ else 0)))
  (h8 : (exists (k : ℤ), ((k ∈ (Set.univ : Set ℤ)) ∧ (|((x - (k * Real.pi)))| ≥ (Real.pi /. 4)))) → (|((Real.tan x))| ≥ 1))
  (h9 : (exists (k : ℤ), ((k ∈ (Set.univ : Set ℤ)) ∧ (|((x - (k * Real.pi)))| ≥ (Real.pi /. 4)))) → (Tendsto (fun n : ℕ => ((a n) : EReal)) atTop (𝓝 ⊤)))
  : (exists (k : ℤ), ((k ∈ (Set.univ : Set ℤ)) ∧ (|((x - (k * Real.pi)))| ≥ (Real.pi /. 4)))) → (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (a n) else 0)) := by
  sorry

theorem proof_gap_exercise_2736_7
  (a : (ℕ -> ℝ))
  (x : ℝ)
  (y : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : y ∈ (Set.univ : Set ℝ))
  (h3 : (forall (n : ℕ) (m : ℤ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (m ∈ (Set.univ : Set ℤ))) → ((x + (y /. n)) ≠ ((Real.pi /. 2) + (m * Real.pi))))))
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((a n) = ((Real.tan (x + (y /. n))) ^ n)))))
  (h5 : Tendsto (fun n : ℕ => (Real.rpow |((Real.rpow (Real.tan (x + (y /. n))) n))| ((n)⁻¹))) atTop (𝓝 |((Real.tan x))|))
  (h6 : (exists (k : ℤ), ((k ∈ (Set.univ : Set ℤ)) ∧ (|((x - (k * Real.pi)))| < (Real.pi /. 4)))) → (|((Real.tan x))| < 1))
  (h7 : (exists (k : ℤ), ((k ∈ (Set.univ : Set ℤ)) ∧ (|((x - (k * Real.pi)))| < (Real.pi /. 4)))) → (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((a n))‖ else 0)))
  (h8 : (exists (k : ℤ), ((k ∈ (Set.univ : Set ℤ)) ∧ (|((x - (k * Real.pi)))| ≥ (Real.pi /. 4)))) → (|((Real.tan x))| ≥ 1))
  (h9 : (exists (k : ℤ), ((k ∈ (Set.univ : Set ℤ)) ∧ (|((x - (k * Real.pi)))| ≥ (Real.pi /. 4)))) → (Tendsto (fun n : ℕ => ((a n) : EReal)) atTop (𝓝 ⊤)))
  (h10 : (exists (k : ℤ), ((k ∈ (Set.univ : Set ℤ)) ∧ (|((x - (k * Real.pi)))| ≥ (Real.pi /. 4)))) → (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (a n) else 0)))
  : ((x, y) ∈ ({p | p = (x, y) ∧ ((exists (k : ℤ), (((k ∈ (Set.univ : Set ℤ)) ∧ (|((x - (k * Real.pi)))| < (Real.pi /. 4))) ∧ (Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then ‖((a n))‖ else 0)))) ∨ (exists (k : ℤ), (((k ∈ (Set.univ : Set ℤ)) ∧ (|((x - (k * Real.pi)))| ≥ (Real.pi /. 4))) ∧ (¬ Summable (fun (n : ℕ) => if (1 : ℕ) ≤ n then (a n) else 0)))))})) ↔ ((x ∈ (Set.univ : Set ℝ)) ∧ (y ∈ (Set.univ : Set ℝ))) := by
  sorry
