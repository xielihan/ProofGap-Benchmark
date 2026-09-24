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

-- exercise: exercise_2868

theorem proof_gap_exercise_2868_1
  (x : ℝ)
  (v_uCE_uB1 : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : v_uCE_uB1 ∈ (Set.univ : Set ℝ))
  : (Complex.exp ((x * (Real.cos v_uCE_uB1)) + ((Complex.I * x) * (Real.sin v_uCE_uB1)))) = (Complex.exp (x * ((Real.cos v_uCE_uB1) + (Complex.I * (Real.sin v_uCE_uB1))))) := by
  sorry

theorem proof_gap_exercise_2868_2
  (x : ℝ)
  (v_uCE_uB1 : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : v_uCE_uB1 ∈ (Set.univ : Set ℝ))
  (h3 : (Complex.exp ((x * (Real.cos v_uCE_uB1)) + ((Complex.I * x) * (Real.sin v_uCE_uB1)))) = (Complex.exp (x * ((Real.cos v_uCE_uB1) + (Complex.I * (Real.sin v_uCE_uB1))))))
  : (Complex.exp (x * ((Real.cos v_uCE_uB1) + (Complex.I * (Real.sin v_uCE_uB1))))) = (Complex.exp (x * (Complex.exp (Complex.I * v_uCE_uB1)))) := by
  sorry

theorem proof_gap_exercise_2868_3
  (x : ℝ)
  (v_uCE_uB1 : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : v_uCE_uB1 ∈ (Set.univ : Set ℝ))
  (h3 : (Complex.exp ((x * (Real.cos v_uCE_uB1)) + ((Complex.I * x) * (Real.sin v_uCE_uB1)))) = (Complex.exp (x * ((Real.cos v_uCE_uB1) + (Complex.I * (Real.sin v_uCE_uB1))))))
  (h4 : (Complex.exp (x * ((Real.cos v_uCE_uB1) + (Complex.I * (Real.sin v_uCE_uB1))))) = (Complex.exp (x * (Complex.exp (Complex.I * v_uCE_uB1)))))
  : (Complex.exp ((x * (Real.cos v_uCE_uB1)) + ((Complex.I * x) * (Real.sin v_uCE_uB1)))) = (Complex.exp (x * (Complex.exp (Complex.I * v_uCE_uB1)))) := by
  sorry

theorem proof_gap_exercise_2868_4
  (x : ℝ)
  (v_uCE_uB1 : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : v_uCE_uB1 ∈ (Set.univ : Set ℝ))
  (h3 : (Complex.exp ((x * (Real.cos v_uCE_uB1)) + ((Complex.I * x) * (Real.sin v_uCE_uB1)))) = (Complex.exp (x * ((Real.cos v_uCE_uB1) + (Complex.I * (Real.sin v_uCE_uB1))))))
  (h4 : (Complex.exp (x * ((Real.cos v_uCE_uB1) + (Complex.I * (Real.sin v_uCE_uB1))))) = (Complex.exp (x * (Complex.exp (Complex.I * v_uCE_uB1)))))
  (h5 : (Complex.exp ((x * (Real.cos v_uCE_uB1)) + ((Complex.I * x) * (Real.sin v_uCE_uB1)))) = (Complex.exp (x * (Complex.exp (Complex.I * v_uCE_uB1)))))
  : (Complex.exp (x * (Complex.exp (Complex.I * v_uCE_uB1)))) = (∑' n, if (0 : ℕ) ≤ n then ((1 /. (n)!) * ((x * (Complex.exp (Complex.I * v_uCE_uB1))) ^ n)) else 0) := by
  sorry

theorem proof_gap_exercise_2868_5
  (x : ℝ)
  (v_uCE_uB1 : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : v_uCE_uB1 ∈ (Set.univ : Set ℝ))
  (h3 : (Complex.exp ((x * (Real.cos v_uCE_uB1)) + ((Complex.I * x) * (Real.sin v_uCE_uB1)))) = (Complex.exp (x * ((Real.cos v_uCE_uB1) + (Complex.I * (Real.sin v_uCE_uB1))))))
  (h4 : (Complex.exp (x * ((Real.cos v_uCE_uB1) + (Complex.I * (Real.sin v_uCE_uB1))))) = (Complex.exp (x * (Complex.exp (Complex.I * v_uCE_uB1)))))
  (h5 : (Complex.exp ((x * (Real.cos v_uCE_uB1)) + ((Complex.I * x) * (Real.sin v_uCE_uB1)))) = (Complex.exp (x * (Complex.exp (Complex.I * v_uCE_uB1)))))
  (h6 : (Complex.exp (x * (Complex.exp (Complex.I * v_uCE_uB1)))) = (∑' n, if (0 : ℕ) ≤ n then ((1 /. (n)!) * ((x * (Complex.exp (Complex.I * v_uCE_uB1))) ^ n)) else 0))
  : (∑' n, if (0 : ℕ) ≤ n then ((1 /. (n)!) * ((x * (Complex.exp (Complex.I * v_uCE_uB1))) ^ n)) else 0) = (∑' n, if (0 : ℕ) ≤ n then (((x ^ n) /. (n)!) * (Complex.exp ((Complex.I * n) * v_uCE_uB1))) else 0) := by
  sorry

theorem proof_gap_exercise_2868_6
  (x : ℝ)
  (v_uCE_uB1 : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : v_uCE_uB1 ∈ (Set.univ : Set ℝ))
  (h3 : (Complex.exp ((x * (Real.cos v_uCE_uB1)) + ((Complex.I * x) * (Real.sin v_uCE_uB1)))) = (Complex.exp (x * ((Real.cos v_uCE_uB1) + (Complex.I * (Real.sin v_uCE_uB1))))))
  (h4 : (Complex.exp (x * ((Real.cos v_uCE_uB1) + (Complex.I * (Real.sin v_uCE_uB1))))) = (Complex.exp (x * (Complex.exp (Complex.I * v_uCE_uB1)))))
  (h5 : (Complex.exp ((x * (Real.cos v_uCE_uB1)) + ((Complex.I * x) * (Real.sin v_uCE_uB1)))) = (Complex.exp (x * (Complex.exp (Complex.I * v_uCE_uB1)))))
  (h6 : (Complex.exp (x * (Complex.exp (Complex.I * v_uCE_uB1)))) = (∑' n, if (0 : ℕ) ≤ n then ((1 /. (n)!) * ((x * (Complex.exp (Complex.I * v_uCE_uB1))) ^ n)) else 0))
  (h7 : (∑' n, if (0 : ℕ) ≤ n then ((1 /. (n)!) * ((x * (Complex.exp (Complex.I * v_uCE_uB1))) ^ n)) else 0) = (∑' n, if (0 : ℕ) ≤ n then (((x ^ n) /. (n)!) * (Complex.exp ((Complex.I * n) * v_uCE_uB1))) else 0))
  : (Complex.exp (x * (Complex.exp (Complex.I * v_uCE_uB1)))) = (∑' n, if (0 : ℕ) ≤ n then (((x ^ n) /. (n)!) * (Complex.exp ((Complex.I * n) * v_uCE_uB1))) else 0) := by
  sorry

theorem proof_gap_exercise_2868_7
  (x : ℝ)
  (v_uCE_uB1 : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : v_uCE_uB1 ∈ (Set.univ : Set ℝ))
  (h3 : (Complex.exp ((x * (Real.cos v_uCE_uB1)) + ((Complex.I * x) * (Real.sin v_uCE_uB1)))) = (Complex.exp (x * ((Real.cos v_uCE_uB1) + (Complex.I * (Real.sin v_uCE_uB1))))))
  (h4 : (Complex.exp (x * ((Real.cos v_uCE_uB1) + (Complex.I * (Real.sin v_uCE_uB1))))) = (Complex.exp (x * (Complex.exp (Complex.I * v_uCE_uB1)))))
  (h5 : (Complex.exp ((x * (Real.cos v_uCE_uB1)) + ((Complex.I * x) * (Real.sin v_uCE_uB1)))) = (Complex.exp (x * (Complex.exp (Complex.I * v_uCE_uB1)))))
  (h6 : (Complex.exp (x * (Complex.exp (Complex.I * v_uCE_uB1)))) = (∑' n, if (0 : ℕ) ≤ n then ((1 /. (n)!) * ((x * (Complex.exp (Complex.I * v_uCE_uB1))) ^ n)) else 0))
  (h7 : (∑' n, if (0 : ℕ) ≤ n then ((1 /. (n)!) * ((x * (Complex.exp (Complex.I * v_uCE_uB1))) ^ n)) else 0) = (∑' n, if (0 : ℕ) ≤ n then (((x ^ n) /. (n)!) * (Complex.exp ((Complex.I * n) * v_uCE_uB1))) else 0))
  (h8 : (Complex.exp (x * (Complex.exp (Complex.I * v_uCE_uB1)))) = (∑' n, if (0 : ℕ) ≤ n then (((x ^ n) /. (n)!) * (Complex.exp ((Complex.I * n) * v_uCE_uB1))) else 0))
  : (Complex.exp (x * (Complex.exp (Complex.I * v_uCE_uB1)))) = (∑' n, if (0 : ℕ) ≤ n then (((x ^ n) /. (n)!) * ((Real.cos (n * v_uCE_uB1)) + (Complex.I * (Real.sin (n * v_uCE_uB1))))) else 0) := by
  sorry

theorem proof_gap_exercise_2868_8
  (x : ℝ)
  (v_uCE_uB1 : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : v_uCE_uB1 ∈ (Set.univ : Set ℝ))
  (h3 : (Complex.exp ((x * (Real.cos v_uCE_uB1)) + ((Complex.I * x) * (Real.sin v_uCE_uB1)))) = (Complex.exp (x * ((Real.cos v_uCE_uB1) + (Complex.I * (Real.sin v_uCE_uB1))))))
  (h4 : (Complex.exp (x * ((Real.cos v_uCE_uB1) + (Complex.I * (Real.sin v_uCE_uB1))))) = (Complex.exp (x * (Complex.exp (Complex.I * v_uCE_uB1)))))
  (h5 : (Complex.exp ((x * (Real.cos v_uCE_uB1)) + ((Complex.I * x) * (Real.sin v_uCE_uB1)))) = (Complex.exp (x * (Complex.exp (Complex.I * v_uCE_uB1)))))
  (h6 : (Complex.exp (x * (Complex.exp (Complex.I * v_uCE_uB1)))) = (∑' n, if (0 : ℕ) ≤ n then ((1 /. (n)!) * ((x * (Complex.exp (Complex.I * v_uCE_uB1))) ^ n)) else 0))
  (h7 : (∑' n, if (0 : ℕ) ≤ n then ((1 /. (n)!) * ((x * (Complex.exp (Complex.I * v_uCE_uB1))) ^ n)) else 0) = (∑' n, if (0 : ℕ) ≤ n then (((x ^ n) /. (n)!) * (Complex.exp ((Complex.I * n) * v_uCE_uB1))) else 0))
  (h8 : (Complex.exp (x * (Complex.exp (Complex.I * v_uCE_uB1)))) = (∑' n, if (0 : ℕ) ≤ n then (((x ^ n) /. (n)!) * (Complex.exp ((Complex.I * n) * v_uCE_uB1))) else 0))
  (h9 : (Complex.exp (x * (Complex.exp (Complex.I * v_uCE_uB1)))) = (∑' n, if (0 : ℕ) ≤ n then (((x ^ n) /. (n)!) * ((Real.cos (n * v_uCE_uB1)) + (Complex.I * (Real.sin (n * v_uCE_uB1))))) else 0))
  : ((Real.exp (x * (Real.cos v_uCE_uB1))) * (Real.cos (x * (Real.sin v_uCE_uB1)))) = (∑' n, if (0 : ℕ) ≤ n then (((Real.cos (n * v_uCE_uB1)) /. (n)!) * (x ^ n)) else 0) := by
  sorry

theorem proof_gap_exercise_2868_9
  (x : ℝ)
  (v_uCE_uB1 : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : v_uCE_uB1 ∈ (Set.univ : Set ℝ))
  (h3 : (Complex.exp ((x * (Real.cos v_uCE_uB1)) + ((Complex.I * x) * (Real.sin v_uCE_uB1)))) = (Complex.exp (x * ((Real.cos v_uCE_uB1) + (Complex.I * (Real.sin v_uCE_uB1))))))
  (h4 : (Complex.exp (x * ((Real.cos v_uCE_uB1) + (Complex.I * (Real.sin v_uCE_uB1))))) = (Complex.exp (x * (Complex.exp (Complex.I * v_uCE_uB1)))))
  (h5 : (Complex.exp ((x * (Real.cos v_uCE_uB1)) + ((Complex.I * x) * (Real.sin v_uCE_uB1)))) = (Complex.exp (x * (Complex.exp (Complex.I * v_uCE_uB1)))))
  (h6 : (Complex.exp (x * (Complex.exp (Complex.I * v_uCE_uB1)))) = (∑' n, if (0 : ℕ) ≤ n then ((1 /. (n)!) * ((x * (Complex.exp (Complex.I * v_uCE_uB1))) ^ n)) else 0))
  (h7 : (∑' n, if (0 : ℕ) ≤ n then ((1 /. (n)!) * ((x * (Complex.exp (Complex.I * v_uCE_uB1))) ^ n)) else 0) = (∑' n, if (0 : ℕ) ≤ n then (((x ^ n) /. (n)!) * (Complex.exp ((Complex.I * n) * v_uCE_uB1))) else 0))
  (h8 : (Complex.exp (x * (Complex.exp (Complex.I * v_uCE_uB1)))) = (∑' n, if (0 : ℕ) ≤ n then (((x ^ n) /. (n)!) * (Complex.exp ((Complex.I * n) * v_uCE_uB1))) else 0))
  (h9 : (Complex.exp (x * (Complex.exp (Complex.I * v_uCE_uB1)))) = (∑' n, if (0 : ℕ) ≤ n then (((x ^ n) /. (n)!) * ((Real.cos (n * v_uCE_uB1)) + (Complex.I * (Real.sin (n * v_uCE_uB1))))) else 0))
  (h10 : ((Real.exp (x * (Real.cos v_uCE_uB1))) * (Real.cos (x * (Real.sin v_uCE_uB1)))) = (∑' n, if (0 : ℕ) ≤ n then (((Real.cos (n * v_uCE_uB1)) /. (n)!) * (x ^ n)) else 0))
  : ((Real.exp (x * (Real.cos v_uCE_uB1))) * (Real.sin (x * (Real.sin v_uCE_uB1)))) = (∑' n, if (0 : ℕ) ≤ n then (((Real.sin (n * v_uCE_uB1)) /. (n)!) * (x ^ n)) else 0) := by
  sorry
