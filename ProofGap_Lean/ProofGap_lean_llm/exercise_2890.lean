import Mathlib

set_option linter.style.longLine false

open scoped BigOperators Topology
open Filter

local infixl:70 " /. " => fun x y => ((x : ℝ) / (y : ℝ))

-- exercise: exercise_2890

noncomputable def eg2890Phi (x : ℝ) : ℝ := (Real.arcsin x) ^ (2 : ℕ)
noncomputable def eg2890FunDeri (φ : ℝ -> ℝ) (_dim order : ℕ) : ℝ -> ℝ :=
  iteratedDeriv order φ
def eg2890Interior (x : ℝ) : Prop := x ∈ (Set.univ : Set ℝ) ∧ -1 < x ∧ x < 1
def eg2890Domain (x : ℝ) : Prop := x ∈ (Set.univ : Set ℝ) ∧ -1 ≤ x ∧ x ≤ 1 ∧ x ≠ 0
noncomputable def eg2890Coeff (k : ℕ) : ℝ :=
  ((2 : ℝ) ^ (2 * k + 1) * ((Nat.factorial k : ℝ) ^ (2 : ℕ))) /. (Nat.factorial (2 * k + 2))
noncomputable def eg2890Series (x : ℝ) : ℝ :=
  ∑' k : ℕ, eg2890Coeff k * x ^ (2 * k)
noncomputable def eg2890Tail3 (x : ℝ) : ℝ :=
  ∑' k : ℕ, if 3 ≤ k then eg2890Coeff k * x ^ (2 * k) else 0

theorem proof_gap_exercise_2890_1
  (f : ℝ -> ℝ) (a : ℕ -> ℝ)
  (hf : ∀ x : ℝ, eg2890Domain x → f x = (Real.arcsin x /. x) ^ (2 : ℕ))
  (hφ : eg2890Phi = fun x => (Real.arcsin x) ^ (2 : ℕ)) :
  ∀ x : ℝ, eg2890Interior x → eg2890Phi x = (∑' n : ℕ, a n * x ^ n) := by
  sorry

theorem proof_gap_exercise_2890_2
  (f : ℝ -> ℝ) (a : ℕ -> ℝ)
  (hf : ∀ x : ℝ, eg2890Domain x → f x = (Real.arcsin x /. x) ^ (2 : ℕ))
  (hφ : eg2890Phi = fun x => (Real.arcsin x) ^ (2 : ℕ))
  (h1 : ∀ x : ℝ, eg2890Interior x → eg2890Phi x = (∑' n : ℕ, a n * x ^ n)) :
  ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) → a n ∈ (Set.univ : Set ℝ) := by
  sorry

theorem proof_gap_exercise_2890_3
  (f : ℝ -> ℝ) (a : ℕ -> ℝ)
  (hf : ∀ x : ℝ, eg2890Domain x → f x = (Real.arcsin x /. x) ^ (2 : ℕ))
  (hφ : eg2890Phi = fun x => (Real.arcsin x) ^ (2 : ℕ))
  (h1 : ∀ x : ℝ, eg2890Interior x → eg2890Phi x = (∑' n : ℕ, a n * x ^ n))
  (h2 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) → a n ∈ (Set.univ : Set ℝ)) :
  ∀ x : ℝ, eg2890Interior x →
    eg2890FunDeri eg2890Phi 1 1 x = (2 * Real.arcsin x) /. Real.sqrt (1 - x ^ (2 : ℕ)) ∧
      (2 * Real.arcsin x) /. Real.sqrt (1 - x ^ (2 : ℕ)) = (∑' n : ℕ, (n + 1 : ℝ) * a (n + 1) * x ^ n) := by
  sorry

theorem proof_gap_exercise_2890_4
  (f : ℝ -> ℝ) (a : ℕ -> ℝ)
  (hf : ∀ x : ℝ, eg2890Domain x → f x = (Real.arcsin x /. x) ^ (2 : ℕ))
  (hφ : eg2890Phi = fun x => (Real.arcsin x) ^ (2 : ℕ))
  (h3 : ∀ x : ℝ, eg2890Interior x → eg2890FunDeri eg2890Phi 1 1 x = (2 * Real.arcsin x) /. Real.sqrt (1 - x ^ (2 : ℕ)) ∧ ((2 * Real.arcsin x) /. Real.sqrt (1 - x ^ (2 : ℕ)) = (∑' n : ℕ, (n + 1 : ℝ) * a (n + 1) * x ^ n))) :
  eg2890Phi 0 = 0 := by
  sorry

theorem proof_gap_exercise_2890_5
  (f : ℝ -> ℝ) (a : ℕ -> ℝ)
  (hf : ∀ x : ℝ, eg2890Domain x → f x = (Real.arcsin x /. x) ^ (2 : ℕ))
  (hφ : eg2890Phi = fun x => (Real.arcsin x) ^ (2 : ℕ))
  (h4 : eg2890Phi 0 = 0) :
  eg2890FunDeri eg2890Phi 1 1 0 = 0 := by
  sorry

theorem proof_gap_exercise_2890_6
  (f : ℝ -> ℝ) (a : ℕ -> ℝ)
  (hf : ∀ x : ℝ, eg2890Domain x → f x = (Real.arcsin x /. x) ^ (2 : ℕ))
  (hφ : eg2890Phi = fun x => (Real.arcsin x) ^ (2 : ℕ))
  (h1 : ∀ x : ℝ, eg2890Interior x → eg2890Phi x = (∑' n : ℕ, a n * x ^ n))
  (h4 : eg2890Phi 0 = 0)
  (h5 : eg2890FunDeri eg2890Phi 1 1 0 = 0) :
  a 0 = 0 := by
  sorry

theorem proof_gap_exercise_2890_7
  (f : ℝ -> ℝ) (a : ℕ -> ℝ)
  (hf : ∀ x : ℝ, eg2890Domain x → f x = (Real.arcsin x /. x) ^ (2 : ℕ))
  (hφ : eg2890Phi = fun x => (Real.arcsin x) ^ (2 : ℕ))
  (h3 : ∀ x : ℝ, eg2890Interior x → eg2890FunDeri eg2890Phi 1 1 x = (2 * Real.arcsin x) /. Real.sqrt (1 - x ^ (2 : ℕ)) ∧ ((2 * Real.arcsin x) /. Real.sqrt (1 - x ^ (2 : ℕ)) = (∑' n : ℕ, (n + 1 : ℝ) * a (n + 1) * x ^ n)))
  (h6 : a 0 = 0) :
  a 1 = 0 := by
  sorry

theorem proof_gap_exercise_2890_8
  (f : ℝ -> ℝ) (a : ℕ -> ℝ)
  (hf : ∀ x : ℝ, eg2890Domain x → f x = (Real.arcsin x /. x) ^ (2 : ℕ))
  (hφ : eg2890Phi = fun x => (Real.arcsin x) ^ (2 : ℕ))
  (h7 : a 1 = 0) :
  ∀ x : ℝ, eg2890Interior x →
    Real.sqrt (1 - x ^ (2 : ℕ)) * eg2890FunDeri eg2890Phi 1 1 x = 2 * Real.arcsin x := by
  sorry

theorem proof_gap_exercise_2890_9
  (f : ℝ -> ℝ) (a : ℕ -> ℝ)
  (hf : ∀ x : ℝ, eg2890Domain x → f x = (Real.arcsin x /. x) ^ (2 : ℕ))
  (hφ : eg2890Phi = fun x => (Real.arcsin x) ^ (2 : ℕ))
  (h8 : ∀ x : ℝ, eg2890Interior x → Real.sqrt (1 - x ^ (2 : ℕ)) * eg2890FunDeri eg2890Phi 1 1 x = 2 * Real.arcsin x) :
  ∀ x : ℝ, eg2890Interior x →
    Real.sqrt (1 - x ^ (2 : ℕ)) * eg2890FunDeri eg2890Phi 1 2 x -
      (x * eg2890FunDeri eg2890Phi 1 1 x) /. Real.sqrt (1 - x ^ (2 : ℕ)) =
        2 /. Real.sqrt (1 - x ^ (2 : ℕ)) := by
  sorry

theorem proof_gap_exercise_2890_10
  (f : ℝ -> ℝ) (a : ℕ -> ℝ)
  (hf : ∀ x : ℝ, eg2890Domain x → f x = (Real.arcsin x /. x) ^ (2 : ℕ))
  (hφ : eg2890Phi = fun x => (Real.arcsin x) ^ (2 : ℕ))
  (h9 : ∀ x : ℝ, eg2890Interior x → Real.sqrt (1 - x ^ (2 : ℕ)) * eg2890FunDeri eg2890Phi 1 2 x - ((x * eg2890FunDeri eg2890Phi 1 1 x) /. Real.sqrt (1 - x ^ (2 : ℕ))) = 2 /. Real.sqrt (1 - x ^ (2 : ℕ))) :
  ∀ x : ℝ, eg2890Interior x →
    (1 - x ^ (2 : ℕ)) * eg2890FunDeri eg2890Phi 1 2 x - x * eg2890FunDeri eg2890Phi 1 1 x = 2 := by
  sorry

theorem proof_gap_exercise_2890_11
  (f : ℝ -> ℝ) (a : ℕ -> ℝ)
  (hf : ∀ x : ℝ, eg2890Domain x → f x = (Real.arcsin x /. x) ^ (2 : ℕ))
  (hφ : eg2890Phi = fun x => (Real.arcsin x) ^ (2 : ℕ))
  (h10 : ∀ x : ℝ, eg2890Interior x → (1 - x ^ (2 : ℕ)) * eg2890FunDeri eg2890Phi 1 2 x - x * eg2890FunDeri eg2890Phi 1 1 x = 2) :
  ∀ x : ℝ, eg2890Interior x →
    (1 - x ^ (2 : ℕ)) * (∑' n : ℕ, if 2 ≤ n then (n : ℝ) * (n - 1 : ℝ) * a n * x ^ (n - 2) else 0) -
      (∑' n : ℕ, if 2 ≤ n then (n : ℝ) * a n * x ^ n else 0) = 2 := by
  sorry

theorem proof_gap_exercise_2890_12
  (f : ℝ -> ℝ) (a : ℕ -> ℝ)
  (hf : ∀ x : ℝ, eg2890Domain x → f x = (Real.arcsin x /. x) ^ (2 : ℕ))
  (hφ : eg2890Phi = fun x => (Real.arcsin x) ^ (2 : ℕ))
  (h11 : ∀ x : ℝ, eg2890Interior x → (1 - x ^ (2 : ℕ)) * (∑' n : ℕ, if 2 ≤ n then (n : ℝ) * (n - 1 : ℝ) * a n * x ^ (n - 2) else 0) - (∑' n : ℕ, if 2 ≤ n then (n : ℝ) * a n * x ^ n else 0) = 2) :
  ∀ x : ℝ, eg2890Interior x →
    (∑' n : ℕ, if 2 ≤ n then (n : ℝ) * (n - 1 : ℝ) * a n * x ^ (n - 2) else 0) -
      (∑' n : ℕ, if 2 ≤ n then ((n : ℝ) ^ (2 : ℕ)) * a n * x ^ n else 0) = 2 := by
  sorry

theorem proof_gap_exercise_2890_13
  (f : ℝ -> ℝ) (a : ℕ -> ℝ)
  (hf : ∀ x : ℝ, eg2890Domain x → f x = (Real.arcsin x /. x) ^ (2 : ℕ))
  (hφ : eg2890Phi = fun x => (Real.arcsin x) ^ (2 : ℕ))
  (h12 : ∀ x : ℝ, eg2890Interior x → (∑' n : ℕ, if 2 ≤ n then (n : ℝ) * (n - 1 : ℝ) * a n * x ^ (n - 2) else 0) - (∑' n : ℕ, if 2 ≤ n then ((n : ℝ) ^ (2 : ℕ)) * a n * x ^ n else 0) = 2) :
  ∀ x : ℝ, eg2890Interior x →
    2 * a 2 + 6 * a 3 * x +
      (∑' n : ℕ, if 2 ≤ n then (((n + 2 : ℝ) * (n + 1 : ℝ) * a (n + 2) - ((n : ℝ) ^ (2 : ℕ)) * a n) * x ^ n) else 0) = 2 := by
  sorry

theorem proof_gap_exercise_2890_14
  (f : ℝ -> ℝ) (a : ℕ -> ℝ)
  (hf : ∀ x : ℝ, eg2890Domain x → f x = (Real.arcsin x /. x) ^ (2 : ℕ))
  (hφ : eg2890Phi = fun x => (Real.arcsin x) ^ (2 : ℕ))
  (h13 : ∀ x : ℝ, eg2890Interior x → 2 * a 2 + 6 * a 3 * x + (∑' n : ℕ, if 2 ≤ n then (((n + 2 : ℝ) * (n + 1 : ℝ) * a (n + 2) - ((n : ℝ) ^ (2 : ℕ)) * a n) * x ^ n) else 0) = 2) :
  a 2 = 1 := by
  sorry

theorem proof_gap_exercise_2890_15
  (f : ℝ -> ℝ) (a : ℕ -> ℝ)
  (hf : ∀ x : ℝ, eg2890Domain x → f x = (Real.arcsin x /. x) ^ (2 : ℕ))
  (hφ : eg2890Phi = fun x => (Real.arcsin x) ^ (2 : ℕ))
  (h14 : a 2 = 1) :
  a 3 = 0 := by
  sorry

theorem proof_gap_exercise_2890_16
  (f : ℝ -> ℝ) (a : ℕ -> ℝ)
  (hf : ∀ x : ℝ, eg2890Domain x → f x = (Real.arcsin x /. x) ^ (2 : ℕ))
  (hφ : eg2890Phi = fun x => (Real.arcsin x) ^ (2 : ℕ))
  (h13 : ∀ x : ℝ, eg2890Interior x → 2 * a 2 + 6 * a 3 * x + (∑' n : ℕ, if 2 ≤ n then (((n + 2 : ℝ) * (n + 1 : ℝ) * a (n + 2) - ((n : ℝ) ^ (2 : ℕ)) * a n) * x ^ n) else 0) = 2)
  (h14 : a 2 = 1)
  (h15 : a 3 = 0) :
  ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ n ≥ 2 →
    a (n + 2) = (((n : ℝ) ^ (2 : ℕ)) /. ((n + 2 : ℝ) * (n + 1 : ℝ))) * a n := by
  sorry

theorem proof_gap_exercise_2890_17
  (f : ℝ -> ℝ) (a : ℕ -> ℝ)
  (hf : ∀ x : ℝ, eg2890Domain x → f x = (Real.arcsin x /. x) ^ (2 : ℕ))
  (hφ : eg2890Phi = fun x => (Real.arcsin x) ^ (2 : ℕ))
  (h15 : a 3 = 0)
  (h16 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ n ≥ 2 → a (n + 2) = (((n : ℝ) ^ (2 : ℕ)) /. ((n + 2 : ℝ) * (n + 1 : ℝ))) * a n) :
  ∀ k : ℕ, k ∈ (Set.univ : Set ℕ) → a (2 * k + 1) = 0 := by
  sorry

theorem proof_gap_exercise_2890_18
  (f : ℝ -> ℝ) (a : ℕ -> ℝ)
  (hf : ∀ x : ℝ, eg2890Domain x → f x = (Real.arcsin x /. x) ^ (2 : ℕ))
  (hφ : eg2890Phi = fun x => (Real.arcsin x) ^ (2 : ℕ))
  (h14 : a 2 = 1)
  (h16 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ n ≥ 2 → a (n + 2) = (((n : ℝ) ^ (2 : ℕ)) /. ((n + 2 : ℝ) * (n + 1 : ℝ))) * a n) :
  ∀ k : ℕ, k ∈ (Set.univ : Set ℕ) → a (2 * k + 2) = eg2890Coeff k := by
  sorry

theorem proof_gap_exercise_2890_19
  (f : ℝ -> ℝ) (a : ℕ -> ℝ)
  (hf : ∀ x : ℝ, eg2890Domain x → f x = (Real.arcsin x /. x) ^ (2 : ℕ))
  (hφ : eg2890Phi = fun x => (Real.arcsin x) ^ (2 : ℕ))
  (h1 : ∀ x : ℝ, eg2890Interior x → eg2890Phi x = (∑' n : ℕ, a n * x ^ n))
  (h17 : ∀ k : ℕ, k ∈ (Set.univ : Set ℕ) → a (2 * k + 1) = 0)
  (h18 : ∀ k : ℕ, k ∈ (Set.univ : Set ℕ) → a (2 * k + 2) = eg2890Coeff k) :
  ∀ x : ℝ, eg2890Interior x →
    eg2890Phi x = (∑' k : ℕ, eg2890Coeff k * x ^ (2 * k + 2)) := by
  sorry

theorem proof_gap_exercise_2890_20
  (f : ℝ -> ℝ) (a : ℕ -> ℝ)
  (hf : ∀ x : ℝ, eg2890Domain x → f x = (Real.arcsin x /. x) ^ (2 : ℕ))
  (hφ : eg2890Phi = fun x => (Real.arcsin x) ^ (2 : ℕ))
  (h19 : ∀ x : ℝ, eg2890Interior x → eg2890Phi x = (∑' k : ℕ, eg2890Coeff k * x ^ (2 * k + 2))) :
  ∀ x : ℝ, eg2890Interior x ∧ x ≠ 0 →
    f x = eg2890Series x := by
  sorry

theorem proof_gap_exercise_2890_21
  (f : ℝ -> ℝ) (a : ℕ -> ℝ)
  (hf : ∀ x : ℝ, eg2890Domain x → f x = (Real.arcsin x /. x) ^ (2 : ℕ))
  (hφ : eg2890Phi = fun x => (Real.arcsin x) ^ (2 : ℕ))
  (h20 : ∀ x : ℝ, eg2890Interior x ∧ x ≠ 0 → f x = eg2890Series x) :
  ∀ x : ℝ, eg2890Interior x →
    eg2890Series x = 1 + (1 /. 3) * x ^ (2 : ℕ) + (8 /. 45) * x ^ (4 : ℕ) + eg2890Tail3 x := by
  sorry

theorem proof_gap_exercise_2890_22
  (f : ℝ -> ℝ) (a : ℕ -> ℝ)
  (hf : ∀ x : ℝ, eg2890Domain x → f x = (Real.arcsin x /. x) ^ (2 : ℕ))
  (hφ : eg2890Phi = fun x => (Real.arcsin x) ^ (2 : ℕ))
  (h20 : ∀ x : ℝ, eg2890Interior x ∧ x ≠ 0 → f x = eg2890Series x)
  (h21 : ∀ x : ℝ, eg2890Interior x → eg2890Series x = 1 + (1 /. 3) * x ^ (2 : ℕ) + (8 /. 45) * x ^ (4 : ℕ) + eg2890Tail3 x) :
  ∀ x : ℝ, eg2890Domain x → f x = eg2890Series x := by
  sorry

theorem proof_gap_exercise_2890_23
  (f : ℝ -> ℝ) (a : ℕ -> ℝ)
  (hf : ∀ x : ℝ, eg2890Domain x → f x = (Real.arcsin x /. x) ^ (2 : ℕ))
  (hφ : eg2890Phi = fun x => (Real.arcsin x) ^ (2 : ℕ))
  (h21 : ∀ x : ℝ, eg2890Interior x → eg2890Series x = 1 + (1 /. 3) * x ^ (2 : ℕ) + (8 /. 45) * x ^ (4 : ℕ) + eg2890Tail3 x)
  (h22 : ∀ x : ℝ, eg2890Domain x → f x = eg2890Series x) :
  ∀ x : ℝ, eg2890Domain x →
    f x = 1 + (1 /. 3) * x ^ (2 : ℕ) + (8 /. 45) * x ^ (4 : ℕ) + eg2890Tail3 x := by
  sorry
