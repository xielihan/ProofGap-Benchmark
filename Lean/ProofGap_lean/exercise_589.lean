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

-- exercise: exercise_589

theorem proof_gap_exercise_589_1
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → (((x ^ (2 : ℕ)) + 1) > 0))) := by
  sorry

theorem proof_gap_exercise_589_2
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → (((x ^ (2 : ℕ)) + 1) > 0))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((Real.rpow ((x ^ (2 : ℕ)) + 1) (((2 : ℝ))⁻¹)) ≠ 0))) := by
  sorry

theorem proof_gap_exercise_589_3
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → (((x ^ (2 : ℕ)) + 1) > 0))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((Real.rpow ((x ^ (2 : ℕ)) + 1) (((2 : ℝ))⁻¹)) ≠ 0))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → (0 < (x /. (Real.rpow ((x ^ (2 : ℕ)) + 1) (((2 : ℝ))⁻¹)))))) := by
  sorry

theorem proof_gap_exercise_589_4
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → (((x ^ (2 : ℕ)) + 1) > 0))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((Real.rpow ((x ^ (2 : ℕ)) + 1) (((2 : ℝ))⁻¹)) ≠ 0))))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → (0 < (x /. (Real.rpow ((x ^ (2 : ℕ)) + 1) (((2 : ℝ))⁻¹)))))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((x /. (Real.rpow ((x ^ (2 : ℕ)) + 1) (((2 : ℝ))⁻¹))) < 1))) := by
  sorry

theorem proof_gap_exercise_589_5
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → (((x ^ (2 : ℕ)) + 1) > 0))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((Real.rpow ((x ^ (2 : ℕ)) + 1) (((2 : ℝ))⁻¹)) ≠ 0))))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → (0 < (x /. (Real.rpow ((x ^ (2 : ℕ)) + 1) (((2 : ℝ))⁻¹)))))))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((x /. (Real.rpow ((x ^ (2 : ℕ)) + 1) (((2 : ℝ))⁻¹))) < 1))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → (0 < (1 /. (Real.rpow ((x ^ (2 : ℕ)) + 1) (((2 : ℝ))⁻¹)))))) := by
  sorry

theorem proof_gap_exercise_589_6
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → (((x ^ (2 : ℕ)) + 1) > 0))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((Real.rpow ((x ^ (2 : ℕ)) + 1) (((2 : ℝ))⁻¹)) ≠ 0))))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → (0 < (x /. (Real.rpow ((x ^ (2 : ℕ)) + 1) (((2 : ℝ))⁻¹)))))))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((x /. (Real.rpow ((x ^ (2 : ℕ)) + 1) (((2 : ℝ))⁻¹))) < 1))))
  (h5 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → (0 < (1 /. (Real.rpow ((x ^ (2 : ℕ)) + 1) (((2 : ℝ))⁻¹)))))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((1 /. (Real.rpow ((x ^ (2 : ℕ)) + 1) (((2 : ℝ))⁻¹))) < 1))) := by
  sorry

theorem proof_gap_exercise_589_7
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → (((x ^ (2 : ℕ)) + 1) > 0))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((Real.rpow ((x ^ (2 : ℕ)) + 1) (((2 : ℝ))⁻¹)) ≠ 0))))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → (0 < (x /. (Real.rpow ((x ^ (2 : ℕ)) + 1) (((2 : ℝ))⁻¹)))))))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((x /. (Real.rpow ((x ^ (2 : ℕ)) + 1) (((2 : ℝ))⁻¹))) < 1))))
  (h5 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → (0 < (1 /. (Real.rpow ((x ^ (2 : ℕ)) + 1) (((2 : ℝ))⁻¹)))))))
  (h6 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((1 /. (Real.rpow ((x ^ (2 : ℕ)) + 1) (((2 : ℝ))⁻¹))) < 1))))
  : (∃ L : ℝ, Tendsto (fun x : ℝ => (x * (Real.arcsin (1 /. (Real.rpow ((x ^ (2 : ℕ)) + 1) (((2 : ℝ))⁻¹)))))) atTop (𝓝 L) ∧ (Tendsto (fun x : ℝ => (x * ((Real.pi /. 2) - (Real.arcsin (x /. (Real.rpow ((x ^ (2 : ℕ)) + 1) (((2 : ℝ))⁻¹))))))) atTop (𝓝 (atTop.limUnder (fun x : ℝ => (x * (Real.arcsin (1 /. (Real.rpow ((x ^ (2 : ℕ)) + 1) (((2 : ℝ))⁻¹)))))))))) := by
  sorry

theorem proof_gap_exercise_589_8
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → (((x ^ (2 : ℕ)) + 1) > 0))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((Real.rpow ((x ^ (2 : ℕ)) + 1) (((2 : ℝ))⁻¹)) ≠ 0))))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → (0 < (x /. (Real.rpow ((x ^ (2 : ℕ)) + 1) (((2 : ℝ))⁻¹)))))))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((x /. (Real.rpow ((x ^ (2 : ℕ)) + 1) (((2 : ℝ))⁻¹))) < 1))))
  (h5 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → (0 < (1 /. (Real.rpow ((x ^ (2 : ℕ)) + 1) (((2 : ℝ))⁻¹)))))))
  (h6 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((1 /. (Real.rpow ((x ^ (2 : ℕ)) + 1) (((2 : ℝ))⁻¹))) < 1))))
  (h7 : Tendsto (fun x : ℝ => (x * ((Real.pi /. 2) - (Real.arcsin (x /. (Real.rpow ((x ^ (2 : ℕ)) + 1) (((2 : ℝ))⁻¹))))))) atTop (𝓝 (atTop.limUnder (fun x : ℝ => (x * (Real.arcsin (1 /. (Real.rpow ((x ^ (2 : ℕ)) + 1) (((2 : ℝ))⁻¹)))))))))
  (h8 : ∃ L : ℝ, Tendsto (fun x : ℝ => (x * (Real.arcsin (1 /. (Real.rpow ((x ^ (2 : ℕ)) + 1) (((2 : ℝ))⁻¹)))))) atTop (𝓝 L))
  : (∃ L : ℝ, Tendsto (fun x : ℝ => (((Real.arcsin (1 /. (Real.rpow ((x ^ (2 : ℕ)) + 1) (((2 : ℝ))⁻¹)))) /. (1 /. (Real.rpow ((x ^ (2 : ℕ)) + 1) (((2 : ℝ))⁻¹)))) * (x /. (Real.rpow ((x ^ (2 : ℕ)) + 1) (((2 : ℝ))⁻¹))))) atTop (𝓝 L) ∧ (Tendsto (fun x : ℝ => (x * (Real.arcsin (1 /. (Real.rpow ((x ^ (2 : ℕ)) + 1) (((2 : ℝ))⁻¹)))))) atTop (𝓝 (atTop.limUnder (fun x : ℝ => (((Real.arcsin (1 /. (Real.rpow ((x ^ (2 : ℕ)) + 1) (((2 : ℝ))⁻¹)))) /. (1 /. (Real.rpow ((x ^ (2 : ℕ)) + 1) (((2 : ℝ))⁻¹)))) * (x /. (Real.rpow ((x ^ (2 : ℕ)) + 1) (((2 : ℝ))⁻¹))))))))) := by
  sorry

theorem proof_gap_exercise_589_9
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → (((x ^ (2 : ℕ)) + 1) > 0))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((Real.rpow ((x ^ (2 : ℕ)) + 1) (((2 : ℝ))⁻¹)) ≠ 0))))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → (0 < (x /. (Real.rpow ((x ^ (2 : ℕ)) + 1) (((2 : ℝ))⁻¹)))))))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((x /. (Real.rpow ((x ^ (2 : ℕ)) + 1) (((2 : ℝ))⁻¹))) < 1))))
  (h5 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → (0 < (1 /. (Real.rpow ((x ^ (2 : ℕ)) + 1) (((2 : ℝ))⁻¹)))))))
  (h6 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((1 /. (Real.rpow ((x ^ (2 : ℕ)) + 1) (((2 : ℝ))⁻¹))) < 1))))
  (h7 : Tendsto (fun x : ℝ => (x * ((Real.pi /. 2) - (Real.arcsin (x /. (Real.rpow ((x ^ (2 : ℕ)) + 1) (((2 : ℝ))⁻¹))))))) atTop (𝓝 (atTop.limUnder (fun x : ℝ => (x * (Real.arcsin (1 /. (Real.rpow ((x ^ (2 : ℕ)) + 1) (((2 : ℝ))⁻¹)))))))))
  (h8 : Tendsto (fun x : ℝ => (x * (Real.arcsin (1 /. (Real.rpow ((x ^ (2 : ℕ)) + 1) (((2 : ℝ))⁻¹)))))) atTop (𝓝 (atTop.limUnder (fun x : ℝ => (((Real.arcsin (1 /. (Real.rpow ((x ^ (2 : ℕ)) + 1) (((2 : ℝ))⁻¹)))) /. (1 /. (Real.rpow ((x ^ (2 : ℕ)) + 1) (((2 : ℝ))⁻¹)))) * (x /. (Real.rpow ((x ^ (2 : ℕ)) + 1) (((2 : ℝ))⁻¹))))))))
  (h9 : ∃ L : ℝ, Tendsto (fun x : ℝ => (x * (Real.arcsin (1 /. (Real.rpow ((x ^ (2 : ℕ)) + 1) (((2 : ℝ))⁻¹)))))) atTop (𝓝 L))
  (h10 : ∃ L : ℝ, Tendsto (fun x : ℝ => (((Real.arcsin (1 /. (Real.rpow ((x ^ (2 : ℕ)) + 1) (((2 : ℝ))⁻¹)))) /. (1 /. (Real.rpow ((x ^ (2 : ℕ)) + 1) (((2 : ℝ))⁻¹)))) * (x /. (Real.rpow ((x ^ (2 : ℕ)) + 1) (((2 : ℝ))⁻¹))))) atTop (𝓝 L))
  : Tendsto (fun x : ℝ => ((Real.arcsin x) /. x)) (𝓝[≠] 0) (𝓝 1) := by
  sorry

theorem proof_gap_exercise_589_10
  (h1 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → (((x ^ (2 : ℕ)) + 1) > 0))))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((Real.rpow ((x ^ (2 : ℕ)) + 1) (((2 : ℝ))⁻¹)) ≠ 0))))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → (0 < (x /. (Real.rpow ((x ^ (2 : ℕ)) + 1) (((2 : ℝ))⁻¹)))))))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((x /. (Real.rpow ((x ^ (2 : ℕ)) + 1) (((2 : ℝ))⁻¹))) < 1))))
  (h5 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → (0 < (1 /. (Real.rpow ((x ^ (2 : ℕ)) + 1) (((2 : ℝ))⁻¹)))))))
  (h6 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x > 0)) → ((1 /. (Real.rpow ((x ^ (2 : ℕ)) + 1) (((2 : ℝ))⁻¹))) < 1))))
  (h7 : Tendsto (fun x : ℝ => (x * ((Real.pi /. 2) - (Real.arcsin (x /. (Real.rpow ((x ^ (2 : ℕ)) + 1) (((2 : ℝ))⁻¹))))))) atTop (𝓝 (atTop.limUnder (fun x : ℝ => (x * (Real.arcsin (1 /. (Real.rpow ((x ^ (2 : ℕ)) + 1) (((2 : ℝ))⁻¹)))))))))
  (h8 : Tendsto (fun x : ℝ => (x * (Real.arcsin (1 /. (Real.rpow ((x ^ (2 : ℕ)) + 1) (((2 : ℝ))⁻¹)))))) atTop (𝓝 (atTop.limUnder (fun x : ℝ => (((Real.arcsin (1 /. (Real.rpow ((x ^ (2 : ℕ)) + 1) (((2 : ℝ))⁻¹)))) /. (1 /. (Real.rpow ((x ^ (2 : ℕ)) + 1) (((2 : ℝ))⁻¹)))) * (x /. (Real.rpow ((x ^ (2 : ℕ)) + 1) (((2 : ℝ))⁻¹))))))))
  (h9 : Tendsto (fun x : ℝ => ((Real.arcsin x) /. x)) (𝓝[≠] 0) (𝓝 1))
  (h10 : ∃ L : ℝ, Tendsto (fun x : ℝ => (x * (Real.arcsin (1 /. (Real.rpow ((x ^ (2 : ℕ)) + 1) (((2 : ℝ))⁻¹)))))) atTop (𝓝 L))
  (h11 : ∃ L : ℝ, Tendsto (fun x : ℝ => (((Real.arcsin (1 /. (Real.rpow ((x ^ (2 : ℕ)) + 1) (((2 : ℝ))⁻¹)))) /. (1 /. (Real.rpow ((x ^ (2 : ℕ)) + 1) (((2 : ℝ))⁻¹)))) * (x /. (Real.rpow ((x ^ (2 : ℕ)) + 1) (((2 : ℝ))⁻¹))))) atTop (𝓝 L))
  : Tendsto (fun x : ℝ => (x * ((Real.pi /. 2) - (Real.arcsin (x /. (Real.rpow ((x ^ (2 : ℕ)) + 1) (((2 : ℝ))⁻¹))))))) atTop (𝓝 1) := by
  sorry
