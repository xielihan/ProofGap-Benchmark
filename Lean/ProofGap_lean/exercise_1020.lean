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

-- exercise: exercise_1020

theorem proof_gap_exercise_1020_1
  (h1 : f = (fun (x : ℝ) => (Real.rpow x (((3 : ℝ))⁻¹))))
  (h2 : a = 0)
  : (forall (b : ℝ), (((b ∈ (Set.univ : Set ℝ)) ∧ (b > 0)) → (DifferentiableOn ℝ f (Set.Ioo 0 b)))) := by
  sorry

theorem proof_gap_exercise_1020_2
  (h1 : f = (fun (x : ℝ) => (Real.rpow x (((3 : ℝ))⁻¹))))
  (h2 : a = 0)
  (h3 : (forall (b : ℝ), (((b ∈ (Set.univ : Set ℝ)) ∧ (b > 0)) → (DifferentiableOn ℝ f (Set.Ioo 0 b)))))
  : (forall (b : ℝ), (((b ∈ (Set.univ : Set ℝ)) ∧ (b > 0)) → (forall (x : ℝ) (b_1 : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (b_1 ∈ (Set.univ : Set ℝ))) ∧ (x ∈ (Set.Ioo 0 b_1))) → ((iteratedDeriv 1 (fun t => f t) x) = (1 /. (3 * (Real.rpow (x ^ (2 : ℕ)) (((3 : ℝ))⁻¹))))))))) := by
  sorry

theorem proof_gap_exercise_1020_3
  (h1 : f = (fun (x : ℝ) => (Real.rpow x (((3 : ℝ))⁻¹))))
  (h2 : a = 0)
  (h3 : (forall (b : ℝ), (((b ∈ (Set.univ : Set ℝ)) ∧ (b > 0)) → (DifferentiableOn ℝ f (Set.Ioo 0 b)))))
  (h4 : (forall (b : ℝ), (((b ∈ (Set.univ : Set ℝ)) ∧ (b > 0)) → (forall (x : ℝ) (b_1 : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (b_1 ∈ (Set.univ : Set ℝ))) ∧ (x ∈ (Set.Ioo 0 b_1))) → ((iteratedDeriv 1 (fun t => f t) x) = (1 /. (3 * (Real.rpow (x ^ (2 : ℕ)) (((3 : ℝ))⁻¹))))))))))
  : (forall (b : ℝ), (((b ∈ (Set.univ : Set ℝ)) ∧ (b > 0)) → (Tendsto (fun x : ℝ => (((iteratedDeriv 1 (fun t => f t) x) : ℝ) : EReal)) (𝓝[>] 0) (𝓝 ⊤)))) := by
  sorry

theorem proof_gap_exercise_1020_4
  (h1 : f = (fun (x : ℝ) => (Real.rpow x (((3 : ℝ))⁻¹))))
  (h2 : a = 0)
  (h3 : (forall (b : ℝ), (((b ∈ (Set.univ : Set ℝ)) ∧ (b > 0)) → (DifferentiableOn ℝ f (Set.Ioo 0 b)))))
  (h4 : (forall (b : ℝ), (((b ∈ (Set.univ : Set ℝ)) ∧ (b > 0)) → (forall (x : ℝ) (b_1 : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (b_1 ∈ (Set.univ : Set ℝ))) ∧ (x ∈ (Set.Ioo 0 b_1))) → ((iteratedDeriv 1 (fun t => f t) x) = (1 /. (3 * (Real.rpow (x ^ (2 : ℕ)) (((3 : ℝ))⁻¹))))))))))
  (h5 : (forall (b : ℝ), (((b ∈ (Set.univ : Set ℝ)) ∧ (b > 0)) → (Tendsto (fun x : ℝ => (((iteratedDeriv 1 (fun t => f t) x) : ℝ) : EReal)) (𝓝[>] 0) (𝓝 ⊤)))))
  : (forall (b : ℝ), (((b ∈ (Set.univ : Set ℝ)) ∧ (b > 0)) → (∃ L : ℝ, Tendsto (fun x : ℝ => (Real.rpow x (((3 : ℝ))⁻¹))) (𝓝[>] 0) (𝓝 L) ∧ (Tendsto (fun x : ℝ => (f x)) (𝓝[>] 0) (𝓝 ((𝓝[>] 0).limUnder (fun x : ℝ => (Real.rpow x (((3 : ℝ))⁻¹))))))))) := by
  sorry

theorem proof_gap_exercise_1020_5
  (h1 : f = (fun (x : ℝ) => (Real.rpow x (((3 : ℝ))⁻¹))))
  (h2 : a = 0)
  (h3 : (forall (b : ℝ), (((b ∈ (Set.univ : Set ℝ)) ∧ (b > 0)) → (DifferentiableOn ℝ f (Set.Ioo 0 b)))))
  (h4 : (forall (b : ℝ), (((b ∈ (Set.univ : Set ℝ)) ∧ (b > 0)) → (forall (x : ℝ) (b_1 : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (b_1 ∈ (Set.univ : Set ℝ))) ∧ (x ∈ (Set.Ioo 0 b_1))) → ((iteratedDeriv 1 (fun t => f t) x) = (1 /. (3 * (Real.rpow (x ^ (2 : ℕ)) (((3 : ℝ))⁻¹))))))))))
  (h5 : (forall (b : ℝ), (((b ∈ (Set.univ : Set ℝ)) ∧ (b > 0)) → (Tendsto (fun x : ℝ => (((iteratedDeriv 1 (fun t => f t) x) : ℝ) : EReal)) (𝓝[>] 0) (𝓝 ⊤)))))
  (h6 : (forall (b : ℝ), (∃ L : ℝ, Tendsto (fun x : ℝ => (Real.rpow x (((3 : ℝ))⁻¹))) (𝓝[>] 0) (𝓝 L) ∧ (((b ∈ (Set.univ : Set ℝ)) ∧ (b > 0)) → (Tendsto (fun x : ℝ => (f x)) (𝓝[>] 0) (𝓝 ((𝓝[>] 0).limUnder (fun x : ℝ => (Real.rpow x (((3 : ℝ))⁻¹))))))))))
  : (forall (b : ℝ), (((b ∈ (Set.univ : Set ℝ)) ∧ (b > 0)) → (Tendsto (fun x : ℝ => (Real.rpow x (((3 : ℝ))⁻¹))) (𝓝[>] 0) (𝓝 0)))) := by
  sorry

theorem proof_gap_exercise_1020_6
  (h1 : f = (fun (x : ℝ) => (Real.rpow x (((3 : ℝ))⁻¹))))
  (h2 : a = 0)
  (h3 : (forall (b : ℝ), (((b ∈ (Set.univ : Set ℝ)) ∧ (b > 0)) → (DifferentiableOn ℝ f (Set.Ioo 0 b)))))
  (h4 : (forall (b : ℝ), (((b ∈ (Set.univ : Set ℝ)) ∧ (b > 0)) → (forall (x : ℝ) (b_1 : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (b_1 ∈ (Set.univ : Set ℝ))) ∧ (x ∈ (Set.Ioo 0 b_1))) → ((iteratedDeriv 1 (fun t => f t) x) = (1 /. (3 * (Real.rpow (x ^ (2 : ℕ)) (((3 : ℝ))⁻¹))))))))))
  (h5 : (forall (b : ℝ), (((b ∈ (Set.univ : Set ℝ)) ∧ (b > 0)) → (Tendsto (fun x : ℝ => (((iteratedDeriv 1 (fun t => f t) x) : ℝ) : EReal)) (𝓝[>] 0) (𝓝 ⊤)))))
  (h6 : (forall (b : ℝ), (∃ L : ℝ, Tendsto (fun x : ℝ => (Real.rpow x (((3 : ℝ))⁻¹))) (𝓝[>] 0) (𝓝 L) ∧ (((b ∈ (Set.univ : Set ℝ)) ∧ (b > 0)) → (Tendsto (fun x : ℝ => (f x)) (𝓝[>] 0) (𝓝 ((𝓝[>] 0).limUnder (fun x : ℝ => (Real.rpow x (((3 : ℝ))⁻¹))))))))))
  (h7 : (forall (b : ℝ), (((b ∈ (Set.univ : Set ℝ)) ∧ (b > 0)) → (Tendsto (fun x : ℝ => (Real.rpow x (((3 : ℝ))⁻¹))) (𝓝[>] 0) (𝓝 0)))))
  : (forall (b : ℝ), (((b ∈ (Set.univ : Set ℝ)) ∧ (b > 0)) → (Tendsto (fun x : ℝ => (f x)) (𝓝[>] 0) (𝓝 0)))) := by
  sorry

theorem proof_gap_exercise_1020_7
  (h1 : f = (fun (x : ℝ) => (Real.rpow x (((3 : ℝ))⁻¹))))
  (h2 : a = 0)
  (h3 : (forall (b : ℝ), (((b ∈ (Set.univ : Set ℝ)) ∧ (b > 0)) → (DifferentiableOn ℝ f (Set.Ioo 0 b)))))
  (h4 : (forall (b : ℝ), (((b ∈ (Set.univ : Set ℝ)) ∧ (b > 0)) → (forall (x : ℝ) (b_1 : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (b_1 ∈ (Set.univ : Set ℝ))) ∧ (x ∈ (Set.Ioo 0 b_1))) → ((iteratedDeriv 1 (fun t => f t) x) = (1 /. (3 * (Real.rpow (x ^ (2 : ℕ)) (((3 : ℝ))⁻¹))))))))))
  (h5 : (forall (b : ℝ), (((b ∈ (Set.univ : Set ℝ)) ∧ (b > 0)) → (Tendsto (fun x : ℝ => (((iteratedDeriv 1 (fun t => f t) x) : ℝ) : EReal)) (𝓝[>] 0) (𝓝 ⊤)))))
  (h6 : (forall (b : ℝ), (∃ L : ℝ, Tendsto (fun x : ℝ => (Real.rpow x (((3 : ℝ))⁻¹))) (𝓝[>] 0) (𝓝 L) ∧ (((b ∈ (Set.univ : Set ℝ)) ∧ (b > 0)) → (Tendsto (fun x : ℝ => (f x)) (𝓝[>] 0) (𝓝 ((𝓝[>] 0).limUnder (fun x : ℝ => (Real.rpow x (((3 : ℝ))⁻¹))))))))))
  (h7 : (forall (b : ℝ), (((b ∈ (Set.univ : Set ℝ)) ∧ (b > 0)) → (Tendsto (fun x : ℝ => (Real.rpow x (((3 : ℝ))⁻¹))) (𝓝[>] 0) (𝓝 0)))))
  (h8 : (forall (b : ℝ), (((b ∈ (Set.univ : Set ℝ)) ∧ (b > 0)) → (Tendsto (fun x : ℝ => (f x)) (𝓝[>] 0) (𝓝 0)))))
  : Not (Tendsto (fun x : ℝ => (((f x) : ℝ) : EReal)) (𝓝[>] 0) (𝓝 ⊤)) := by
  sorry

theorem proof_gap_exercise_1020_8
  (h1 : f = (fun (x : ℝ) => (Real.rpow x (((3 : ℝ))⁻¹))))
  (h2 : a = 0)
  (h3 : (forall (b : ℝ), (((b ∈ (Set.univ : Set ℝ)) ∧ (b > 0)) → (DifferentiableOn ℝ f (Set.Ioo 0 b)))))
  (h4 : (forall (b : ℝ), (((b ∈ (Set.univ : Set ℝ)) ∧ (b > 0)) → (forall (x : ℝ) (b_1 : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (b_1 ∈ (Set.univ : Set ℝ))) ∧ (x ∈ (Set.Ioo 0 b_1))) → ((iteratedDeriv 1 (fun t => f t) x) = (1 /. (3 * (Real.rpow (x ^ (2 : ℕ)) (((3 : ℝ))⁻¹))))))))))
  (h5 : (forall (b : ℝ), (((b ∈ (Set.univ : Set ℝ)) ∧ (b > 0)) → (Tendsto (fun x : ℝ => (((iteratedDeriv 1 (fun t => f t) x) : ℝ) : EReal)) (𝓝[>] 0) (𝓝 ⊤)))))
  (h6 : (forall (b : ℝ), (∃ L : ℝ, Tendsto (fun x : ℝ => (Real.rpow x (((3 : ℝ))⁻¹))) (𝓝[>] 0) (𝓝 L) ∧ (((b ∈ (Set.univ : Set ℝ)) ∧ (b > 0)) → (Tendsto (fun x : ℝ => (f x)) (𝓝[>] 0) (𝓝 ((𝓝[>] 0).limUnder (fun x : ℝ => (Real.rpow x (((3 : ℝ))⁻¹))))))))))
  (h7 : (forall (b : ℝ), (((b ∈ (Set.univ : Set ℝ)) ∧ (b > 0)) → (Tendsto (fun x : ℝ => (Real.rpow x (((3 : ℝ))⁻¹))) (𝓝[>] 0) (𝓝 0)))))
  (h8 : (forall (b : ℝ), (((b ∈ (Set.univ : Set ℝ)) ∧ (b > 0)) → (Tendsto (fun x : ℝ => (f x)) (𝓝[>] 0) (𝓝 0)))))
  (h9 : Not (Tendsto (fun x : ℝ => (((f x) : ℝ) : EReal)) (𝓝[>] 0) (𝓝 ⊤)))
  : Not (forall (f : (ℝ -> ℝ)) (a : ℝ) (b : ℝ), ((((((a ∈ (Set.univ : Set ℝ)) ∧ (b ∈ (Set.univ : Set ℝ))) ∧ (a < b)) ∧ (DifferentiableOn ℝ f (Set.Ioo a b))) ∧ (Tendsto (fun x : ℝ => (((iteratedDeriv 1 (fun t => f t) x) : ℝ) : EReal)) (𝓝[>] a) (𝓝 ⊤))) → (Tendsto (fun x : ℝ => (((f x) : ℝ) : EReal)) (𝓝[>] a) (𝓝 ⊤)))) := by
  sorry
