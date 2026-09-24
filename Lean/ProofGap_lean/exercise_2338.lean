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

-- exercise: exercise_2338

theorem proof_gap_exercise_2338_1
  : (forall (b : ℝ), (((b ∈ (Set.univ : Set ℝ)) ∧ (b > 2)) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (2 ≤ x)) ∧ (x ≤ b)) → (((((x ^ (2 : ℕ)) + x) - 2) ≠ 0) ∧ (((x - 1) /. (x + 2)) > 0)))))) := by
  sorry

theorem proof_gap_exercise_2338_2
  (h1 : (forall (b : ℝ), (((b ∈ (Set.univ : Set ℝ)) ∧ (b > 2)) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (2 ≤ x)) ∧ (x ≤ b)) → (((((x ^ (2 : ℕ)) + x) - 2) ≠ 0) ∧ (((x - 1) /. (x + 2)) > 0)))))))
  : (forall (b : ℝ), (((b ∈ (Set.univ : Set ℝ)) ∧ (b > 2)) → ((∫ x in (2 : ℝ)..b, (((1 : ℝ) /. (((x ^ (2 : ℕ)) + x) - (2 : ℝ))) * (1 : ℝ))) = (((1 /. 3) * (Real.log ((b - 1) /. (b + 2)))) - ((1 /. 3) * (Real.log ((2 - 1) /. (2 + 2)))))))) := by
  sorry

theorem proof_gap_exercise_2338_3
  (h1 : (forall (b : ℝ), (((b ∈ (Set.univ : Set ℝ)) ∧ (b > 2)) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (2 ≤ x)) ∧ (x ≤ b)) → (((((x ^ (2 : ℕ)) + x) - 2) ≠ 0) ∧ (((x - 1) /. (x + 2)) > 0)))))))
  (h2 : (forall (b : ℝ), (((b ∈ (Set.univ : Set ℝ)) ∧ (b > 2)) → ((∫ x in (2 : ℝ)..b, (((1 : ℝ) /. (((x ^ (2 : ℕ)) + x) - (2 : ℝ))) * (1 : ℝ))) = (((1 /. 3) * (Real.log ((b - 1) /. (b + 2)))) - ((1 /. 3) * (Real.log ((2 - 1) /. (2 + 2)))))))))
  (h3 : b > 2)
  : (∃ L : ℝ, Tendsto (fun b : ℝ => (((1 /. 3) * (Real.log ((b - 1) /. (b + 2)))) - ((1 /. 3) * (Real.log ((2 - 1) /. (2 + 2)))))) atTop (𝓝 L) ∧ (Tendsto (fun b : ℝ => (∫ x in (2 : ℝ)..b, (((1 : ℝ) /. (((x ^ (2 : ℕ)) + x) - (2 : ℝ))) * (1 : ℝ)))) atTop (𝓝 (atTop.limUnder (fun b : ℝ => (((1 /. 3) * (Real.log ((b - 1) /. (b + 2)))) - ((1 /. 3) * (Real.log ((2 - 1) /. (2 + 2)))))))))) := by
  sorry

theorem proof_gap_exercise_2338_4
  (h1 : (forall (b : ℝ), (((b ∈ (Set.univ : Set ℝ)) ∧ (b > 2)) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (2 ≤ x)) ∧ (x ≤ b)) → (((((x ^ (2 : ℕ)) + x) - 2) ≠ 0) ∧ (((x - 1) /. (x + 2)) > 0)))))))
  (h2 : (forall (b : ℝ), (((b ∈ (Set.univ : Set ℝ)) ∧ (b > 2)) → ((∫ x in (2 : ℝ)..b, (((1 : ℝ) /. (((x ^ (2 : ℕ)) + x) - (2 : ℝ))) * (1 : ℝ))) = (((1 /. 3) * (Real.log ((b - 1) /. (b + 2)))) - ((1 /. 3) * (Real.log ((2 - 1) /. (2 + 2)))))))))
  (h3 : Tendsto (fun b : ℝ => (∫ x in (2 : ℝ)..b, (((1 : ℝ) /. (((x ^ (2 : ℕ)) + x) - (2 : ℝ))) * (1 : ℝ)))) atTop (𝓝 (atTop.limUnder (fun b : ℝ => (((1 /. 3) * (Real.log ((b - 1) /. (b + 2)))) - ((1 /. 3) * (Real.log ((2 - 1) /. (2 + 2)))))))))
  (h4 : b > 2)
  (h5 : ∃ L : ℝ, Tendsto (fun b : ℝ => (((1 /. 3) * (Real.log ((b - 1) /. (b + 2)))) - ((1 /. 3) * (Real.log ((2 - 1) /. (2 + 2)))))) atTop (𝓝 L))
  : (∃ L : ℝ, Tendsto (fun b : ℝ => ((Real.log ((b - 1) /. (b + 2))) + (2 * (Real.log (2 : ℝ))))) atTop (𝓝 L) ∧ (Tendsto (fun b : ℝ => (((1 /. 3) * (Real.log ((b - 1) /. (b + 2)))) - ((1 /. 3) * (Real.log ((2 - 1) /. (2 + 2)))))) atTop (𝓝 ((1 /. 3) * atTop.limUnder (fun b : ℝ => ((Real.log ((b - 1) /. (b + 2))) + (2 * (Real.log (2 : ℝ))))))))) := by
  sorry

theorem proof_gap_exercise_2338_5
  (h1 : (forall (b : ℝ), (((b ∈ (Set.univ : Set ℝ)) ∧ (b > 2)) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (2 ≤ x)) ∧ (x ≤ b)) → (((((x ^ (2 : ℕ)) + x) - 2) ≠ 0) ∧ (((x - 1) /. (x + 2)) > 0)))))))
  (h2 : (forall (b : ℝ), (((b ∈ (Set.univ : Set ℝ)) ∧ (b > 2)) → ((∫ x in (2 : ℝ)..b, (((1 : ℝ) /. (((x ^ (2 : ℕ)) + x) - (2 : ℝ))) * (1 : ℝ))) = (((1 /. 3) * (Real.log ((b - 1) /. (b + 2)))) - ((1 /. 3) * (Real.log ((2 - 1) /. (2 + 2)))))))))
  (h3 : Tendsto (fun b : ℝ => (∫ x in (2 : ℝ)..b, (((1 : ℝ) /. (((x ^ (2 : ℕ)) + x) - (2 : ℝ))) * (1 : ℝ)))) atTop (𝓝 (atTop.limUnder (fun b : ℝ => (((1 /. 3) * (Real.log ((b - 1) /. (b + 2)))) - ((1 /. 3) * (Real.log ((2 - 1) /. (2 + 2)))))))))
  (h4 : Tendsto (fun b : ℝ => (((1 /. 3) * (Real.log ((b - 1) /. (b + 2)))) - ((1 /. 3) * (Real.log ((2 - 1) /. (2 + 2)))))) atTop (𝓝 ((1 /. 3) * atTop.limUnder (fun b : ℝ => ((Real.log ((b - 1) /. (b + 2))) + (2 * (Real.log (2 : ℝ))))))))
  (h5 : ∃ L : ℝ, Tendsto (fun b : ℝ => (((1 /. 3) * (Real.log ((b - 1) /. (b + 2)))) - ((1 /. 3) * (Real.log ((2 - 1) /. (2 + 2)))))) atTop (𝓝 L))
  (h6 : ∃ L : ℝ, Tendsto (fun b : ℝ => ((Real.log ((b - 1) /. (b + 2))) + (2 * (Real.log (2 : ℝ))))) atTop (𝓝 L))
  : ((1 /. 3) * atTop.limUnder (fun b : ℝ => ((Real.log ((b - 1) /. (b + 2))) + (2 * (Real.log (2 : ℝ)))))) = ((2 /. 3) * (Real.log (2 : ℝ))) := by
  sorry

theorem proof_gap_exercise_2338_6
  (h1 : (forall (b : ℝ), (((b ∈ (Set.univ : Set ℝ)) ∧ (b > 2)) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (2 ≤ x)) ∧ (x ≤ b)) → (((((x ^ (2 : ℕ)) + x) - 2) ≠ 0) ∧ (((x - 1) /. (x + 2)) > 0)))))))
  (h2 : (forall (b : ℝ), (((b ∈ (Set.univ : Set ℝ)) ∧ (b > 2)) → ((∫ x in (2 : ℝ)..b, (((1 : ℝ) /. (((x ^ (2 : ℕ)) + x) - (2 : ℝ))) * (1 : ℝ))) = (((1 /. 3) * (Real.log ((b - 1) /. (b + 2)))) - ((1 /. 3) * (Real.log ((2 - 1) /. (2 + 2)))))))))
  (h3 : Tendsto (fun b : ℝ => (∫ x in (2 : ℝ)..b, (((1 : ℝ) /. (((x ^ (2 : ℕ)) + x) - (2 : ℝ))) * (1 : ℝ)))) atTop (𝓝 (atTop.limUnder (fun b : ℝ => (((1 /. 3) * (Real.log ((b - 1) /. (b + 2)))) - ((1 /. 3) * (Real.log ((2 - 1) /. (2 + 2)))))))))
  (h4 : Tendsto (fun b : ℝ => (((1 /. 3) * (Real.log ((b - 1) /. (b + 2)))) - ((1 /. 3) * (Real.log ((2 - 1) /. (2 + 2)))))) atTop (𝓝 ((1 /. 3) * atTop.limUnder (fun b : ℝ => ((Real.log ((b - 1) /. (b + 2))) + (2 * (Real.log (2 : ℝ))))))))
  (h5 : ((1 /. 3) * atTop.limUnder (fun b : ℝ => ((Real.log ((b - 1) /. (b + 2))) + (2 * (Real.log (2 : ℝ)))))) = ((2 /. 3) * (Real.log (2 : ℝ))))
  (h6 : ∃ L : ℝ, Tendsto (fun b : ℝ => (((1 /. 3) * (Real.log ((b - 1) /. (b + 2)))) - ((1 /. 3) * (Real.log ((2 - 1) /. (2 + 2)))))) atTop (𝓝 L))
  (h7 : ∃ L : ℝ, Tendsto (fun b : ℝ => ((Real.log ((b - 1) /. (b + 2))) + (2 * (Real.log (2 : ℝ))))) atTop (𝓝 L))
  : Tendsto (fun b : ℝ => (∫ x in (2 : ℝ)..b, (((1 : ℝ) /. (((x ^ (2 : ℕ)) + x) - (2 : ℝ))) * (1 : ℝ)))) atTop (𝓝 ((2 /. 3) * (Real.log (2 : ℝ)))) := by
  sorry

theorem proof_gap_exercise_2338_7
  (h1 : (forall (b : ℝ), (((b ∈ (Set.univ : Set ℝ)) ∧ (b > 2)) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (2 ≤ x)) ∧ (x ≤ b)) → (((((x ^ (2 : ℕ)) + x) - 2) ≠ 0) ∧ (((x - 1) /. (x + 2)) > 0)))))))
  (h2 : (forall (b : ℝ), (((b ∈ (Set.univ : Set ℝ)) ∧ (b > 2)) → ((∫ x in (2 : ℝ)..b, (((1 : ℝ) /. (((x ^ (2 : ℕ)) + x) - (2 : ℝ))) * (1 : ℝ))) = (((1 /. 3) * (Real.log ((b - 1) /. (b + 2)))) - ((1 /. 3) * (Real.log ((2 - 1) /. (2 + 2)))))))))
  (h3 : Tendsto (fun b : ℝ => (∫ x in (2 : ℝ)..b, (((1 : ℝ) /. (((x ^ (2 : ℕ)) + x) - (2 : ℝ))) * (1 : ℝ)))) atTop (𝓝 (atTop.limUnder (fun b : ℝ => (((1 /. 3) * (Real.log ((b - 1) /. (b + 2)))) - ((1 /. 3) * (Real.log ((2 - 1) /. (2 + 2)))))))))
  (h4 : Tendsto (fun b : ℝ => (((1 /. 3) * (Real.log ((b - 1) /. (b + 2)))) - ((1 /. 3) * (Real.log ((2 - 1) /. (2 + 2)))))) atTop (𝓝 ((1 /. 3) * atTop.limUnder (fun b : ℝ => ((Real.log ((b - 1) /. (b + 2))) + (2 * (Real.log (2 : ℝ))))))))
  (h5 : ((1 /. 3) * atTop.limUnder (fun b : ℝ => ((Real.log ((b - 1) /. (b + 2))) + (2 * (Real.log (2 : ℝ)))))) = ((2 /. 3) * (Real.log (2 : ℝ))))
  (h6 : Tendsto (fun b : ℝ => (∫ x in (2 : ℝ)..b, (((1 : ℝ) /. (((x ^ (2 : ℕ)) + x) - (2 : ℝ))) * (1 : ℝ)))) atTop (𝓝 ((2 /. 3) * (Real.log (2 : ℝ)))))
  (h7 : b > 2)
  (h8 : ∃ L : ℝ, Tendsto (fun b : ℝ => (((1 /. 3) * (Real.log ((b - 1) /. (b + 2)))) - ((1 /. 3) * (Real.log ((2 - 1) /. (2 + 2)))))) atTop (𝓝 L))
  (h9 : ∃ L : ℝ, Tendsto (fun b : ℝ => ((Real.log ((b - 1) /. (b + 2))) + (2 * (Real.log (2 : ℝ))))) atTop (𝓝 L))
  : (∫ x in Set.Ioi (2 : ℝ), (((1 : ℝ) /. (((x ^ (2 : ℕ)) + x) - (2 : ℝ))) * (1 : ℝ))) = ((2 /. 3) * (Real.log (2 : ℝ))) := by
  sorry
