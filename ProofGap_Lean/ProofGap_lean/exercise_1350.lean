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

-- exercise: exercise_1350

theorem proof_gap_exercise_1350_1
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), (((((y ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x < 1)) ∧ (y = (1 /. x))) → (y > 1))))) := by
  sorry

theorem proof_gap_exercise_1350_2
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), (((((y ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x < 1)) ∧ (y = (1 /. x))) → (y > 1))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), (((((y ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x < 1)) ∧ (y = (1 /. x))) → (∃ L : ℝ, Tendsto (fun y_1 : ℝ => ((Real.log (Real.log y_1)) /. y_1)) atTop (𝓝 L) ∧ (Tendsto (fun x_1 : ℝ => (x_1 * (Real.log (Real.log (1 /. x_1))))) (𝓝[>] 0) (𝓝 (atTop.limUnder (fun y_1 : ℝ => ((Real.log (Real.log y_1)) /. y_1)))))))))) := by
  sorry

theorem proof_gap_exercise_1350_3
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), (((((y ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x < 1)) ∧ (y = (1 /. x))) → (y > 1))))))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), (∃ L : ℝ, Tendsto (fun y_1 : ℝ => ((Real.log (Real.log y_1)) /. y_1)) atTop (𝓝 L) ∧ (((((y ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x < 1)) ∧ (y = (1 /. x))) → (Tendsto (fun x_1 : ℝ => (x_1 * (Real.log (Real.log (1 /. x_1))))) (𝓝[>] 0) (𝓝 (atTop.limUnder (fun y_1 : ℝ => ((Real.log (Real.log y_1)) /. y_1)))))))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), (((((y ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x < 1)) ∧ (y = (1 /. x))) → (∃ L : ℝ, Tendsto (fun y_1 : ℝ => (1 /. (y_1 * (Real.log y_1)))) atTop (𝓝 L) ∧ (Tendsto (fun y_1 : ℝ => ((Real.log (Real.log y_1)) /. y_1)) atTop (𝓝 (atTop.limUnder (fun y_1 : ℝ => (1 /. (y_1 * (Real.log y_1)))))))))))) := by
  sorry

theorem proof_gap_exercise_1350_4
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), (((((y ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x < 1)) ∧ (y = (1 /. x))) → (y > 1))))))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), (∃ L : ℝ, Tendsto (fun y_1 : ℝ => ((Real.log (Real.log y_1)) /. y_1)) atTop (𝓝 L) ∧ (((((y ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x < 1)) ∧ (y = (1 /. x))) → (Tendsto (fun x_1 : ℝ => (x_1 * (Real.log (Real.log (1 /. x_1))))) (𝓝[>] 0) (𝓝 (atTop.limUnder (fun y_1 : ℝ => ((Real.log (Real.log y_1)) /. y_1)))))))))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), (∃ L : ℝ, Tendsto (fun y_1 : ℝ => (1 /. (y_1 * (Real.log y_1)))) atTop (𝓝 L) ∧ (((((y ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x < 1)) ∧ (y = (1 /. x))) → (Tendsto (fun y_1 : ℝ => ((Real.log (Real.log y_1)) /. y_1)) atTop (𝓝 (atTop.limUnder (fun y_1 : ℝ => (1 /. (y_1 * (Real.log y_1)))))))))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), (((((y ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x < 1)) ∧ (y = (1 /. x))) → (Tendsto (fun y_1 : ℝ => (1 /. (y_1 * (Real.log y_1)))) atTop (𝓝 0)))))) := by
  sorry

theorem proof_gap_exercise_1350_5
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), (((((y ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x < 1)) ∧ (y = (1 /. x))) → (y > 1))))))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), (∃ L : ℝ, Tendsto (fun y_1 : ℝ => ((Real.log (Real.log y_1)) /. y_1)) atTop (𝓝 L) ∧ (((((y ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x < 1)) ∧ (y = (1 /. x))) → (Tendsto (fun x_1 : ℝ => (x_1 * (Real.log (Real.log (1 /. x_1))))) (𝓝[>] 0) (𝓝 (atTop.limUnder (fun y_1 : ℝ => ((Real.log (Real.log y_1)) /. y_1)))))))))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), (∃ L : ℝ, Tendsto (fun y_1 : ℝ => (1 /. (y_1 * (Real.log y_1)))) atTop (𝓝 L) ∧ (((((y ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x < 1)) ∧ (y = (1 /. x))) → (Tendsto (fun y_1 : ℝ => ((Real.log (Real.log y_1)) /. y_1)) atTop (𝓝 (atTop.limUnder (fun y_1 : ℝ => (1 /. (y_1 * (Real.log y_1)))))))))))))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), (((((y ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x < 1)) ∧ (y = (1 /. x))) → (Tendsto (fun y_1 : ℝ => (1 /. (y_1 * (Real.log y_1)))) atTop (𝓝 0)))))))
  : Tendsto (fun x : ℝ => (Real.rpow (Real.log (1 /. x)) x)) (𝓝[>] 0) (𝓝 (Real.exp (0 : ℝ))) := by
  sorry

theorem proof_gap_exercise_1350_6
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), (((((y ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x < 1)) ∧ (y = (1 /. x))) → (y > 1))))))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), (∃ L : ℝ, Tendsto (fun y_1 : ℝ => ((Real.log (Real.log y_1)) /. y_1)) atTop (𝓝 L) ∧ (((((y ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x < 1)) ∧ (y = (1 /. x))) → (Tendsto (fun x_1 : ℝ => (x_1 * (Real.log (Real.log (1 /. x_1))))) (𝓝[>] 0) (𝓝 (atTop.limUnder (fun y_1 : ℝ => ((Real.log (Real.log y_1)) /. y_1)))))))))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), (∃ L : ℝ, Tendsto (fun y_1 : ℝ => (1 /. (y_1 * (Real.log y_1)))) atTop (𝓝 L) ∧ (((((y ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x < 1)) ∧ (y = (1 /. x))) → (Tendsto (fun y_1 : ℝ => ((Real.log (Real.log y_1)) /. y_1)) atTop (𝓝 (atTop.limUnder (fun y_1 : ℝ => (1 /. (y_1 * (Real.log y_1)))))))))))))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), (((((y ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x < 1)) ∧ (y = (1 /. x))) → (Tendsto (fun y_1 : ℝ => (1 /. (y_1 * (Real.log y_1)))) atTop (𝓝 0)))))))
  (h5 : Tendsto (fun x : ℝ => (Real.rpow (Real.log (1 /. x)) x)) (𝓝[>] 0) (𝓝 (Real.exp (0 : ℝ))))
  : (Real.exp (0 : ℝ)) = 1 := by
  sorry

theorem proof_gap_exercise_1350_7
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), (((((y ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x < 1)) ∧ (y = (1 /. x))) → (y > 1))))))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), (∃ L : ℝ, Tendsto (fun y_1 : ℝ => ((Real.log (Real.log y_1)) /. y_1)) atTop (𝓝 L) ∧ (((((y ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x < 1)) ∧ (y = (1 /. x))) → (Tendsto (fun x_1 : ℝ => (x_1 * (Real.log (Real.log (1 /. x_1))))) (𝓝[>] 0) (𝓝 (atTop.limUnder (fun y_1 : ℝ => ((Real.log (Real.log y_1)) /. y_1)))))))))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), (∃ L : ℝ, Tendsto (fun y_1 : ℝ => (1 /. (y_1 * (Real.log y_1)))) atTop (𝓝 L) ∧ (((((y ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x < 1)) ∧ (y = (1 /. x))) → (Tendsto (fun y_1 : ℝ => ((Real.log (Real.log y_1)) /. y_1)) atTop (𝓝 (atTop.limUnder (fun y_1 : ℝ => (1 /. (y_1 * (Real.log y_1)))))))))))))
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), (((((y ∈ (Set.univ : Set ℝ)) ∧ (0 < x)) ∧ (x < 1)) ∧ (y = (1 /. x))) → (Tendsto (fun y_1 : ℝ => (1 /. (y_1 * (Real.log y_1)))) atTop (𝓝 0)))))))
  (h5 : Tendsto (fun x : ℝ => (Real.rpow (Real.log (1 /. x)) x)) (𝓝[>] 0) (𝓝 (Real.exp (0 : ℝ))))
  (h6 : (Real.exp (0 : ℝ)) = 1)
  : Tendsto (fun x : ℝ => (Real.rpow (Real.log (1 /. x)) x)) (𝓝[>] 0) (𝓝 1) := by
  sorry
