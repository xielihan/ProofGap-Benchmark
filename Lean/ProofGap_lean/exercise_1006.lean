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

-- exercise: exercise_1006

theorem proof_gap_exercise_1006_1
  (f : (ℝ -> ℝ))
  (h1 : True)
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((f x) = |((Real.log |(x)|))|))))
  : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) ∧ (|(x)| ≠ 1)) → ((iteratedDeriv 1 (fun t => f t) x) = ((1 /. x) * (|((Real.log |(x)|))| /. (Real.log |(x)|)))))) := by
  sorry

theorem proof_gap_exercise_1006_2
  (f : (ℝ -> ℝ))
  (h1 : True)
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((f x) = |((Real.log |(x)|))|))))
  (h3 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) ∧ (|(x)| ≠ 1)) → ((iteratedDeriv 1 (fun t => f t) x) = ((1 /. x) * (|((Real.log |(x)|))| /. (Real.log |(x)|)))))))
  : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < |(x)|)) ∧ (|(x)| < 1)) → ((iteratedDeriv 1 (fun t => f t) x) = (-(1 /. x))))) := by
  sorry

theorem proof_gap_exercise_1006_3
  (f : (ℝ -> ℝ))
  (h1 : True)
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((f x) = |((Real.log |(x)|))|))))
  (h3 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) ∧ (|(x)| ≠ 1)) → ((iteratedDeriv 1 (fun t => f t) x) = ((1 /. x) * (|((Real.log |(x)|))| /. (Real.log |(x)|)))))))
  (h4 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < |(x)|)) ∧ (|(x)| < 1)) → ((iteratedDeriv 1 (fun t => f t) x) = (-(1 /. x))))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| > 1)) → ((iteratedDeriv 1 (fun t => f t) x) = (1 /. x)))) := by
  sorry

theorem proof_gap_exercise_1006_4
  (f : (ℝ -> ℝ))
  (h1 : True)
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((f x) = |((Real.log |(x)|))|))))
  (h3 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) ∧ (|(x)| ≠ 1)) → ((iteratedDeriv 1 (fun t_1 => f t_1) x) = ((1 /. x) * (|((Real.log |(x)|))| /. (Real.log |(x)|)))))))
  (h4 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < |(x)|)) ∧ (|(x)| < 1)) → ((iteratedDeriv 1 (fun t_1 => f t_1) x) = (-(1 /. x))))))
  (h5 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| > 1)) → ((iteratedDeriv 1 (fun t_1 => f t_1) x) = (1 /. x)))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x = 1)) → (Tendsto (fun t : ℝ => (((f t) - (f (1 : ℝ))) /. (t - 1))) (𝓝[<] 1) (𝓝 (-(1 : ℝ)))))) := by
  sorry

theorem proof_gap_exercise_1006_5
  (f : (ℝ -> ℝ))
  (h1 : True)
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((f x) = |((Real.log |(x)|))|))))
  (h3 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) ∧ (|(x)| ≠ 1)) → ((iteratedDeriv 1 (fun t_1 => f t_1) x) = ((1 /. x) * (|((Real.log |(x)|))| /. (Real.log |(x)|)))))))
  (h4 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < |(x)|)) ∧ (|(x)| < 1)) → ((iteratedDeriv 1 (fun t_1 => f t_1) x) = (-(1 /. x))))))
  (h5 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| > 1)) → ((iteratedDeriv 1 (fun t_1 => f t_1) x) = (1 /. x)))))
  (h6 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x = 1)) → (Tendsto (fun t : ℝ => (((f t) - (f (1 : ℝ))) /. (t - 1))) (𝓝[<] 1) (𝓝 (-(1 : ℝ)))))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x = 1)) → (Tendsto (fun t : ℝ => (((f t) - (f (1 : ℝ))) /. (t - 1))) (𝓝[>] 1) (𝓝 1)))) := by
  sorry

theorem proof_gap_exercise_1006_6
  (f : (ℝ -> ℝ))
  (h1 : True)
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((f x) = |((Real.log |(x)|))|))))
  (h3 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) ∧ (|(x)| ≠ 1)) → ((iteratedDeriv 1 (fun t_1 => f t_1) x) = ((1 /. x) * (|((Real.log |(x)|))| /. (Real.log |(x)|)))))))
  (h4 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < |(x)|)) ∧ (|(x)| < 1)) → ((iteratedDeriv 1 (fun t_1 => f t_1) x) = (-(1 /. x))))))
  (h5 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| > 1)) → ((iteratedDeriv 1 (fun t_1 => f t_1) x) = (1 /. x)))))
  (h6 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x = 1)) → (Tendsto (fun t : ℝ => (((f t) - (f (1 : ℝ))) /. (t - 1))) (𝓝[<] 1) (𝓝 (-(1 : ℝ)))))))
  (h7 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x = 1)) → (Tendsto (fun t : ℝ => (((f t) - (f (1 : ℝ))) /. (t - 1))) (𝓝[>] 1) (𝓝 1)))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x = (-(1 : ℝ)))) → (Tendsto (fun t : ℝ => (((f t) - (f (-(1 : ℝ)))) /. (t + 1))) (𝓝[<] (-(1 : ℝ))) (𝓝 (-(1 : ℝ)))))) := by
  sorry

theorem proof_gap_exercise_1006_7
  (f : (ℝ -> ℝ))
  (h1 : True)
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) → ((f x) = |((Real.log |(x)|))|))))
  (h3 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (x ≠ 0)) ∧ (|(x)| ≠ 1)) → ((iteratedDeriv 1 (fun t_1 => f t_1) x) = ((1 /. x) * (|((Real.log |(x)|))| /. (Real.log |(x)|)))))))
  (h4 : (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < |(x)|)) ∧ (|(x)| < 1)) → ((iteratedDeriv 1 (fun t_1 => f t_1) x) = (-(1 /. x))))))
  (h5 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| > 1)) → ((iteratedDeriv 1 (fun t_1 => f t_1) x) = (1 /. x)))))
  (h6 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x = 1)) → (Tendsto (fun t : ℝ => (((f t) - (f (1 : ℝ))) /. (t - 1))) (𝓝[<] 1) (𝓝 (-(1 : ℝ)))))))
  (h7 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x = 1)) → (Tendsto (fun t : ℝ => (((f t) - (f (1 : ℝ))) /. (t - 1))) (𝓝[>] 1) (𝓝 1)))))
  (h8 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x = (-(1 : ℝ)))) → (Tendsto (fun t : ℝ => (((f t) - (f (-(1 : ℝ)))) /. (t + 1))) (𝓝[<] (-(1 : ℝ))) (𝓝 (-(1 : ℝ)))))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x = (-(1 : ℝ)))) → (Tendsto (fun t : ℝ => (((f t) - (f (-(1 : ℝ)))) /. (t + 1))) (𝓝[>] (-(1 : ℝ))) (𝓝 1)))) := by
  sorry
