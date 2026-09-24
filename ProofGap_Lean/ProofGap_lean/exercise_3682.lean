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

-- exercise: exercise_3682

theorem proof_gap_exercise_3682_1
  (h1 : f = (fun (p : ℝ × ℝ) => ((p.1 - (p.2 ^ (2 : ℕ))) * ((2 * p.1) - (p.2 ^ (2 : ℕ))))))
  : (f (0, 0)) = 0 := by
  sorry

theorem proof_gap_exercise_3682_2
  (h1 : f = (fun (p : ℝ × ℝ) => ((p.1 - (p.2 ^ (2 : ℕ))) * ((2 * p.1) - (p.2 ^ (2 : ℕ))))))
  (h2 : (f (0, 0)) = 0)
  : (forall (k : ℝ), ((k ∈ (Set.univ : Set ℝ)) → (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f (x, (k * x))) = (((x ^ (2 : ℕ)) * (1 - ((k ^ (2 : ℕ)) * x))) * (2 - ((k ^ (2 : ℕ)) * x)))))))) := by
  sorry

theorem proof_gap_exercise_3682_3
  (h1 : f = (fun (p : ℝ × ℝ) => ((p.1 - (p.2 ^ (2 : ℕ))) * ((2 * p.1) - (p.2 ^ (2 : ℕ))))))
  (h2 : (f (0, 0)) = 0)
  (h3 : (forall (k : ℝ), ((k ∈ (Set.univ : Set ℝ)) → (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f (x, (k * x))) = (((x ^ (2 : ℕ)) * (1 - ((k ^ (2 : ℕ)) * x))) * (2 - ((k ^ (2 : ℕ)) * x)))))))))
  : (forall (k : ℝ), (((k ≠ 0) ∧ (k ∈ (Set.univ : Set ℝ))) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < |(x)|)) ∧ (|(x)| < (1 /. (k ^ (2 : ℕ))))) → ((f (x, (k * x))) > 0))))) := by
  sorry

theorem proof_gap_exercise_3682_4
  (h1 : f = (fun (p : ℝ × ℝ) => ((p.1 - (p.2 ^ (2 : ℕ))) * ((2 * p.1) - (p.2 ^ (2 : ℕ))))))
  (h2 : (f (0, 0)) = 0)
  (h3 : (forall (k : ℝ), ((k ∈ (Set.univ : Set ℝ)) → (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f (x, (k * x))) = (((x ^ (2 : ℕ)) * (1 - ((k ^ (2 : ℕ)) * x))) * (2 - ((k ^ (2 : ℕ)) * x)))))))))
  (h4 : (forall (k : ℝ), (((k ≠ 0) ∧ (k ∈ (Set.univ : Set ℝ))) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < |(x)|)) ∧ (|(x)| < (1 /. (k ^ (2 : ℕ))))) → ((f (x, (k * x))) > 0))))))
  : (forall (k : ℝ), ((k ∈ (Set.univ : Set ℝ)) → ((0, 0) ∈ (lpMinimumPointsOn f ({p : ℝ × ℝ | ((p.1 ∈ (Set.univ : Set ℝ)) ∧ (p.2 ∈ (Set.univ : Set ℝ))) ∧ (p.2 = (k * p.1))}))))) := by
  sorry

theorem proof_gap_exercise_3682_5
  (h1 : f = (fun (p : ℝ × ℝ) => ((p.1 - (p.2 ^ (2 : ℕ))) * ((2 * p.1) - (p.2 ^ (2 : ℕ))))))
  (h2 : (f (0, 0)) = 0)
  (h3 : (forall (k : ℝ), ((k ∈ (Set.univ : Set ℝ)) → (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f (x, (k * x))) = (((x ^ (2 : ℕ)) * (1 - ((k ^ (2 : ℕ)) * x))) * (2 - ((k ^ (2 : ℕ)) * x)))))))))
  (h4 : (forall (k : ℝ), (((k ≠ 0) ∧ (k ∈ (Set.univ : Set ℝ))) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < |(x)|)) ∧ (|(x)| < (1 /. (k ^ (2 : ℕ))))) → ((f (x, (k * x))) > 0))))))
  (h5 : (forall (k : ℝ), ((k ∈ (Set.univ : Set ℝ)) → ((0, 0) ∈ (lpMinimumPointsOn f ({p : ℝ × ℝ | ((p.1 ∈ (Set.univ : Set ℝ)) ∧ (p.2 ∈ (Set.univ : Set ℝ))) ∧ (p.2 = (k * p.1))}))))))
  : (forall (y : ℝ), ((y ∈ (Set.univ : Set ℝ)) → ((f (0, y)) = (y ^ (4 : ℕ))))) := by
  sorry

theorem proof_gap_exercise_3682_6
  (h1 : f = (fun (p : ℝ × ℝ) => ((p.1 - (p.2 ^ (2 : ℕ))) * ((2 * p.1) - (p.2 ^ (2 : ℕ))))))
  (h2 : (f (0, 0)) = 0)
  (h3 : (forall (k : ℝ), ((k ∈ (Set.univ : Set ℝ)) → (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f (x, (k * x))) = (((x ^ (2 : ℕ)) * (1 - ((k ^ (2 : ℕ)) * x))) * (2 - ((k ^ (2 : ℕ)) * x)))))))))
  (h4 : (forall (k : ℝ), (((k ≠ 0) ∧ (k ∈ (Set.univ : Set ℝ))) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < |(x)|)) ∧ (|(x)| < (1 /. (k ^ (2 : ℕ))))) → ((f (x, (k * x))) > 0))))))
  (h5 : (forall (k : ℝ), ((k ∈ (Set.univ : Set ℝ)) → ((0, 0) ∈ (lpMinimumPointsOn f ({p : ℝ × ℝ | ((p.1 ∈ (Set.univ : Set ℝ)) ∧ (p.2 ∈ (Set.univ : Set ℝ))) ∧ (p.2 = (k * p.1))}))))))
  (h6 : (forall (y : ℝ), ((y ∈ (Set.univ : Set ℝ)) → ((f (0, y)) = (y ^ (4 : ℕ))))))
  : (0, 0) ∈ (lpMinimumPointsOn f ({p : ℝ × ℝ | ((p.1 ∈ (Set.univ : Set ℝ)) ∧ (p.2 ∈ (Set.univ : Set ℝ))) ∧ (p.1 = 0)})) := by
  sorry

theorem proof_gap_exercise_3682_7
  (h1 : f = (fun (p : ℝ × ℝ) => ((p.1 - (p.2 ^ (2 : ℕ))) * ((2 * p.1) - (p.2 ^ (2 : ℕ))))))
  (h2 : (f (0, 0)) = 0)
  (h3 : (forall (k : ℝ), ((k ∈ (Set.univ : Set ℝ)) → (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f (x, (k * x))) = (((x ^ (2 : ℕ)) * (1 - ((k ^ (2 : ℕ)) * x))) * (2 - ((k ^ (2 : ℕ)) * x)))))))))
  (h4 : (forall (k : ℝ), (((k ≠ 0) ∧ (k ∈ (Set.univ : Set ℝ))) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < |(x)|)) ∧ (|(x)| < (1 /. (k ^ (2 : ℕ))))) → ((f (x, (k * x))) > 0))))))
  (h5 : (forall (k : ℝ), ((k ∈ (Set.univ : Set ℝ)) → ((0, 0) ∈ (lpMinimumPointsOn f ({p : ℝ × ℝ | ((p.1 ∈ (Set.univ : Set ℝ)) ∧ (p.2 ∈ (Set.univ : Set ℝ))) ∧ (p.2 = (k * p.1))}))))))
  (h6 : (forall (y : ℝ), ((y ∈ (Set.univ : Set ℝ)) → ((f (0, y)) = (y ^ (4 : ℕ))))))
  (h7 : (0, 0) ∈ (lpMinimumPointsOn f ({p : ℝ × ℝ | ((p.1 ∈ (Set.univ : Set ℝ)) ∧ (p.2 ∈ (Set.univ : Set ℝ))) ∧ (p.1 = 0)})))
  : (forall (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (a ∈ ({x_1 : ℝ | 0 < x_1}))) → (((f (a, (Real.rpow ((((15 : ℝ) /. (10 : ℝ))) * a) (((2 : ℝ))⁻¹)))) = ((-(((025 : ℝ) /. (100 : ℝ)))) * (a ^ (2 : ℕ)))) ∧ (((-(((025 : ℝ) /. (100 : ℝ)))) * (a ^ (2 : ℕ))) < 0)))) := by
  sorry

theorem proof_gap_exercise_3682_8
  (h1 : f = (fun (p : ℝ × ℝ) => ((p.1 - (p.2 ^ (2 : ℕ))) * ((2 * p.1) - (p.2 ^ (2 : ℕ))))))
  (h2 : (f (0, 0)) = 0)
  (h3 : (forall (k : ℝ), ((k ∈ (Set.univ : Set ℝ)) → (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f (x, (k * x))) = (((x ^ (2 : ℕ)) * (1 - ((k ^ (2 : ℕ)) * x))) * (2 - ((k ^ (2 : ℕ)) * x)))))))))
  (h4 : (forall (k : ℝ), (((k ≠ 0) ∧ (k ∈ (Set.univ : Set ℝ))) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < |(x)|)) ∧ (|(x)| < (1 /. (k ^ (2 : ℕ))))) → ((f (x, (k * x))) > 0))))))
  (h5 : (forall (k : ℝ), ((k ∈ (Set.univ : Set ℝ)) → ((0, 0) ∈ (lpMinimumPointsOn f ({p : ℝ × ℝ | ((p.1 ∈ (Set.univ : Set ℝ)) ∧ (p.2 ∈ (Set.univ : Set ℝ))) ∧ (p.2 = (k * p.1))}))))))
  (h6 : (forall (y : ℝ), ((y ∈ (Set.univ : Set ℝ)) → ((f (0, y)) = (y ^ (4 : ℕ))))))
  (h7 : (0, 0) ∈ (lpMinimumPointsOn f ({p : ℝ × ℝ | ((p.1 ∈ (Set.univ : Set ℝ)) ∧ (p.2 ∈ (Set.univ : Set ℝ))) ∧ (p.1 = 0)})))
  (h8 : (forall (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (a ∈ ({x_1 : ℝ | 0 < x_1}))) → (((f (a, (Real.rpow ((((15 : ℝ) /. (10 : ℝ))) * a) (((2 : ℝ))⁻¹)))) = ((-(((025 : ℝ) /. (100 : ℝ)))) * (a ^ (2 : ℕ)))) ∧ (((-(((025 : ℝ) /. (100 : ℝ)))) * (a ^ (2 : ℕ))) < 0)))))
  : (0, 0) ∉ (lpMinimumPoints f) := by
  sorry

theorem proof_gap_exercise_3682_9
  (h1 : f = (fun (p : ℝ × ℝ) => ((p.1 - (p.2 ^ (2 : ℕ))) * ((2 * p.1) - (p.2 ^ (2 : ℕ))))))
  (h2 : (f (0, 0)) = 0)
  (h3 : (forall (k : ℝ), ((k ∈ (Set.univ : Set ℝ)) → (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f (x, (k * x))) = (((x ^ (2 : ℕ)) * (1 - ((k ^ (2 : ℕ)) * x))) * (2 - ((k ^ (2 : ℕ)) * x)))))))))
  (h4 : (forall (k : ℝ), (((k ≠ 0) ∧ (k ∈ (Set.univ : Set ℝ))) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < |(x)|)) ∧ (|(x)| < (1 /. (k ^ (2 : ℕ))))) → ((f (x, (k * x))) > 0))))))
  (h5 : (forall (k : ℝ), ((k ∈ (Set.univ : Set ℝ)) → ((0, 0) ∈ (lpMinimumPointsOn f ({p : ℝ × ℝ | ((p.1 ∈ (Set.univ : Set ℝ)) ∧ (p.2 ∈ (Set.univ : Set ℝ))) ∧ (p.2 = (k * p.1))}))))))
  (h6 : (forall (y : ℝ), ((y ∈ (Set.univ : Set ℝ)) → ((f (0, y)) = (y ^ (4 : ℕ))))))
  (h7 : (0, 0) ∈ (lpMinimumPointsOn f ({p : ℝ × ℝ | ((p.1 ∈ (Set.univ : Set ℝ)) ∧ (p.2 ∈ (Set.univ : Set ℝ))) ∧ (p.1 = 0)})))
  (h8 : (forall (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (a ∈ ({x_1 : ℝ | 0 < x_1}))) → (((f (a, (Real.rpow ((((15 : ℝ) /. (10 : ℝ))) * a) (((2 : ℝ))⁻¹)))) = ((-(((025 : ℝ) /. (100 : ℝ)))) * (a ^ (2 : ℕ)))) ∧ (((-(((025 : ℝ) /. (100 : ℝ)))) * (a ^ (2 : ℕ))) < 0)))))
  (h9 : (0, 0) ∉ (lpMinimumPoints f))
  : Not (forall (f : (ℝ × ℝ -> ℝ)) (x_0 : ℝ) (y_0 : ℝ), (((((x_0 ∈ (Set.univ : Set ℝ)) ∧ (y_0 ∈ (Set.univ : Set ℝ))) ∧ (forall (k : ℝ), ((k ∈ (Set.univ : Set ℝ)) → ((x_0, y_0) ∈ (lpMinimumPointsOn f ({p : ℝ × ℝ | ((p.1 ∈ (Set.univ : Set ℝ)) ∧ (p.2 ∈ (Set.univ : Set ℝ))) ∧ ((p.2 - y_0) = (k * (p.1 - x_0)))})))))) ∧ ((x_0, y_0) ∈ (lpMinimumPointsOn f ({p : ℝ × ℝ | ((p.1 ∈ (Set.univ : Set ℝ)) ∧ (p.2 ∈ (Set.univ : Set ℝ))) ∧ (p.1 = x_0)})))) → ((x_0, y_0) ∈ (lpMinimumPoints f)))) := by
  sorry

theorem proof_gap_exercise_3682_10
  (h1 : f = (fun (p : ℝ × ℝ) => ((p.1 - (p.2 ^ (2 : ℕ))) * ((2 * p.1) - (p.2 ^ (2 : ℕ))))))
  (h2 : (f (0, 0)) = 0)
  (h3 : (forall (k : ℝ), ((k ∈ (Set.univ : Set ℝ)) → (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f (x, (k * x))) = (((x ^ (2 : ℕ)) * (1 - ((k ^ (2 : ℕ)) * x))) * (2 - ((k ^ (2 : ℕ)) * x)))))))))
  (h4 : (forall (k : ℝ), (((k ≠ 0) ∧ (k ∈ (Set.univ : Set ℝ))) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < |(x)|)) ∧ (|(x)| < (1 /. (k ^ (2 : ℕ))))) → ((f (x, (k * x))) > 0))))))
  (h5 : (forall (k : ℝ), ((k ∈ (Set.univ : Set ℝ)) → ((0, 0) ∈ (lpMinimumPointsOn f ({p : ℝ × ℝ | ((p.1 ∈ (Set.univ : Set ℝ)) ∧ (p.2 ∈ (Set.univ : Set ℝ))) ∧ (p.2 = (k * p.1))}))))))
  (h6 : (forall (y : ℝ), ((y ∈ (Set.univ : Set ℝ)) → ((f (0, y)) = (y ^ (4 : ℕ))))))
  (h7 : (0, 0) ∈ (lpMinimumPointsOn f ({p : ℝ × ℝ | ((p.1 ∈ (Set.univ : Set ℝ)) ∧ (p.2 ∈ (Set.univ : Set ℝ))) ∧ (p.1 = 0)})))
  (h8 : (forall (a : ℝ), (((a ∈ (Set.univ : Set ℝ)) ∧ (a ∈ ({x_1 : ℝ | 0 < x_1}))) → (((f (a, (Real.rpow ((((15 : ℝ) /. (10 : ℝ))) * a) (((2 : ℝ))⁻¹)))) = ((-(((025 : ℝ) /. (100 : ℝ)))) * (a ^ (2 : ℕ)))) ∧ (((-(((025 : ℝ) /. (100 : ℝ)))) * (a ^ (2 : ℕ))) < 0)))))
  (h9 : (0, 0) ∉ (lpMinimumPoints f))
  (h10 : Not (forall (f : (ℝ × ℝ -> ℝ)) (x_0 : ℝ) (y_0 : ℝ), (((((x_0 ∈ (Set.univ : Set ℝ)) ∧ (y_0 ∈ (Set.univ : Set ℝ))) ∧ (forall (k : ℝ), ((k ∈ (Set.univ : Set ℝ)) → ((x_0, y_0) ∈ (lpMinimumPointsOn f ({p : ℝ × ℝ | ((p.1 ∈ (Set.univ : Set ℝ)) ∧ (p.2 ∈ (Set.univ : Set ℝ))) ∧ ((p.2 - y_0) = (k * (p.1 - x_0)))})))))) ∧ ((x_0, y_0) ∈ (lpMinimumPointsOn f ({p : ℝ × ℝ | ((p.1 ∈ (Set.univ : Set ℝ)) ∧ (p.2 ∈ (Set.univ : Set ℝ))) ∧ (p.1 = x_0)})))) → ((x_0, y_0) ∈ (lpMinimumPoints f)))))
  : Not (forall (f : (ℝ × ℝ -> ℝ)) (x_0 : ℝ) (y_0 : ℝ), (((((x_0 ∈ (Set.univ : Set ℝ)) ∧ (y_0 ∈ (Set.univ : Set ℝ))) ∧ (forall (k : ℝ), ((k ∈ (Set.univ : Set ℝ)) → ((x_0, y_0) ∈ (lpMinimumPointsOn f ({p : ℝ × ℝ | ((p.1 ∈ (Set.univ : Set ℝ)) ∧ (p.2 ∈ (Set.univ : Set ℝ))) ∧ ((p.2 - y_0) = (k * (p.1 - x_0)))})))))) ∧ ((x_0, y_0) ∈ (lpMinimumPointsOn f ({p : ℝ × ℝ | ((p.1 ∈ (Set.univ : Set ℝ)) ∧ (p.2 ∈ (Set.univ : Set ℝ))) ∧ (p.1 = x_0)})))) → ((x_0, y_0) ∈ (lpMinimumPoints f)))) := by
  sorry
