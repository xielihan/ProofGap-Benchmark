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

-- exercise: exercise_2911

theorem proof_gap_exercise_2911_1
  (F : (ℝ -> ℝ))
  (n : ℕ)
  (h1 : n ∈ (Set.univ : Set ℕ))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| < 1)) → ((F x) = (∑' n_1, if (1 : ℕ) ≤ n_1 then (n_1 * (x ^ n_1)) else 0)))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| < 1)) → ((∫ t in (0 : ℝ)..x, ((F t) * (1 : ℝ))) = (∑' n_1, if (1 : ℕ) ≤ n_1 then ((n_1 * (x ^ (n_1 + 1))) /. (n_1 + 1)) else 0)))) := by
  sorry

theorem proof_gap_exercise_2911_2
  (F : (ℝ -> ℝ))
  (n : ℕ)
  (h1 : n ∈ (Set.univ : Set ℕ))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| < 1)) → ((F x) = (∑' n_1, if (1 : ℕ) ≤ n_1 then (n_1 * (x ^ n_1)) else 0)))))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| < 1)) → ((∫ t in (0 : ℝ)..x, ((F t) * (1 : ℝ))) = (∑' n_1, if (1 : ℕ) ≤ n_1 then ((n_1 * (x ^ (n_1 + 1))) /. (n_1 + 1)) else 0)))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| < 1)) → ((∫ t in (0 : ℝ)..x, ((F t) * (1 : ℝ))) = (∑' n_1, if (2 : ℕ) ≤ n_1 then ((1 - (1 /. n_1)) * (x ^ n_1)) else 0)))) := by
  sorry

theorem proof_gap_exercise_2911_3
  (F : (ℝ -> ℝ))
  (n : ℕ)
  (h1 : n ∈ (Set.univ : Set ℕ))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| < 1)) → ((F x) = (∑' n_1, if (1 : ℕ) ≤ n_1 then (n_1 * (x ^ n_1)) else 0)))))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| < 1)) → ((∫ t in (0 : ℝ)..x, ((F t) * (1 : ℝ))) = (∑' n_1, if (1 : ℕ) ≤ n_1 then ((n_1 * (x ^ (n_1 + 1))) /. (n_1 + 1)) else 0)))))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| < 1)) → ((∫ t in (0 : ℝ)..x, ((F t) * (1 : ℝ))) = (∑' n_1, if (2 : ℕ) ≤ n_1 then ((1 - (1 /. n_1)) * (x ^ n_1)) else 0)))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| < 1)) → ((∫ t in (0 : ℝ)..x, ((F t) * (1 : ℝ))) = ((∑' n_1, if (2 : ℕ) ≤ n_1 then (x ^ n_1) else 0) - (∑' n_1, if (2 : ℕ) ≤ n_1 then ((x ^ n_1) /. n_1) else 0))))) := by
  sorry

theorem proof_gap_exercise_2911_4
  (F : (ℝ -> ℝ))
  (n : ℕ)
  (h1 : n ∈ (Set.univ : Set ℕ))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| < 1)) → ((F x) = (∑' n_1, if (1 : ℕ) ≤ n_1 then (n_1 * (x ^ n_1)) else 0)))))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| < 1)) → ((∫ t in (0 : ℝ)..x, ((F t) * (1 : ℝ))) = (∑' n_1, if (1 : ℕ) ≤ n_1 then ((n_1 * (x ^ (n_1 + 1))) /. (n_1 + 1)) else 0)))))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| < 1)) → ((∫ t in (0 : ℝ)..x, ((F t) * (1 : ℝ))) = (∑' n_1, if (2 : ℕ) ≤ n_1 then ((1 - (1 /. n_1)) * (x ^ n_1)) else 0)))))
  (h5 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| < 1)) → ((∫ t in (0 : ℝ)..x, ((F t) * (1 : ℝ))) = ((∑' n_1, if (2 : ℕ) ≤ n_1 then (x ^ n_1) else 0) - (∑' n_1, if (2 : ℕ) ≤ n_1 then ((x ^ n_1) /. n_1) else 0))))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| < 1)) → ((∫ t in (0 : ℝ)..x, ((F t) * (1 : ℝ))) = ((x /. (1 - x)) + (Real.log (1 - x)))))) := by
  sorry

theorem proof_gap_exercise_2911_5
  (F : (ℝ -> ℝ))
  (n : ℕ)
  (h1 : n ∈ (Set.univ : Set ℕ))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| < 1)) → ((F x) = (∑' n_1, if (1 : ℕ) ≤ n_1 then (n_1 * (x ^ n_1)) else 0)))))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| < 1)) → ((∫ t in (0 : ℝ)..x, ((F t) * (1 : ℝ))) = (∑' n_1, if (1 : ℕ) ≤ n_1 then ((n_1 * (x ^ (n_1 + 1))) /. (n_1 + 1)) else 0)))))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| < 1)) → ((∫ t in (0 : ℝ)..x, ((F t) * (1 : ℝ))) = (∑' n_1, if (2 : ℕ) ≤ n_1 then ((1 - (1 /. n_1)) * (x ^ n_1)) else 0)))))
  (h5 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| < 1)) → ((∫ t in (0 : ℝ)..x, ((F t) * (1 : ℝ))) = ((∑' n_1, if (2 : ℕ) ≤ n_1 then (x ^ n_1) else 0) - (∑' n_1, if (2 : ℕ) ≤ n_1 then ((x ^ n_1) /. n_1) else 0))))))
  (h6 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| < 1)) → ((∫ t in (0 : ℝ)..x, ((F t) * (1 : ℝ))) = ((x /. (1 - x)) + (Real.log (1 - x)))))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| < 1)) → ((F x) = (iteratedDeriv 1 (fun t_1 => ((t_1 /. (1 - t_1)) + (Real.log (1 - t_1)))) x)))) := by
  sorry

theorem proof_gap_exercise_2911_6
  (F : (ℝ -> ℝ))
  (n : ℕ)
  (h1 : n ∈ (Set.univ : Set ℕ))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| < 1)) → ((F x) = (∑' n_1, if (1 : ℕ) ≤ n_1 then (n_1 * (x ^ n_1)) else 0)))))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| < 1)) → ((∫ t in (0 : ℝ)..x, ((F t) * (1 : ℝ))) = (∑' n_1, if (1 : ℕ) ≤ n_1 then ((n_1 * (x ^ (n_1 + 1))) /. (n_1 + 1)) else 0)))))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| < 1)) → ((∫ t in (0 : ℝ)..x, ((F t) * (1 : ℝ))) = (∑' n_1, if (2 : ℕ) ≤ n_1 then ((1 - (1 /. n_1)) * (x ^ n_1)) else 0)))))
  (h5 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| < 1)) → ((∫ t in (0 : ℝ)..x, ((F t) * (1 : ℝ))) = ((∑' n_1, if (2 : ℕ) ≤ n_1 then (x ^ n_1) else 0) - (∑' n_1, if (2 : ℕ) ≤ n_1 then ((x ^ n_1) /. n_1) else 0))))))
  (h6 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| < 1)) → ((∫ t in (0 : ℝ)..x, ((F t) * (1 : ℝ))) = ((x /. (1 - x)) + (Real.log (1 - x)))))))
  (h7 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| < 1)) → ((F x) = (iteratedDeriv 1 (fun t_1 => ((t_1 /. (1 - t_1)) + (Real.log (1 - t_1)))) x)))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| < 1)) → ((F x) = (x /. ((1 - x) ^ (2 : ℕ)))))) := by
  sorry

theorem proof_gap_exercise_2911_7
  (F : (ℝ -> ℝ))
  (n : ℕ)
  (h1 : n ∈ (Set.univ : Set ℕ))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| < 1)) → ((F x) = (∑' n_1, if (1 : ℕ) ≤ n_1 then (n_1 * (x ^ n_1)) else 0)))))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| < 1)) → ((∫ t in (0 : ℝ)..x, ((F t) * (1 : ℝ))) = (∑' n_1, if (1 : ℕ) ≤ n_1 then ((n_1 * (x ^ (n_1 + 1))) /. (n_1 + 1)) else 0)))))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| < 1)) → ((∫ t in (0 : ℝ)..x, ((F t) * (1 : ℝ))) = (∑' n_1, if (2 : ℕ) ≤ n_1 then ((1 - (1 /. n_1)) * (x ^ n_1)) else 0)))))
  (h5 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| < 1)) → ((∫ t in (0 : ℝ)..x, ((F t) * (1 : ℝ))) = ((∑' n_1, if (2 : ℕ) ≤ n_1 then (x ^ n_1) else 0) - (∑' n_1, if (2 : ℕ) ≤ n_1 then ((x ^ n_1) /. n_1) else 0))))))
  (h6 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| < 1)) → ((∫ t in (0 : ℝ)..x, ((F t) * (1 : ℝ))) = ((x /. (1 - x)) + (Real.log (1 - x)))))))
  (h7 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| < 1)) → ((F x) = (iteratedDeriv 1 (fun t_1 => ((t_1 /. (1 - t_1)) + (Real.log (1 - t_1)))) x)))))
  (h8 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| < 1)) → ((F x) = (x /. ((1 - x) ^ (2 : ℕ)))))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| < 1)) → ((∑' n_1, if (1 : ℕ) ≤ n_1 then (n_1 * (x ^ n_1)) else 0) = (x /. ((1 - x) ^ (2 : ℕ)))))) := by
  sorry

theorem proof_gap_exercise_2911_8
  (F : (ℝ -> ℝ))
  (n : ℕ)
  (h1 : n ∈ (Set.univ : Set ℕ))
  (h2 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| < 1)) → ((F x) = (∑' n_1, if (1 : ℕ) ≤ n_1 then (n_1 * (x ^ n_1)) else 0)))))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| < 1)) → ((∫ t in (0 : ℝ)..x, ((F t) * (1 : ℝ))) = (∑' n_1, if (1 : ℕ) ≤ n_1 then ((n_1 * (x ^ (n_1 + 1))) /. (n_1 + 1)) else 0)))))
  (h4 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| < 1)) → ((∫ t in (0 : ℝ)..x, ((F t) * (1 : ℝ))) = (∑' n_1, if (2 : ℕ) ≤ n_1 then ((1 - (1 /. n_1)) * (x ^ n_1)) else 0)))))
  (h5 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| < 1)) → ((∫ t in (0 : ℝ)..x, ((F t) * (1 : ℝ))) = ((∑' n_1, if (2 : ℕ) ≤ n_1 then (x ^ n_1) else 0) - (∑' n_1, if (2 : ℕ) ≤ n_1 then ((x ^ n_1) /. n_1) else 0))))))
  (h6 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| < 1)) → ((∫ t in (0 : ℝ)..x, ((F t) * (1 : ℝ))) = ((x /. (1 - x)) + (Real.log (1 - x)))))))
  (h7 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| < 1)) → ((F x) = (iteratedDeriv 1 (fun t_1 => ((t_1 /. (1 - t_1)) + (Real.log (1 - t_1)))) x)))))
  (h8 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| < 1)) → ((F x) = (x /. ((1 - x) ^ (2 : ℕ)))))))
  (h9 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| < 1)) → ((∑' n_1, if (1 : ℕ) ≤ n_1 then (n_1 * (x ^ n_1)) else 0) = (x /. ((1 - x) ^ (2 : ℕ)))))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (|(x)| = 1)) → (¬ Summable (fun (n_1 : ℕ) => if (1 : ℕ) ≤ n_1 then (n_1 * (x ^ n_1)) else 0)))) := by
  sorry
