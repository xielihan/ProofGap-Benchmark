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

-- exercise: exercise_64

theorem proof_gap_exercise_64_1
  (a : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : a > 1)
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > 0))) → (((b : ℕ → _) n) = (Real.rpow (n : ℝ) (((n : ℝ))⁻¹)))))
  : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((b n) = (Real.rpow (n : ℝ) (((n : ℝ))⁻¹))))) := by
  sorry

theorem proof_gap_exercise_64_2
  (a : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : a > 1)
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > 0))) → (((b : ℕ → _) n) = (Real.rpow (n : ℝ) (((n : ℝ))⁻¹)))))
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((b n) = (Real.rpow (n : ℝ) (((n : ℝ))⁻¹))))))
  : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((b n) > 1))) := by
  sorry

theorem proof_gap_exercise_64_3
  (a : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : a > 1)
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > 0))) → (((b : ℕ → _) n) = (Real.rpow (n : ℝ) (((n : ℝ))⁻¹)))))
  (h4 : (forall (n : ℕ), ((n ∈ ({n_1 : ℕ | 0 < n_1})) → ((b n) = (Real.rpow (n : ℝ) (((n : ℝ))⁻¹))))))
  (h5 : (forall (n : ℕ), (((n ∈ ({n_1 : ℕ | 0 < n_1})) ∧ (n > 1)) → ((b n) > 1))))
  : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (((b n) ^ n) > (((n ^ (2 : ℕ)) /. 4) * (((b n) - 1) ^ (2 : ℕ)))))) := by
  sorry

theorem proof_gap_exercise_64_4
  (a : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : a > 1)
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > 0))) → (((b : ℕ → _) n) = (Real.rpow (n : ℝ) (((n : ℝ))⁻¹)))))
  (h4 : (forall (n : ℕ), ((n ∈ ({n_1 : ℕ | 0 < n_1})) → ((b n) = (Real.rpow (n : ℝ) (((n : ℝ))⁻¹))))))
  (h5 : (forall (n : ℕ), (((n ∈ ({n_1 : ℕ | 0 < n_1})) ∧ (n > 1)) → ((b n) > 1))))
  (h6 : (forall (n : ℕ), ((n ∈ ({n_1 : ℕ | 0 < n_1})) → (((b n) ^ n) > (((n ^ (2 : ℕ)) /. 4) * (((b n) - 1) ^ (2 : ℕ)))))))
  : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (n > (((n ^ (2 : ℕ)) /. 4) * (((Real.rpow (n : ℝ) (((n : ℝ))⁻¹)) - 1) ^ (2 : ℕ)))))) := by
  sorry

theorem proof_gap_exercise_64_5
  (a : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : a > 1)
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > 0))) → (((b : ℕ → _) n) = (Real.rpow (n : ℝ) (((n : ℝ))⁻¹)))))
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((b n) = (Real.rpow (n : ℝ) (((n : ℝ))⁻¹))))))
  (h5 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((b n) > 1))))
  (h6 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (((b n) ^ n) > (((n ^ (2 : ℕ)) /. 4) * (((b n) - 1) ^ (2 : ℕ)))))))
  (h7 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (n > (((n ^ (2 : ℕ)) /. 4) * (((Real.rpow (n : ℝ) (((n : ℝ))⁻¹)) - 1) ^ (2 : ℕ)))))))
  : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (0 < ((Real.rpow (n : ℝ) (((n : ℝ))⁻¹)) - 1)))) := by
  sorry

theorem proof_gap_exercise_64_6
  (a : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : a > 1)
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > 0))) → (((b : ℕ → _) n) = (Real.rpow (n : ℝ) (((n : ℝ))⁻¹)))))
  (h4 : (forall (n : ℕ), ((n ∈ ({n_1 : ℕ | 0 < n_1})) → ((b n) = (Real.rpow (n : ℝ) (((n : ℝ))⁻¹))))))
  (h5 : (forall (n : ℕ), (((n ∈ ({n_1 : ℕ | 0 < n_1})) ∧ (n > 1)) → ((b n) > 1))))
  (h6 : (forall (n : ℕ), ((n ∈ ({n_1 : ℕ | 0 < n_1})) → (((b n) ^ n) > (((n ^ (2 : ℕ)) /. 4) * (((b n) - 1) ^ (2 : ℕ)))))))
  (h7 : (forall (n : ℕ), ((n ∈ ({n_1 : ℕ | 0 < n_1})) → (n > (((n ^ (2 : ℕ)) /. 4) * (((Real.rpow (n : ℝ) (((n : ℝ))⁻¹)) - 1) ^ (2 : ℕ)))))))
  (h8 : (forall (n : ℕ), (((n ∈ ({n_1 : ℕ | 0 < n_1})) ∧ (n > 1)) → (0 < ((Real.rpow (n : ℝ) (((n : ℝ))⁻¹)) - 1)))))
  : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (((Real.rpow (n : ℝ) (((n : ℝ))⁻¹)) - 1) < (2 /. (Real.rpow (n : ℝ) (((2 : ℝ))⁻¹)))))) := by
  sorry

theorem proof_gap_exercise_64_7
  (a : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : a > 1)
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > 0))) → (((b : ℕ → _) n) = (Real.rpow (n : ℝ) (((n : ℝ))⁻¹)))))
  (h4 : (forall (n : ℕ), ((n ∈ ({n_1 : ℕ | 0 < n_1})) → ((b n) = (Real.rpow (n : ℝ) (((n : ℝ))⁻¹))))))
  (h5 : (forall (n : ℕ), (((n ∈ ({n_1 : ℕ | 0 < n_1})) ∧ (n > 1)) → ((b n) > 1))))
  (h6 : (forall (n : ℕ), ((n ∈ ({n_1 : ℕ | 0 < n_1})) → (((b n) ^ n) > (((n ^ (2 : ℕ)) /. 4) * (((b n) - 1) ^ (2 : ℕ)))))))
  (h7 : (forall (n : ℕ), ((n ∈ ({n_1 : ℕ | 0 < n_1})) → (n > (((n ^ (2 : ℕ)) /. 4) * (((Real.rpow (n : ℝ) (((n : ℝ))⁻¹)) - 1) ^ (2 : ℕ)))))))
  (h8 : (forall (n : ℕ), (((n ∈ ({n_1 : ℕ | 0 < n_1})) ∧ (n > 1)) → (0 < ((Real.rpow (n : ℝ) (((n : ℝ))⁻¹)) - 1)))))
  (h9 : (forall (n : ℕ), ((n ∈ ({n_1 : ℕ | 0 < n_1})) → (((Real.rpow (n : ℝ) (((n : ℝ))⁻¹)) - 1) < (2 /. (Real.rpow (n : ℝ) (((2 : ℝ))⁻¹)))))))
  : Tendsto (fun n : ℕ => (Real.rpow n ((n)⁻¹))) atTop (𝓝 1) := by
  sorry

theorem proof_gap_exercise_64_8
  (a : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : a > 1)
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > 0))) → (((b : ℕ → _) n) = (Real.rpow (n : ℝ) (((n : ℝ))⁻¹)))))
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((b n) = (Real.rpow (n : ℝ) (((n : ℝ))⁻¹))))))
  (h5 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((b n) > 1))))
  (h6 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (((b n) ^ n) > (((n ^ (2 : ℕ)) /. 4) * (((b n) - 1) ^ (2 : ℕ)))))))
  (h7 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (n > (((n ^ (2 : ℕ)) /. 4) * (((Real.rpow (n : ℝ) (((n : ℝ))⁻¹)) - 1) ^ (2 : ℕ)))))))
  (h8 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (0 < ((Real.rpow (n : ℝ) (((n : ℝ))⁻¹)) - 1)))))
  (h9 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (((Real.rpow (n : ℝ) (((n : ℝ))⁻¹)) - 1) < (2 /. (Real.rpow (n : ℝ) (((2 : ℝ))⁻¹)))))))
  (h10 : Tendsto (fun n : ℕ => (Real.rpow n ((n)⁻¹))) atTop (𝓝 1))
  : Tendsto (fun n : ℕ => (b n)) atTop (𝓝 1) := by
  sorry

theorem proof_gap_exercise_64_9
  (a : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : a > 1)
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > 0))) → (((b : ℕ → _) n) = (Real.rpow (n : ℝ) (((n : ℝ))⁻¹)))))
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((b n) = (Real.rpow (n : ℝ) (((n : ℝ))⁻¹))))))
  (h5 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((b n) > 1))))
  (h6 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (((b n) ^ n) > (((n ^ (2 : ℕ)) /. 4) * (((b n) - 1) ^ (2 : ℕ)))))))
  (h7 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (n > (((n ^ (2 : ℕ)) /. 4) * (((Real.rpow (n : ℝ) (((n : ℝ))⁻¹)) - 1) ^ (2 : ℕ)))))))
  (h8 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (0 < ((Real.rpow (n : ℝ) (((n : ℝ))⁻¹)) - 1)))))
  (h9 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (((Real.rpow (n : ℝ) (((n : ℝ))⁻¹)) - 1) < (2 /. (Real.rpow (n : ℝ) (((2 : ℝ))⁻¹)))))))
  (h10 : Tendsto (fun n : ℕ => (Real.rpow n ((n)⁻¹))) atTop (𝓝 1))
  (h11 : Tendsto (fun n : ℕ => (b n)) atTop (𝓝 1))
  : Tendsto (fun n : ℕ => (b n)) atTop (𝓝 1) := by
  sorry

theorem proof_gap_exercise_64_10
  (a : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : a > 1)
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > 0))) → (((b : ℕ → _) n) = (Real.rpow (n : ℝ) (((n : ℝ))⁻¹)))))
  (h4 : (forall (n : ℕ), ((n ∈ ({n_1 : ℕ | 0 < n_1})) → ((b n) = (Real.rpow (n : ℝ) (((n : ℝ))⁻¹))))))
  (h5 : (forall (n : ℕ), (((n ∈ ({n_1 : ℕ | 0 < n_1})) ∧ (n > 1)) → ((b n) > 1))))
  (h6 : (forall (n : ℕ), ((n ∈ ({n_1 : ℕ | 0 < n_1})) → (((b n) ^ n) > (((n ^ (2 : ℕ)) /. 4) * (((b n) - 1) ^ (2 : ℕ)))))))
  (h7 : (forall (n : ℕ), ((n ∈ ({n_1 : ℕ | 0 < n_1})) → (n > (((n ^ (2 : ℕ)) /. 4) * (((Real.rpow (n : ℝ) (((n : ℝ))⁻¹)) - 1) ^ (2 : ℕ)))))))
  (h8 : (forall (n : ℕ), (((n ∈ ({n_1 : ℕ | 0 < n_1})) ∧ (n > 1)) → (0 < ((Real.rpow (n : ℝ) (((n : ℝ))⁻¹)) - 1)))))
  (h9 : (forall (n : ℕ), ((n ∈ ({n_1 : ℕ | 0 < n_1})) → (((Real.rpow (n : ℝ) (((n : ℝ))⁻¹)) - 1) < (2 /. (Real.rpow (n : ℝ) (((2 : ℝ))⁻¹)))))))
  (h10 : Tendsto (fun n : ℕ => (Real.rpow n ((n)⁻¹))) atTop (𝓝 1))
  (h11 : Tendsto (fun n : ℕ => (b n)) atTop (𝓝 1))
  (h12 : Tendsto (fun n : ℕ => (b n)) atTop (𝓝 1))
  : (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → ((Real.rpow a v_uCE_uB5) > 1))) := by
  sorry

theorem proof_gap_exercise_64_11
  (a : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : a > 1)
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > 0))) → (((b : ℕ → _) n) = (Real.rpow (n : ℝ) (((n : ℝ))⁻¹)))))
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((b n) = (Real.rpow (n : ℝ) (((n : ℝ))⁻¹))))))
  (h5 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((b n) > 1))))
  (h6 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (((b n) ^ n) > (((n ^ (2 : ℕ)) /. 4) * (((b n) - 1) ^ (2 : ℕ)))))))
  (h7 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (n > (((n ^ (2 : ℕ)) /. 4) * (((Real.rpow (n : ℝ) (((n : ℝ))⁻¹)) - 1) ^ (2 : ℕ)))))))
  (h8 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (0 < ((Real.rpow (n : ℝ) (((n : ℝ))⁻¹)) - 1)))))
  (h9 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (((Real.rpow (n : ℝ) (((n : ℝ))⁻¹)) - 1) < (2 /. (Real.rpow (n : ℝ) (((2 : ℝ))⁻¹)))))))
  (h10 : Tendsto (fun n : ℕ => (Real.rpow n ((n)⁻¹))) atTop (𝓝 1))
  (h11 : Tendsto (fun n : ℕ => (b n)) atTop (𝓝 1))
  (h12 : Tendsto (fun n : ℕ => (b n)) atTop (𝓝 1))
  (h13 : (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → ((Real.rpow a v_uCE_uB5) > 1))))
  : (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (N : ℕ), (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n > N)) → ((Real.rpow (n : ℝ) (((n : ℝ))⁻¹)) < (Real.rpow a v_uCE_uB5)))))))) := by
  sorry

theorem proof_gap_exercise_64_12
  (a : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : a > 1)
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > 0))) → (((b : ℕ → _) n) = (Real.rpow (n : ℝ) (((n : ℝ))⁻¹)))))
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((b n) = (Real.rpow (n : ℝ) (((n : ℝ))⁻¹))))))
  (h5 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((b n) > 1))))
  (h6 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (((b n) ^ n) > (((n ^ (2 : ℕ)) /. 4) * (((b n) - 1) ^ (2 : ℕ)))))))
  (h7 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (n > (((n ^ (2 : ℕ)) /. 4) * (((Real.rpow (n : ℝ) (((n : ℝ))⁻¹)) - 1) ^ (2 : ℕ)))))))
  (h8 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (0 < ((Real.rpow (n : ℝ) (((n : ℝ))⁻¹)) - 1)))))
  (h9 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (((Real.rpow (n : ℝ) (((n : ℝ))⁻¹)) - 1) < (2 /. (Real.rpow (n : ℝ) (((2 : ℝ))⁻¹)))))))
  (h10 : Tendsto (fun n : ℕ => (Real.rpow n ((n)⁻¹))) atTop (𝓝 1))
  (h11 : Tendsto (fun n : ℕ => (b n)) atTop (𝓝 1))
  (h12 : Tendsto (fun n : ℕ => (b n)) atTop (𝓝 1))
  (h13 : (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → ((Real.rpow a v_uCE_uB5) > 1))))
  (h14 : (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (N : ℕ), (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n > N)) → ((Real.rpow (n : ℝ) (((n : ℝ))⁻¹)) < (Real.rpow a v_uCE_uB5)))))))))
  : (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (N : ℕ), (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n > N)) → ((Real.rpow (n : ℝ) (((n : ℝ))⁻¹)) < (Real.rpow a v_uCE_uB5)))))))) := by
  sorry

theorem proof_gap_exercise_64_13
  (a : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : a > 1)
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > 0))) → (((b : ℕ → _) n) = (Real.rpow (n : ℝ) (((n : ℝ))⁻¹)))))
  (h4 : (forall (n : ℕ), ((n ∈ ({n_1 : ℕ | 0 < n_1})) → ((b n) = (Real.rpow (n : ℝ) (((n : ℝ))⁻¹))))))
  (h5 : (forall (n : ℕ), (((n ∈ ({n_1 : ℕ | 0 < n_1})) ∧ (n > 1)) → ((b n) > 1))))
  (h6 : (forall (n : ℕ), ((n ∈ ({n_1 : ℕ | 0 < n_1})) → (((b n) ^ n) > (((n ^ (2 : ℕ)) /. 4) * (((b n) - 1) ^ (2 : ℕ)))))))
  (h7 : (forall (n : ℕ), ((n ∈ ({n_1 : ℕ | 0 < n_1})) → (n > (((n ^ (2 : ℕ)) /. 4) * (((Real.rpow (n : ℝ) (((n : ℝ))⁻¹)) - 1) ^ (2 : ℕ)))))))
  (h8 : (forall (n : ℕ), (((n ∈ ({n_1 : ℕ | 0 < n_1})) ∧ (n > 1)) → (0 < ((Real.rpow (n : ℝ) (((n : ℝ))⁻¹)) - 1)))))
  (h9 : (forall (n : ℕ), ((n ∈ ({n_1 : ℕ | 0 < n_1})) → (((Real.rpow (n : ℝ) (((n : ℝ))⁻¹)) - 1) < (2 /. (Real.rpow (n : ℝ) (((2 : ℝ))⁻¹)))))))
  (h10 : Tendsto (fun n : ℕ => (Real.rpow n ((n)⁻¹))) atTop (𝓝 1))
  (h11 : Tendsto (fun n : ℕ => (b n)) atTop (𝓝 1))
  (h12 : Tendsto (fun n : ℕ => (b n)) atTop (𝓝 1))
  (h13 : (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → ((Real.rpow a v_uCE_uB5) > 1))))
  (h14 : (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (N : ℕ), ((N ∈ ({n_1 : ℕ | 0 < n_1})) ∧ (forall (n : ℕ), (((n ∈ ({n_1 : ℕ | 0 < n_1})) ∧ (n > N)) → ((Real.rpow (n : ℝ) (((n : ℝ))⁻¹)) < (Real.rpow a v_uCE_uB5)))))))))
  (h15 : (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (N : ℕ), ((N ∈ ({n_1 : ℕ | 0 < n_1})) ∧ (forall (n : ℕ), (((n ∈ ({n_1 : ℕ | 0 < n_1})) ∧ (n > N)) → ((Real.rpow (n : ℝ) (((n : ℝ))⁻¹)) < (Real.rpow a v_uCE_uB5)))))))))
  : (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (N : ℕ), (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n > N)) → (n < (Real.rpow a (n * v_uCE_uB5))))))))) := by
  sorry

theorem proof_gap_exercise_64_14
  (a : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : a > 1)
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > 0))) → (((b : ℕ → _) n) = (Real.rpow (n : ℝ) (((n : ℝ))⁻¹)))))
  (h4 : (forall (n : ℕ), ((n ∈ ({n_1 : ℕ | 0 < n_1})) → ((b n) = (Real.rpow (n : ℝ) (((n : ℝ))⁻¹))))))
  (h5 : (forall (n : ℕ), (((n ∈ ({n_1 : ℕ | 0 < n_1})) ∧ (n > 1)) → ((b n) > 1))))
  (h6 : (forall (n : ℕ), ((n ∈ ({n_1 : ℕ | 0 < n_1})) → (((b n) ^ n) > (((n ^ (2 : ℕ)) /. 4) * (((b n) - 1) ^ (2 : ℕ)))))))
  (h7 : (forall (n : ℕ), ((n ∈ ({n_1 : ℕ | 0 < n_1})) → (n > (((n ^ (2 : ℕ)) /. 4) * (((Real.rpow (n : ℝ) (((n : ℝ))⁻¹)) - 1) ^ (2 : ℕ)))))))
  (h8 : (forall (n : ℕ), (((n ∈ ({n_1 : ℕ | 0 < n_1})) ∧ (n > 1)) → (0 < ((Real.rpow (n : ℝ) (((n : ℝ))⁻¹)) - 1)))))
  (h9 : (forall (n : ℕ), ((n ∈ ({n_1 : ℕ | 0 < n_1})) → (((Real.rpow (n : ℝ) (((n : ℝ))⁻¹)) - 1) < (2 /. (Real.rpow (n : ℝ) (((2 : ℝ))⁻¹)))))))
  (h10 : Tendsto (fun n : ℕ => (Real.rpow n ((n)⁻¹))) atTop (𝓝 1))
  (h11 : Tendsto (fun n : ℕ => (b n)) atTop (𝓝 1))
  (h12 : Tendsto (fun n : ℕ => (b n)) atTop (𝓝 1))
  (h13 : (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → ((Real.rpow a v_uCE_uB5) > 1))))
  (h14 : (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (N : ℕ), ((N ∈ ({n_1 : ℕ | 0 < n_1})) ∧ (forall (n : ℕ), (((n ∈ ({n_1 : ℕ | 0 < n_1})) ∧ (n > N)) → ((Real.rpow (n : ℝ) (((n : ℝ))⁻¹)) < (Real.rpow a v_uCE_uB5)))))))))
  (h15 : (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (N : ℕ), ((N ∈ ({n_1 : ℕ | 0 < n_1})) ∧ (forall (n : ℕ), (((n ∈ ({n_1 : ℕ | 0 < n_1})) ∧ (n > N)) → ((Real.rpow (n : ℝ) (((n : ℝ))⁻¹)) < (Real.rpow a v_uCE_uB5)))))))))
  (h16 : (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (N : ℕ), ((N ∈ ({n_1 : ℕ | 0 < n_1})) ∧ (forall (n : ℕ), (((n ∈ ({n_1 : ℕ | 0 < n_1})) ∧ (n > N)) → (n < (Real.rpow a (n * v_uCE_uB5))))))))))
  : (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (N : ℕ), (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n > N)) → (0 < ((Real.logb a (n : ℝ)) /. n)))))))) := by
  sorry

theorem proof_gap_exercise_64_15
  (a : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : a > 1)
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > 0))) → (((b : ℕ → _) n) = (Real.rpow (n : ℝ) (((n : ℝ))⁻¹)))))
  (h4 : (forall (n : ℕ), ((n ∈ ({n_1 : ℕ | 0 < n_1})) → ((b n) = (Real.rpow (n : ℝ) (((n : ℝ))⁻¹))))))
  (h5 : (forall (n : ℕ), (((n ∈ ({n_1 : ℕ | 0 < n_1})) ∧ (n > 1)) → ((b n) > 1))))
  (h6 : (forall (n : ℕ), ((n ∈ ({n_1 : ℕ | 0 < n_1})) → (((b n) ^ n) > (((n ^ (2 : ℕ)) /. 4) * (((b n) - 1) ^ (2 : ℕ)))))))
  (h7 : (forall (n : ℕ), ((n ∈ ({n_1 : ℕ | 0 < n_1})) → (n > (((n ^ (2 : ℕ)) /. 4) * (((Real.rpow (n : ℝ) (((n : ℝ))⁻¹)) - 1) ^ (2 : ℕ)))))))
  (h8 : (forall (n : ℕ), (((n ∈ ({n_1 : ℕ | 0 < n_1})) ∧ (n > 1)) → (0 < ((Real.rpow (n : ℝ) (((n : ℝ))⁻¹)) - 1)))))
  (h9 : (forall (n : ℕ), ((n ∈ ({n_1 : ℕ | 0 < n_1})) → (((Real.rpow (n : ℝ) (((n : ℝ))⁻¹)) - 1) < (2 /. (Real.rpow (n : ℝ) (((2 : ℝ))⁻¹)))))))
  (h10 : Tendsto (fun n : ℕ => (Real.rpow n ((n)⁻¹))) atTop (𝓝 1))
  (h11 : Tendsto (fun n : ℕ => (b n)) atTop (𝓝 1))
  (h12 : Tendsto (fun n : ℕ => (b n)) atTop (𝓝 1))
  (h13 : (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → ((Real.rpow a v_uCE_uB5) > 1))))
  (h14 : (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (N : ℕ), ((N ∈ ({n_1 : ℕ | 0 < n_1})) ∧ (forall (n : ℕ), (((n ∈ ({n_1 : ℕ | 0 < n_1})) ∧ (n > N)) → ((Real.rpow (n : ℝ) (((n : ℝ))⁻¹)) < (Real.rpow a v_uCE_uB5)))))))))
  (h15 : (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (N : ℕ), ((N ∈ ({n_1 : ℕ | 0 < n_1})) ∧ (forall (n : ℕ), (((n ∈ ({n_1 : ℕ | 0 < n_1})) ∧ (n > N)) → ((Real.rpow (n : ℝ) (((n : ℝ))⁻¹)) < (Real.rpow a v_uCE_uB5)))))))))
  (h16 : (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (N : ℕ), ((N ∈ ({n_1 : ℕ | 0 < n_1})) ∧ (forall (n : ℕ), (((n ∈ ({n_1 : ℕ | 0 < n_1})) ∧ (n > N)) → (n < (Real.rpow a (n * v_uCE_uB5))))))))))
  (h17 : (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (N : ℕ), ((N ∈ ({n_1 : ℕ | 0 < n_1})) ∧ (forall (n : ℕ), (((n ∈ ({n_1 : ℕ | 0 < n_1})) ∧ (n > N)) → (0 < ((Real.logb a (n : ℝ)) /. n)))))))))
  : (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (N : ℕ), (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n > N)) → (((Real.logb a (n : ℝ)) /. n) < v_uCE_uB5))))))) := by
  sorry

theorem proof_gap_exercise_64_16
  (a : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : a > 1)
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > 0))) → (((b : ℕ → _) n) = (Real.rpow (n : ℝ) (((n : ℝ))⁻¹)))))
  (h4 : (forall (n : ℕ), ((n ∈ ({n_1 : ℕ | 0 < n_1})) → ((b n) = (Real.rpow (n : ℝ) (((n : ℝ))⁻¹))))))
  (h5 : (forall (n : ℕ), (((n ∈ ({n_1 : ℕ | 0 < n_1})) ∧ (n > 1)) → ((b n) > 1))))
  (h6 : (forall (n : ℕ), ((n ∈ ({n_1 : ℕ | 0 < n_1})) → (((b n) ^ n) > (((n ^ (2 : ℕ)) /. 4) * (((b n) - 1) ^ (2 : ℕ)))))))
  (h7 : (forall (n : ℕ), ((n ∈ ({n_1 : ℕ | 0 < n_1})) → (n > (((n ^ (2 : ℕ)) /. 4) * (((Real.rpow (n : ℝ) (((n : ℝ))⁻¹)) - 1) ^ (2 : ℕ)))))))
  (h8 : (forall (n : ℕ), (((n ∈ ({n_1 : ℕ | 0 < n_1})) ∧ (n > 1)) → (0 < ((Real.rpow (n : ℝ) (((n : ℝ))⁻¹)) - 1)))))
  (h9 : (forall (n : ℕ), ((n ∈ ({n_1 : ℕ | 0 < n_1})) → (((Real.rpow (n : ℝ) (((n : ℝ))⁻¹)) - 1) < (2 /. (Real.rpow (n : ℝ) (((2 : ℝ))⁻¹)))))))
  (h10 : Tendsto (fun n : ℕ => (Real.rpow n ((n)⁻¹))) atTop (𝓝 1))
  (h11 : Tendsto (fun n : ℕ => (b n)) atTop (𝓝 1))
  (h12 : Tendsto (fun n : ℕ => (b n)) atTop (𝓝 1))
  (h13 : (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → ((Real.rpow a v_uCE_uB5) > 1))))
  (h14 : (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (N : ℕ), ((N ∈ ({n_1 : ℕ | 0 < n_1})) ∧ (forall (n : ℕ), (((n ∈ ({n_1 : ℕ | 0 < n_1})) ∧ (n > N)) → ((Real.rpow (n : ℝ) (((n : ℝ))⁻¹)) < (Real.rpow a v_uCE_uB5)))))))))
  (h15 : (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (N : ℕ), ((N ∈ ({n_1 : ℕ | 0 < n_1})) ∧ (forall (n : ℕ), (((n ∈ ({n_1 : ℕ | 0 < n_1})) ∧ (n > N)) → ((Real.rpow (n : ℝ) (((n : ℝ))⁻¹)) < (Real.rpow a v_uCE_uB5)))))))))
  (h16 : (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (N : ℕ), ((N ∈ ({n_1 : ℕ | 0 < n_1})) ∧ (forall (n : ℕ), (((n ∈ ({n_1 : ℕ | 0 < n_1})) ∧ (n > N)) → (n < (Real.rpow a (n * v_uCE_uB5))))))))))
  (h17 : (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (N : ℕ), ((N ∈ ({n_1 : ℕ | 0 < n_1})) ∧ (forall (n : ℕ), (((n ∈ ({n_1 : ℕ | 0 < n_1})) ∧ (n > N)) → (0 < ((Real.logb a (n : ℝ)) /. n)))))))))
  (h18 : (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (N : ℕ), ((N ∈ ({n_1 : ℕ | 0 < n_1})) ∧ (forall (n : ℕ), (((n ∈ ({n_1 : ℕ | 0 < n_1})) ∧ (n > N)) → (((Real.logb a (n : ℝ)) /. n) < v_uCE_uB5))))))))
  : Tendsto (fun n : ℕ => ((Real.logb a n) /. n)) atTop (𝓝 0) := by
  sorry

theorem proof_gap_exercise_64_17
  (a : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : a > 1)
  (h3 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n > 0))) → (((b : ℕ → _) n) = (Real.rpow (n : ℝ) (((n : ℝ))⁻¹)))))
  (h4 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((b n) = (Real.rpow (n : ℝ) (((n : ℝ))⁻¹))))))
  (h5 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((b n) > 1))))
  (h6 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (((b n) ^ n) > (((n ^ (2 : ℕ)) /. 4) * (((b n) - 1) ^ (2 : ℕ)))))))
  (h7 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (n > (((n ^ (2 : ℕ)) /. 4) * (((Real.rpow (n : ℝ) (((n : ℝ))⁻¹)) - 1) ^ (2 : ℕ)))))))
  (h8 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (0 < ((Real.rpow (n : ℝ) (((n : ℝ))⁻¹)) - 1)))))
  (h9 : (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (((Real.rpow (n : ℝ) (((n : ℝ))⁻¹)) - 1) < (2 /. (Real.rpow (n : ℝ) (((2 : ℝ))⁻¹)))))))
  (h10 : Tendsto (fun n : ℕ => (Real.rpow n ((n)⁻¹))) atTop (𝓝 1))
  (h11 : Tendsto (fun n : ℕ => (b n)) atTop (𝓝 1))
  (h12 : Tendsto (fun n : ℕ => (b n)) atTop (𝓝 1))
  (h13 : (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → ((Real.rpow a v_uCE_uB5) > 1))))
  (h14 : (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (N : ℕ), (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n > N)) → ((Real.rpow (n : ℝ) (((n : ℝ))⁻¹)) < (Real.rpow a v_uCE_uB5)))))))))
  (h15 : (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (N : ℕ), (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n > N)) → ((Real.rpow (n : ℝ) (((n : ℝ))⁻¹)) < (Real.rpow a v_uCE_uB5)))))))))
  (h16 : (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (N : ℕ), (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n > N)) → (n < (Real.rpow a (n * v_uCE_uB5))))))))))
  (h17 : (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (N : ℕ), (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n > N)) → (0 < ((Real.logb a (n : ℝ)) /. n)))))))))
  (h18 : (forall (v_uCE_uB5 : ℝ), (((v_uCE_uB5 ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_uB5 > 0)) → (exists (N : ℕ), (((N ∈ (Set.univ : Set ℕ)) ∧ (N ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (forall (n : ℕ), ((((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (n > N)) → (((Real.logb a (n : ℝ)) /. n) < v_uCE_uB5))))))))
  (h19 : Tendsto (fun n : ℕ => ((Real.logb a n) /. n)) atTop (𝓝 0))
  : Tendsto (fun n : ℕ => ((Real.logb a n) /. n)) atTop (𝓝 0) := by
  sorry
