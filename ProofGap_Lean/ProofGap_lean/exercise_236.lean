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

-- exercise: exercise_236

theorem proof_gap_exercise_236_1
  (f : (ℝ -> ℝ))
  (k : ℝ)
  (T : ℝ)
  (h1 : k ∈ (Set.univ : Set ℝ))
  (h2 : T ∈ (Set.univ : Set ℝ))
  (h3 : k > 0)
  (h4 : T > 0)
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f (x + T)) = (k * (f x))))))
  (h6 : a = (Real.rpow k (1 /. T)))
  : a > 0 := by
  sorry

theorem proof_gap_exercise_236_2
  (f : (ℝ -> ℝ))
  (k : ℝ)
  (T : ℝ)
  (h1 : k ∈ (Set.univ : Set ℝ))
  (h2 : T ∈ (Set.univ : Set ℝ))
  (h3 : k > 0)
  (h4 : T > 0)
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f (x + T)) = (k * (f x))))))
  (h6 : a = (Real.rpow k (1 /. T)))
  (h7 : a > 0)
  : (Real.rpow a T) = k := by
  sorry

theorem proof_gap_exercise_236_3
  (f : (ℝ -> ℝ))
  (k : ℝ)
  (T : ℝ)
  (h1 : k ∈ (Set.univ : Set ℝ))
  (h2 : T ∈ (Set.univ : Set ℝ))
  (h3 : k > 0)
  (h4 : T > 0)
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f (x + T)) = (k * (f x))))))
  (h6 : a = (Real.rpow k (1 /. T)))
  (h7 : a > 0)
  (h8 : (Real.rpow a T) = k)
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f (x + T)) = ((Real.rpow a T) * (f x))))) := by
  sorry

theorem proof_gap_exercise_236_4
  (f : (ℝ -> ℝ))
  (k : ℝ)
  (T : ℝ)
  (h1 : k ∈ (Set.univ : Set ℝ))
  (h2 : T ∈ (Set.univ : Set ℝ))
  (h3 : k > 0)
  (h4 : T > 0)
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f (x + T)) = (k * (f x))))))
  (h6 : a = (Real.rpow k (1 /. T)))
  (h7 : a > 0)
  (h8 : (Real.rpow a T) = k)
  (h9 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f (x + T)) = ((Real.rpow a T) * (f x))))))
  (h10 : v_uCF_u86 = (fun (x : ℝ) => ((Real.rpow a (-x)) * (f x))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((v_uCF_u86 (x + T)) = ((Real.rpow a (-(x + T))) * (f (x + T)))))) := by
  sorry

theorem proof_gap_exercise_236_5
  (f : (ℝ -> ℝ))
  (k : ℝ)
  (T : ℝ)
  (h1 : k ∈ (Set.univ : Set ℝ))
  (h2 : T ∈ (Set.univ : Set ℝ))
  (h3 : k > 0)
  (h4 : T > 0)
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f (x + T)) = (k * (f x))))))
  (h6 : a = (Real.rpow k (1 /. T)))
  (h7 : a > 0)
  (h8 : (Real.rpow a T) = k)
  (h9 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f (x + T)) = ((Real.rpow a T) * (f x))))))
  (h10 : v_uCF_u86 = (fun (x : ℝ) => ((Real.rpow a (-x)) * (f x))))
  (h11 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((v_uCF_u86 (x + T)) = ((Real.rpow a (-(x + T))) * (f (x + T)))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((v_uCF_u86 (x + T)) = ((((Real.rpow a (-x)) * (Real.rpow a (-T))) * (Real.rpow a T)) * (f x))))) := by
  sorry

theorem proof_gap_exercise_236_6
  (f : (ℝ -> ℝ))
  (k : ℝ)
  (T : ℝ)
  (h1 : k ∈ (Set.univ : Set ℝ))
  (h2 : T ∈ (Set.univ : Set ℝ))
  (h3 : k > 0)
  (h4 : T > 0)
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f (x + T)) = (k * (f x))))))
  (h6 : a = (Real.rpow k (1 /. T)))
  (h7 : a > 0)
  (h8 : (Real.rpow a T) = k)
  (h9 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f (x + T)) = ((Real.rpow a T) * (f x))))))
  (h10 : v_uCF_u86 = (fun (x : ℝ) => ((Real.rpow a (-x)) * (f x))))
  (h11 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((v_uCF_u86 (x + T)) = ((Real.rpow a (-(x + T))) * (f (x + T)))))))
  (h12 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((v_uCF_u86 (x + T)) = ((((Real.rpow a (-x)) * (Real.rpow a (-T))) * (Real.rpow a T)) * (f x))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((v_uCF_u86 (x + T)) = ((Real.rpow a (-x)) * (f x))))) := by
  sorry

theorem proof_gap_exercise_236_7
  (f : (ℝ -> ℝ))
  (k : ℝ)
  (T : ℝ)
  (h1 : k ∈ (Set.univ : Set ℝ))
  (h2 : T ∈ (Set.univ : Set ℝ))
  (h3 : k > 0)
  (h4 : T > 0)
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f (x + T)) = (k * (f x))))))
  (h6 : a = (Real.rpow k (1 /. T)))
  (h7 : a > 0)
  (h8 : (Real.rpow a T) = k)
  (h9 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f (x + T)) = ((Real.rpow a T) * (f x))))))
  (h10 : v_uCF_u86 = (fun (x : ℝ) => ((Real.rpow a (-x)) * (f x))))
  (h11 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((v_uCF_u86 (x + T)) = ((Real.rpow a (-(x + T))) * (f (x + T)))))))
  (h12 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((v_uCF_u86 (x + T)) = ((((Real.rpow a (-x)) * (Real.rpow a (-T))) * (Real.rpow a T)) * (f x))))))
  (h13 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((v_uCF_u86 (x + T)) = ((Real.rpow a (-x)) * (f x))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((v_uCF_u86 (x + T)) = (v_uCF_u86 x)))) := by
  sorry

theorem proof_gap_exercise_236_8
  (f : (ℝ -> ℝ))
  (k : ℝ)
  (T : ℝ)
  (h1 : k ∈ (Set.univ : Set ℝ))
  (h2 : T ∈ (Set.univ : Set ℝ))
  (h3 : k > 0)
  (h4 : T > 0)
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f (x + T)) = (k * (f x))))))
  (h6 : a = (Real.rpow k (1 /. T)))
  (h7 : a > 0)
  (h8 : (Real.rpow a T) = k)
  (h9 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f (x + T)) = ((Real.rpow a T) * (f x))))))
  (h10 : v_uCF_u86 = (fun (x : ℝ) => ((Real.rpow a (-x)) * (f x))))
  (h11 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((v_uCF_u86 (x + T)) = ((Real.rpow a (-(x + T))) * (f (x + T)))))))
  (h12 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((v_uCF_u86 (x + T)) = ((((Real.rpow a (-x)) * (Real.rpow a (-T))) * (Real.rpow a T)) * (f x))))))
  (h13 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((v_uCF_u86 (x + T)) = ((Real.rpow a (-x)) * (f x))))))
  (h14 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((v_uCF_u86 (x + T)) = (v_uCF_u86 x)))))
  : Function.Periodic v_uCF_u86 T := by
  sorry

theorem proof_gap_exercise_236_9
  (f : (ℝ -> ℝ))
  (k : ℝ)
  (T : ℝ)
  (h1 : k ∈ (Set.univ : Set ℝ))
  (h2 : T ∈ (Set.univ : Set ℝ))
  (h3 : k > 0)
  (h4 : T > 0)
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f (x + T)) = (k * (f x))))))
  (h6 : a = (Real.rpow k (1 /. T)))
  (h7 : a > 0)
  (h8 : (Real.rpow a T) = k)
  (h9 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f (x + T)) = ((Real.rpow a T) * (f x))))))
  (h10 : v_uCF_u86 = (fun (x : ℝ) => ((Real.rpow a (-x)) * (f x))))
  (h11 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((v_uCF_u86 (x + T)) = ((Real.rpow a (-(x + T))) * (f (x + T)))))))
  (h12 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((v_uCF_u86 (x + T)) = ((((Real.rpow a (-x)) * (Real.rpow a (-T))) * (Real.rpow a T)) * (f x))))))
  (h13 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((v_uCF_u86 (x + T)) = ((Real.rpow a (-x)) * (f x))))))
  (h14 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((v_uCF_u86 (x + T)) = (v_uCF_u86 x)))))
  (h15 : Function.Periodic v_uCF_u86 T)
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = ((Real.rpow a x) * (v_uCF_u86 x))))) := by
  sorry

theorem proof_gap_exercise_236_10
  (f : (ℝ -> ℝ))
  (k : ℝ)
  (T : ℝ)
  (h1 : k ∈ (Set.univ : Set ℝ))
  (h2 : T ∈ (Set.univ : Set ℝ))
  (h3 : k > 0)
  (h4 : T > 0)
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f (x + T)) = (k * (f x))))))
  (h6 : a = (Real.rpow k (1 /. T)))
  (h7 : a > 0)
  (h8 : (Real.rpow a T) = k)
  (h9 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f (x + T)) = ((Real.rpow a T) * (f x))))))
  (h10 : v_uCF_u86 = (fun (x : ℝ) => ((Real.rpow a (-x)) * (f x))))
  (h11 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((v_uCF_u86 (x + T)) = ((Real.rpow a (-(x + T))) * (f (x + T)))))))
  (h12 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((v_uCF_u86 (x + T)) = ((((Real.rpow a (-x)) * (Real.rpow a (-T))) * (Real.rpow a T)) * (f x))))))
  (h13 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((v_uCF_u86 (x + T)) = ((Real.rpow a (-x)) * (f x))))))
  (h14 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((v_uCF_u86 (x + T)) = (v_uCF_u86 x)))))
  (h15 : Function.Periodic v_uCF_u86 T)
  (h16 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = ((Real.rpow a x) * (v_uCF_u86 x))))))
  : (exists (v_uCF_u86 : (ℝ -> ℝ)) (a : ℝ), ((((a ∈ (Set.univ : Set ℝ)) ∧ (a > 0)) ∧ (Function.Periodic v_uCF_u86 T)) ∧ (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = ((Real.rpow a x) * (v_uCF_u86 x))))))) := by
  sorry

theorem proof_gap_exercise_236_11
  (f : (ℝ -> ℝ))
  (k : ℝ)
  (T : ℝ)
  (h1 : k ∈ (Set.univ : Set ℝ))
  (h2 : T ∈ (Set.univ : Set ℝ))
  (h3 : k > 0)
  (h4 : T > 0)
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f (x + T)) = (k * (f x))))))
  (h6 : a = (Real.rpow k (1 /. T)))
  (h7 : a > 0)
  (h8 : (Real.rpow a T) = k)
  (h9 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f (x + T)) = ((Real.rpow a T) * (f x))))))
  (h10 : v_uCF_u86 = (fun (x : ℝ) => ((Real.rpow a (-x)) * (f x))))
  (h11 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((v_uCF_u86 (x + T)) = ((Real.rpow a (-(x + T))) * (f (x + T)))))))
  (h12 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((v_uCF_u86 (x + T)) = ((((Real.rpow a (-x)) * (Real.rpow a (-T))) * (Real.rpow a T)) * (f x))))))
  (h13 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((v_uCF_u86 (x + T)) = ((Real.rpow a (-x)) * (f x))))))
  (h14 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((v_uCF_u86 (x + T)) = (v_uCF_u86 x)))))
  (h15 : Function.Periodic v_uCF_u86 T)
  (h16 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = ((Real.rpow a x) * (v_uCF_u86 x))))))
  (h17 : (exists (v_uCF_u86 : (ℝ -> ℝ)) (a : ℝ), ((((a ∈ (Set.univ : Set ℝ)) ∧ (a > 0)) ∧ (Function.Periodic v_uCF_u86 T)) ∧ (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = ((Real.rpow a x) * (v_uCF_u86 x))))))))
  : (exists (v_uCF_u86 : (ℝ -> ℝ)) (a : ℝ), ((((a ∈ (Set.univ : Set ℝ)) ∧ (a > 0)) ∧ (Function.Periodic v_uCF_u86 T)) ∧ (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = ((Real.rpow a x) * (v_uCF_u86 x))))))) := by
  sorry
