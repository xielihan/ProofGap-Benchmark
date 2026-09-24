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

-- exercise: exercise_2186

theorem proof_gap_exercise_2186_1
  (f : (ℝ -> ℝ))
  (S : (ℕ -> ℝ))
  (a : ℝ)
  (n : ℕ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : (n ∈ (Set.univ : Set ℕ)) ∧ (n > 0))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc 0 1))) → ((f x) = (Real.rpow a x)))))
  (h4 : (a ≠ 1) → (h = (1 /. n)))
  : (a ≠ 1) → (exists (v_uCE_uBE : (ℕ -> ℝ)), (forall (i : ℕ), (((i ∈ (Set.univ : Set ℕ)) ∧ (i ≤ (n - 1))) → ((v_uCE_uBE i) = (i * h))))) := by
  sorry

theorem proof_gap_exercise_2186_2
  (f : (ℝ -> ℝ))
  (S : (ℕ -> ℝ))
  (a : ℝ)
  (n : ℕ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : (n ∈ (Set.univ : Set ℕ)) ∧ (n > 0))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc 0 1))) → ((f x) = (Real.rpow a x)))))
  (h4 : (a ≠ 1) → (h = (1 /. n)))
  (h5 : (a ≠ 1) → (exists (v_uCE_uBE : (ℕ -> ℝ)), (forall (i : ℕ), (((i ∈ (Set.univ : Set ℕ)) ∧ (i ≤ (n - 1))) → ((v_uCE_uBE i) = (i * h))))))
  : (a ≠ 1) → ((S n) = (∑ i ∈ Finset.Icc (0 : ℕ) (n - 1), (h * (Real.rpow a (i * h))))) := by
  sorry

theorem proof_gap_exercise_2186_3
  (f : (ℝ -> ℝ))
  (S : (ℕ -> ℝ))
  (a : ℝ)
  (n : ℕ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : (n ∈ (Set.univ : Set ℕ)) ∧ (n > 0))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc 0 1))) → ((f x) = (Real.rpow a x)))))
  (h4 : (a ≠ 1) → (h = (1 /. n)))
  (h5 : (a ≠ 1) → (exists (v_uCE_uBE : (ℕ -> ℝ)), (forall (i : ℕ), (((i ∈ (Set.univ : Set ℕ)) ∧ (i ≤ (n - 1))) → ((v_uCE_uBE i) = (i * h))))))
  (h6 : (a ≠ 1) → ((S n) = (∑ i ∈ Finset.Icc (0 : ℕ) (n - 1), (h * (Real.rpow a (i * h))))))
  : (a ≠ 1) → ((S n) = ((h * (a - 1)) /. ((Real.rpow a h) - 1))) := by
  sorry

theorem proof_gap_exercise_2186_4
  (f : (ℝ -> ℝ))
  (S : (ℕ -> ℝ))
  (a : ℝ)
  (n : ℕ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : (n ∈ (Set.univ : Set ℕ)) ∧ (n > 0))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc 0 1))) → ((f x) = (Real.rpow a x)))))
  (h4 : (a ≠ 1) → (h = (1 /. n)))
  (h5 : (a ≠ 1) → (exists (v_uCE_uBE : (ℕ -> ℝ)), (forall (i : ℕ), (((i ∈ (Set.univ : Set ℕ)) ∧ (i ≤ (n - 1))) → ((v_uCE_uBE i) = (i * h))))))
  (h6 : (a ≠ 1) → ((S n) = (∑ i ∈ Finset.Icc (0 : ℕ) (n - 1), (h * (Real.rpow a (i * h))))))
  (h7 : (a ≠ 1) → ((S n) = ((h * (a - 1)) /. ((Real.rpow a h) - 1))))
  : (a ≠ 1) → ((S n) = ((a - 1) /. (n * ((Real.rpow a (1 /. n)) - 1)))) := by
  sorry

theorem proof_gap_exercise_2186_5
  (f : (ℝ -> ℝ))
  (S : (ℕ -> ℝ))
  (a : ℝ)
  (n : ℕ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : (n ∈ (Set.univ : Set ℕ)) ∧ (n > 0))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc 0 1))) → ((f x) = (Real.rpow a x)))))
  (h4 : (a ≠ 1) → (h = (1 /. n)))
  (h5 : (a ≠ 1) → (exists (v_uCE_uBE : (ℕ -> ℝ)), (forall (i : ℕ), (((i ∈ (Set.univ : Set ℕ)) ∧ (i ≤ (n - 1))) → ((v_uCE_uBE i) = (i * h))))))
  (h6 : (a ≠ 1) → ((S n) = (∑ i ∈ Finset.Icc (0 : ℕ) (n - 1), (h * (Real.rpow a (i * h))))))
  (h7 : (a ≠ 1) → ((S n) = ((h * (a - 1)) /. ((Real.rpow a h) - 1))))
  (h8 : (a ≠ 1) → ((S n) = ((a - 1) /. (n * ((Real.rpow a (1 /. n)) - 1)))))
  : (a ≠ 1) → (∃ L : ℝ, Tendsto (fun n_1 : ℕ => ((a - 1) /. (((Real.rpow a (1 /. n_1)) - 1) /. (1 /. n_1)))) atTop (𝓝 L) ∧ (Tendsto (fun n_1 : ℕ => (S n_1)) atTop (𝓝 (atTop.limUnder (fun n_1 : ℕ => ((a - 1) /. (((Real.rpow a (1 /. n_1)) - 1) /. (1 /. n_1)))))))) := by
  sorry

theorem proof_gap_exercise_2186_6
  (f : (ℝ -> ℝ))
  (S : (ℕ -> ℝ))
  (a : ℝ)
  (n : ℕ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : (n ∈ (Set.univ : Set ℕ)) ∧ (n > 0))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc 0 1))) → ((f x) = (Real.rpow a x)))))
  (h4 : (a ≠ 1) → (h = (1 /. n)))
  (h5 : (a ≠ 1) → (exists (v_uCE_uBE : (ℕ -> ℝ)), (forall (i : ℕ), (((i ∈ (Set.univ : Set ℕ)) ∧ (i ≤ (n - 1))) → ((v_uCE_uBE i) = (i * h))))))
  (h6 : (a ≠ 1) → ((S n) = (∑ i ∈ Finset.Icc (0 : ℕ) (n - 1), (h * (Real.rpow a (i * h))))))
  (h7 : (a ≠ 1) → ((S n) = ((h * (a - 1)) /. ((Real.rpow a h) - 1))))
  (h8 : (a ≠ 1) → ((S n) = ((a - 1) /. (n * ((Real.rpow a (1 /. n)) - 1)))))
  (h9 : (a ≠ 1) → (Tendsto (fun n_1 : ℕ => (S n_1)) atTop (𝓝 (atTop.limUnder (fun n_1 : ℕ => ((a - 1) /. (((Real.rpow a (1 /. n_1)) - 1) /. (1 /. n_1))))))))
  (h10 : ∃ L : ℝ, Tendsto (fun n_1 : ℕ => ((a - 1) /. (((Real.rpow a (1 /. n_1)) - 1) /. (1 /. n_1)))) atTop (𝓝 L))
  : (a ≠ 1) → (Tendsto (fun n_1 : ℕ => (S n_1)) atTop (𝓝 ((a - 1) /. (Real.log a)))) := by
  sorry

theorem proof_gap_exercise_2186_7
  (f : (ℝ -> ℝ))
  (S : (ℕ -> ℝ))
  (a : ℝ)
  (n : ℕ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : (n ∈ (Set.univ : Set ℕ)) ∧ (n > 0))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc 0 1))) → ((f x) = (Real.rpow a x)))))
  (h4 : (a ≠ 1) → (h = (1 /. n)))
  (h5 : (a ≠ 1) → (exists (v_uCE_uBE : (ℕ -> ℝ)), (forall (i : ℕ), (((i ∈ (Set.univ : Set ℕ)) ∧ (i ≤ (n - 1))) → ((v_uCE_uBE i) = (i * h))))))
  (h6 : (a ≠ 1) → ((S n) = (∑ i ∈ Finset.Icc (0 : ℕ) (n - 1), (h * (Real.rpow a (i * h))))))
  (h7 : (a ≠ 1) → ((S n) = ((h * (a - 1)) /. ((Real.rpow a h) - 1))))
  (h8 : (a ≠ 1) → ((S n) = ((a - 1) /. (n * ((Real.rpow a (1 /. n)) - 1)))))
  (h9 : (a ≠ 1) → (Tendsto (fun n_1 : ℕ => (S n_1)) atTop (𝓝 (atTop.limUnder (fun n_1 : ℕ => ((a - 1) /. (((Real.rpow a (1 /. n_1)) - 1) /. (1 /. n_1))))))))
  (h10 : (a ≠ 1) → (Tendsto (fun n_1 : ℕ => (S n_1)) atTop (𝓝 ((a - 1) /. (Real.log a)))))
  (h11 : ∃ L : ℝ, Tendsto (fun n_1 : ℕ => ((a - 1) /. (((Real.rpow a (1 /. n_1)) - 1) /. (1 /. n_1)))) atTop (𝓝 L))
  : (a ≠ 1) → ((∫ x in (0 : ℝ)..(1 : ℝ), ((Real.rpow a x) * (1 : ℝ))) = ((a - 1) /. (Real.log a))) := by
  sorry

theorem proof_gap_exercise_2186_8
  (f : (ℝ -> ℝ))
  (S : (ℕ -> ℝ))
  (a : ℝ)
  (n : ℕ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : (n ∈ (Set.univ : Set ℕ)) ∧ (n > 0))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc 0 1))) → ((f x) = (Real.rpow a x)))))
  (h4 : (a ≠ 1) → (h = (1 /. n)))
  (h5 : (a ≠ 1) → (exists (v_uCE_uBE : (ℕ -> ℝ)), (forall (i : ℕ), (((i ∈ (Set.univ : Set ℕ)) ∧ (i ≤ (n - 1))) → ((v_uCE_uBE i) = (i * h))))))
  (h6 : (a ≠ 1) → ((S n) = (∑ i ∈ Finset.Icc (0 : ℕ) (n - 1), (h * (Real.rpow a (i * h))))))
  (h7 : (a ≠ 1) → ((S n) = ((h * (a - 1)) /. ((Real.rpow a h) - 1))))
  (h8 : (a ≠ 1) → ((S n) = ((a - 1) /. (n * ((Real.rpow a (1 /. n)) - 1)))))
  (h9 : (a ≠ 1) → (Tendsto (fun n_1 : ℕ => (S n_1)) atTop (𝓝 (atTop.limUnder (fun n_1 : ℕ => ((a - 1) /. (((Real.rpow a (1 /. n_1)) - 1) /. (1 /. n_1))))))))
  (h10 : (a ≠ 1) → (Tendsto (fun n_1 : ℕ => (S n_1)) atTop (𝓝 ((a - 1) /. (Real.log a)))))
  (h11 : (a ≠ 1) → ((∫ x in (0 : ℝ)..(1 : ℝ), ((Real.rpow a x) * (1 : ℝ))) = ((a - 1) /. (Real.log a))))
  (h12 : ∃ L : ℝ, Tendsto (fun n_1 : ℕ => ((a - 1) /. (((Real.rpow a (1 /. n_1)) - 1) /. (1 /. n_1)))) atTop (𝓝 L))
  : (a = 1) → ((∫ x in (0 : ℝ)..(1 : ℝ), ((Real.rpow a x) * (1 : ℝ))) = (∫ x in (0 : ℝ)..(1 : ℝ), ((1 : ℝ) * (1 : ℝ)))) := by
  sorry

theorem proof_gap_exercise_2186_9
  (f : (ℝ -> ℝ))
  (S : (ℕ -> ℝ))
  (a : ℝ)
  (n : ℕ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : (n ∈ (Set.univ : Set ℕ)) ∧ (n > 0))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc 0 1))) → ((f x) = (Real.rpow a x)))))
  (h4 : (a ≠ 1) → (h = (1 /. n)))
  (h5 : (a ≠ 1) → (exists (v_uCE_uBE : (ℕ -> ℝ)), (forall (i : ℕ), (((i ∈ (Set.univ : Set ℕ)) ∧ (i ≤ (n - 1))) → ((v_uCE_uBE i) = (i * h))))))
  (h6 : (a ≠ 1) → ((S n) = (∑ i ∈ Finset.Icc (0 : ℕ) (n - 1), (h * (Real.rpow a (i * h))))))
  (h7 : (a ≠ 1) → ((S n) = ((h * (a - 1)) /. ((Real.rpow a h) - 1))))
  (h8 : (a ≠ 1) → ((S n) = ((a - 1) /. (n * ((Real.rpow a (1 /. n)) - 1)))))
  (h9 : (a ≠ 1) → (Tendsto (fun n_1 : ℕ => (S n_1)) atTop (𝓝 (atTop.limUnder (fun n_1 : ℕ => ((a - 1) /. (((Real.rpow a (1 /. n_1)) - 1) /. (1 /. n_1))))))))
  (h10 : (a ≠ 1) → (Tendsto (fun n_1 : ℕ => (S n_1)) atTop (𝓝 ((a - 1) /. (Real.log a)))))
  (h11 : (a ≠ 1) → ((∫ x in (0 : ℝ)..(1 : ℝ), ((Real.rpow a x) * (1 : ℝ))) = ((a - 1) /. (Real.log a))))
  (h12 : (a = 1) → ((∫ x in (0 : ℝ)..(1 : ℝ), ((Real.rpow a x) * (1 : ℝ))) = (∫ x in (0 : ℝ)..(1 : ℝ), ((1 : ℝ) * (1 : ℝ)))))
  (h13 : ∃ L : ℝ, Tendsto (fun n_1 : ℕ => ((a - 1) /. (((Real.rpow a (1 /. n_1)) - 1) /. (1 /. n_1)))) atTop (𝓝 L))
  : (a = 1) → ((∫ x in (0 : ℝ)..(1 : ℝ), ((Real.rpow a x) * (1 : ℝ))) = 1) := by
  sorry

theorem proof_gap_exercise_2186_10
  (f : (ℝ -> ℝ))
  (S : (ℕ -> ℝ))
  (a : ℝ)
  (n : ℕ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : (n ∈ (Set.univ : Set ℕ)) ∧ (n > 0))
  (h3 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ (Set.Icc 0 1))) → ((f x) = (Real.rpow a x)))))
  (h4 : (a ≠ 1) → (h = (1 /. n)))
  (h5 : (a ≠ 1) → (exists (v_uCE_uBE : (ℕ -> ℝ)), (forall (i : ℕ), (((i ∈ (Set.univ : Set ℕ)) ∧ (i ≤ (n - 1))) → ((v_uCE_uBE i) = (i * h))))))
  (h6 : (a ≠ 1) → ((S n) = (∑ i ∈ Finset.Icc (0 : ℕ) (n - 1), (h * (Real.rpow a (i * h))))))
  (h7 : (a ≠ 1) → ((S n) = ((h * (a - 1)) /. ((Real.rpow a h) - 1))))
  (h8 : (a ≠ 1) → ((S n) = ((a - 1) /. (n * ((Real.rpow a (1 /. n)) - 1)))))
  (h9 : (a ≠ 1) → (Tendsto (fun n_1 : ℕ => (S n_1)) atTop (𝓝 (atTop.limUnder (fun n_1 : ℕ => ((a - 1) /. (((Real.rpow a (1 /. n_1)) - 1) /. (1 /. n_1))))))))
  (h10 : (a ≠ 1) → (Tendsto (fun n_1 : ℕ => (S n_1)) atTop (𝓝 ((a - 1) /. (Real.log a)))))
  (h11 : (a ≠ 1) → ((∫ x in (0 : ℝ)..(1 : ℝ), ((Real.rpow a x) * (1 : ℝ))) = ((a - 1) /. (Real.log a))))
  (h12 : (a = 1) → ((∫ x in (0 : ℝ)..(1 : ℝ), ((Real.rpow a x) * (1 : ℝ))) = (∫ x in (0 : ℝ)..(1 : ℝ), ((1 : ℝ) * (1 : ℝ)))))
  (h13 : (a = 1) → ((∫ x in (0 : ℝ)..(1 : ℝ), ((Real.rpow a x) * (1 : ℝ))) = 1))
  (h14 : ∃ L : ℝ, Tendsto (fun n_1 : ℕ => ((a - 1) /. (((Real.rpow a (1 /. n_1)) - 1) /. (1 /. n_1)))) atTop (𝓝 L))
  : (∫ x in (0 : ℝ)..(1 : ℝ), ((Real.rpow a x) * (1 : ℝ))) = (if (a ≠ 1) then ((a - 1) /. (Real.log a)) else (if (a = 1) then 1 else 1)) := by
  sorry
