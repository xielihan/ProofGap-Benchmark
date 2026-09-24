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

-- exercise: exercise_221_4

theorem proof_gap_exercise_221_4_1
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (c : ℝ)
  (d : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : c ∈ (Set.univ : Set ℝ))
  (h4 : d ∈ (Set.univ : Set ℝ))
  (h5 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (((c * x) + d) ≠ 0)) → ((f x) = (((a * x) + b) /. ((c * x) + d))))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (((c * x) + d) ≠ 0)) → ((f x) = ((a /. c) + ((b - (a * (d /. c))) /. ((c * x) + d)))))) := by
  sorry

theorem proof_gap_exercise_221_4_2
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (c : ℝ)
  (d : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : c ∈ (Set.univ : Set ℝ))
  (h4 : d ∈ (Set.univ : Set ℝ))
  (h5 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (((c * x) + d) ≠ 0)) → ((f x) = (((a * x) + b) /. ((c * x) + d))))))
  (h6 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (((c * x) + d) ≠ 0)) → ((f x) = ((a /. c) + ((b - (a * (d /. c))) /. ((c * x) + d)))))))
  : (c = 0) → ((d ≠ 0) → (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (((a /. d) * x) + (b /. d)))))) := by
  sorry

theorem proof_gap_exercise_221_4_3
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (c : ℝ)
  (d : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : c ∈ (Set.univ : Set ℝ))
  (h4 : d ∈ (Set.univ : Set ℝ))
  (h5 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (((c * x) + d) ≠ 0)) → ((f x) = (((a * x) + b) /. ((c * x) + d))))))
  (h6 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (((c * x) + d) ≠ 0)) → ((f x) = ((a /. c) + ((b - (a * (d /. c))) /. ((c * x) + d)))))))
  (h7 : (c = 0) → ((d ≠ 0) → (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (((a /. d) * x) + (b /. d)))))))
  : (c = 0) → ((d ≠ 0) → (((a /. d) > 0) → (StrictMonoOn f (Set.univ : Set ℝ)))) := by
  sorry

theorem proof_gap_exercise_221_4_4
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (c : ℝ)
  (d : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : c ∈ (Set.univ : Set ℝ))
  (h4 : d ∈ (Set.univ : Set ℝ))
  (h5 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (((c * x) + d) ≠ 0)) → ((f x) = (((a * x) + b) /. ((c * x) + d))))))
  (h6 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (((c * x) + d) ≠ 0)) → ((f x) = ((a /. c) + ((b - (a * (d /. c))) /. ((c * x) + d)))))))
  (h7 : (c = 0) → ((d ≠ 0) → (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (((a /. d) * x) + (b /. d)))))))
  (h8 : (c = 0) → ((d ≠ 0) → (((a /. d) > 0) → (StrictMonoOn f (Set.univ : Set ℝ)))))
  : (c = 0) → ((d ≠ 0) → (((a /. d) < 0) → (StrictAntiOn f (Set.univ : Set ℝ)))) := by
  sorry

theorem proof_gap_exercise_221_4_5
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (c : ℝ)
  (d : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : c ∈ (Set.univ : Set ℝ))
  (h4 : d ∈ (Set.univ : Set ℝ))
  (h5 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (((c * x) + d) ≠ 0)) → ((f x) = (((a * x) + b) /. ((c * x) + d))))))
  (h6 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (((c * x) + d) ≠ 0)) → ((f x) = ((a /. c) + ((b - (a * (d /. c))) /. ((c * x) + d)))))))
  (h7 : (c = 0) → ((d ≠ 0) → (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (((a /. d) * x) + (b /. d)))))))
  (h8 : (c = 0) → ((d ≠ 0) → (((a /. d) > 0) → (StrictMonoOn f (Set.univ : Set ℝ)))))
  (h9 : (c = 0) → ((d ≠ 0) → (((a /. d) < 0) → (StrictAntiOn f (Set.univ : Set ℝ)))))
  : (c > 0) → ((b > (a * (d /. c))) → (StrictAntiOn f (Set.Iio (-(d /. c))))) := by
  sorry

theorem proof_gap_exercise_221_4_6
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (c : ℝ)
  (d : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : c ∈ (Set.univ : Set ℝ))
  (h4 : d ∈ (Set.univ : Set ℝ))
  (h5 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (((c * x) + d) ≠ 0)) → ((f x) = (((a * x) + b) /. ((c * x) + d))))))
  (h6 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (((c * x) + d) ≠ 0)) → ((f x) = ((a /. c) + ((b - (a * (d /. c))) /. ((c * x) + d)))))))
  (h7 : (c = 0) → ((d ≠ 0) → (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (((a /. d) * x) + (b /. d)))))))
  (h8 : (c = 0) → ((d ≠ 0) → (((a /. d) > 0) → (StrictMonoOn f (Set.univ : Set ℝ)))))
  (h9 : (c = 0) → ((d ≠ 0) → (((a /. d) < 0) → (StrictAntiOn f (Set.univ : Set ℝ)))))
  (h10 : (c > 0) → ((b > (a * (d /. c))) → (StrictAntiOn f (Set.Iio (-(d /. c))))))
  (h11 : c ≠ 0)
  : (c > 0) → ((b > (a * (d /. c))) → (StrictAntiOn f (Set.Ioi (-(d /. c))))) := by
  sorry

theorem proof_gap_exercise_221_4_7
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (c : ℝ)
  (d : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : c ∈ (Set.univ : Set ℝ))
  (h4 : d ∈ (Set.univ : Set ℝ))
  (h5 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (((c * x) + d) ≠ 0)) → ((f x) = (((a * x) + b) /. ((c * x) + d))))))
  (h6 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (((c * x) + d) ≠ 0)) → ((f x) = ((a /. c) + ((b - (a * (d /. c))) /. ((c * x) + d)))))))
  (h7 : (c = 0) → ((d ≠ 0) → (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (((a /. d) * x) + (b /. d)))))))
  (h8 : (c = 0) → ((d ≠ 0) → (((a /. d) > 0) → (StrictMonoOn f (Set.univ : Set ℝ)))))
  (h9 : (c = 0) → ((d ≠ 0) → (((a /. d) < 0) → (StrictAntiOn f (Set.univ : Set ℝ)))))
  (h10 : (c > 0) → ((b > (a * (d /. c))) → (StrictAntiOn f (Set.Iio (-(d /. c))))))
  (h11 : (c > 0) → ((b > (a * (d /. c))) → (StrictAntiOn f (Set.Ioi (-(d /. c))))))
  (h12 : c ≠ 0)
  : (c > 0) → ((b < ((a * d) /. c)) → (StrictMonoOn f (Set.Iio (-(d /. c))))) := by
  sorry

theorem proof_gap_exercise_221_4_8
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (c : ℝ)
  (d : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : c ∈ (Set.univ : Set ℝ))
  (h4 : d ∈ (Set.univ : Set ℝ))
  (h5 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (((c * x) + d) ≠ 0)) → ((f x) = (((a * x) + b) /. ((c * x) + d))))))
  (h6 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (((c * x) + d) ≠ 0)) → ((f x) = ((a /. c) + ((b - (a * (d /. c))) /. ((c * x) + d)))))))
  (h7 : (c = 0) → ((d ≠ 0) → (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (((a /. d) * x) + (b /. d)))))))
  (h8 : (c = 0) → ((d ≠ 0) → (((a /. d) > 0) → (StrictMonoOn f (Set.univ : Set ℝ)))))
  (h9 : (c = 0) → ((d ≠ 0) → (((a /. d) < 0) → (StrictAntiOn f (Set.univ : Set ℝ)))))
  (h10 : (c > 0) → ((b > (a * (d /. c))) → (StrictAntiOn f (Set.Iio (-(d /. c))))))
  (h11 : (c > 0) → ((b > (a * (d /. c))) → (StrictAntiOn f (Set.Ioi (-(d /. c))))))
  (h12 : (c > 0) → ((b < ((a * d) /. c)) → (StrictMonoOn f (Set.Iio (-(d /. c))))))
  (h13 : c ≠ 0)
  : (c > 0) → ((b < ((a * d) /. c)) → (StrictMonoOn f (Set.Ioi (-(d /. c))))) := by
  sorry

theorem proof_gap_exercise_221_4_9
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (c : ℝ)
  (d : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : c ∈ (Set.univ : Set ℝ))
  (h4 : d ∈ (Set.univ : Set ℝ))
  (h5 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (((c * x) + d) ≠ 0)) → ((f x) = (((a * x) + b) /. ((c * x) + d))))))
  (h6 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (((c * x) + d) ≠ 0)) → ((f x) = ((a /. c) + ((b - (a * (d /. c))) /. ((c * x) + d)))))))
  (h7 : (c = 0) → ((d ≠ 0) → (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (((a /. d) * x) + (b /. d)))))))
  (h8 : (c = 0) → ((d ≠ 0) → (((a /. d) > 0) → (StrictMonoOn f (Set.univ : Set ℝ)))))
  (h9 : (c = 0) → ((d ≠ 0) → (((a /. d) < 0) → (StrictAntiOn f (Set.univ : Set ℝ)))))
  (h10 : (c > 0) → ((b > (a * (d /. c))) → (StrictAntiOn f (Set.Iio (-(d /. c))))))
  (h11 : (c > 0) → ((b > (a * (d /. c))) → (StrictAntiOn f (Set.Ioi (-(d /. c))))))
  (h12 : (c > 0) → ((b < ((a * d) /. c)) → (StrictMonoOn f (Set.Iio (-(d /. c))))))
  (h13 : (c > 0) → ((b < ((a * d) /. c)) → (StrictMonoOn f (Set.Ioi (-(d /. c))))))
  : ((c = 0) ∧ (d ≠ 0)) → ((((a /. d) > 0) → (StrictMonoOn f (Set.univ : Set ℝ))) ∧ (((a /. d) < 0) → (StrictAntiOn f (Set.univ : Set ℝ)))) := by
  sorry

theorem proof_gap_exercise_221_4_10
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (c : ℝ)
  (d : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : c ∈ (Set.univ : Set ℝ))
  (h4 : d ∈ (Set.univ : Set ℝ))
  (h5 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (((c * x) + d) ≠ 0)) → ((f x) = (((a * x) + b) /. ((c * x) + d))))))
  (h6 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (((c * x) + d) ≠ 0)) → ((f x) = ((a /. c) + ((b - (a * (d /. c))) /. ((c * x) + d)))))))
  (h7 : (c = 0) → ((d ≠ 0) → (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (((a /. d) * x) + (b /. d)))))))
  (h8 : (c = 0) → ((d ≠ 0) → (((a /. d) > 0) → (StrictMonoOn f (Set.univ : Set ℝ)))))
  (h9 : (c = 0) → ((d ≠ 0) → (((a /. d) < 0) → (StrictAntiOn f (Set.univ : Set ℝ)))))
  (h10 : (c > 0) → ((b > (a * (d /. c))) → (StrictAntiOn f (Set.Iio (-(d /. c))))))
  (h11 : (c > 0) → ((b > (a * (d /. c))) → (StrictAntiOn f (Set.Ioi (-(d /. c))))))
  (h12 : (c > 0) → ((b < ((a * d) /. c)) → (StrictMonoOn f (Set.Iio (-(d /. c))))))
  (h13 : (c > 0) → ((b < ((a * d) /. c)) → (StrictMonoOn f (Set.Ioi (-(d /. c))))))
  (h14 : ((c = 0) ∧ (d ≠ 0)) → ((((a /. d) > 0) → (StrictMonoOn f (Set.univ : Set ℝ))) ∧ (((a /. d) < 0) → (StrictAntiOn f (Set.univ : Set ℝ)))))
  : (c > 0) → (((b > (a * (d /. c))) → ((StrictAntiOn f (Set.Iio (-(d /. c)))) ∧ (StrictAntiOn f (Set.Ioi (-(d /. c)))))) ∧ ((b < ((a * d) /. c)) → ((StrictMonoOn f (Set.Iio (-(d /. c)))) ∧ (StrictMonoOn f (Set.Ioi (-(d /. c))))))) := by
  sorry

theorem proof_gap_exercise_221_4_11
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (b : ℝ)
  (c : ℝ)
  (d : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : c ∈ (Set.univ : Set ℝ))
  (h4 : d ∈ (Set.univ : Set ℝ))
  (h5 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (((c * x) + d) ≠ 0)) → ((f x) = (((a * x) + b) /. ((c * x) + d))))))
  (h6 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (((c * x) + d) ≠ 0)) → ((f x) = ((a /. c) + ((b - (a * (d /. c))) /. ((c * x) + d)))))))
  (h7 : (c = 0) → ((d ≠ 0) → (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (((a /. d) * x) + (b /. d)))))))
  (h8 : (c = 0) → ((d ≠ 0) → (((a /. d) > 0) → (StrictMonoOn f (Set.univ : Set ℝ)))))
  (h9 : (c = 0) → ((d ≠ 0) → (((a /. d) < 0) → (StrictAntiOn f (Set.univ : Set ℝ)))))
  (h10 : (c > 0) → ((b > (a * (d /. c))) → (StrictAntiOn f (Set.Iio (-(d /. c))))))
  (h11 : (c > 0) → ((b > (a * (d /. c))) → (StrictAntiOn f (Set.Ioi (-(d /. c))))))
  (h12 : (c > 0) → ((b < ((a * d) /. c)) → (StrictMonoOn f (Set.Iio (-(d /. c))))))
  (h13 : (c > 0) → ((b < ((a * d) /. c)) → (StrictMonoOn f (Set.Ioi (-(d /. c))))))
  (h14 : ((c = 0) ∧ (d ≠ 0)) → ((((a /. d) > 0) → (StrictMonoOn f (Set.univ : Set ℝ))) ∧ (((a /. d) < 0) → (StrictAntiOn f (Set.univ : Set ℝ)))))
  (h15 : (c > 0) → (((b > (a * (d /. c))) → ((StrictAntiOn f (Set.Iio (-(d /. c)))) ∧ (StrictAntiOn f (Set.Ioi (-(d /. c)))))) ∧ ((b < ((a * d) /. c)) → ((StrictMonoOn f (Set.Iio (-(d /. c)))) ∧ (StrictMonoOn f (Set.Ioi (-(d /. c))))))))
  : (((c = 0) ∧ (d ≠ 0)) → ((((a /. d) > 0) → (StrictMonoOn f (Set.univ : Set ℝ))) ∧ (((a /. d) < 0) → (StrictAntiOn f (Set.univ : Set ℝ))))) ∧ ((c > 0) → (((b > (a * (d /. c))) → ((StrictAntiOn f (Set.Iio (-(d /. c)))) ∧ (StrictAntiOn f (Set.Ioi (-(d /. c)))))) ∧ ((b < ((a * d) /. c)) → ((StrictMonoOn f (Set.Iio (-(d /. c)))) ∧ (StrictMonoOn f (Set.Ioi (-(d /. c)))))))) := by
  sorry
