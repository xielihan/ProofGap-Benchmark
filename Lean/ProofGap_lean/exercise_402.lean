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

-- exercise: exercise_402

theorem proof_gap_exercise_402_1
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (E : ℝ), (((((E ∈ (Set.univ : Set ℝ)) ∧ (E > 0)) ∧ (0 < |((x - 1))|)) ∧ (|((x - 1))| < (1 /. (Real.rpow E (((2 : ℝ))⁻¹))))) → ((1 /. (|((1 - x))| ^ (2 : ℕ))) > E))))) := by
  sorry

theorem proof_gap_exercise_402_2
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (E : ℝ), (((((E ∈ (Set.univ : Set ℝ)) ∧ (E > 0)) ∧ (0 < |((x - 1))|)) ∧ (|((x - 1))| < (1 /. (Real.rpow E (((2 : ℝ))⁻¹))))) → ((1 /. (|((1 - x))| ^ (2 : ℕ))) > E))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (E : ℝ), (((((E ∈ (Set.univ : Set ℝ)) ∧ (E > 0)) ∧ (0 < |((x - 1))|)) ∧ (|((x - 1))| < (1 /. E))) → ((0 < |((x - 1))|) ∧ (|((x - 1))| < (1 /. (Real.rpow E (((2 : ℝ))⁻¹))))))))) := by
  sorry

theorem proof_gap_exercise_402_3
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (E : ℝ), (((((E ∈ (Set.univ : Set ℝ)) ∧ (E > 0)) ∧ (0 < |((x - 1))|)) ∧ (|((x - 1))| < (1 /. (Real.rpow E (((2 : ℝ))⁻¹))))) → ((1 /. (|((1 - x))| ^ (2 : ℕ))) > E))))))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (E : ℝ), (((((E ∈ (Set.univ : Set ℝ)) ∧ (E > 0)) ∧ (0 < |((x - 1))|)) ∧ (|((x - 1))| < (1 /. E))) → ((0 < |((x - 1))|) ∧ (|((x - 1))| < (1 /. (Real.rpow E (((2 : ℝ))⁻¹))))))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (E : ℝ), (((((E ∈ (Set.univ : Set ℝ)) ∧ (E > 0)) ∧ (0 < |((x - 1))|)) ∧ (|((x - 1))| < (1 /. E))) → ((1 /. (|((1 - x))| ^ (2 : ℕ))) > E))))) := by
  sorry

theorem proof_gap_exercise_402_4
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (E : ℝ), (((((E ∈ (Set.univ : Set ℝ)) ∧ (E > 0)) ∧ (0 < |((x - 1))|)) ∧ (|((x - 1))| < (1 /. (Real.rpow E (((2 : ℝ))⁻¹))))) → ((1 /. (|((1 - x))| ^ (2 : ℕ))) > E))))))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (E : ℝ), (((((E ∈ (Set.univ : Set ℝ)) ∧ (E > 0)) ∧ (0 < |((x - 1))|)) ∧ (|((x - 1))| < (1 /. E))) → ((0 < |((x - 1))|) ∧ (|((x - 1))| < (1 /. (Real.rpow E (((2 : ℝ))⁻¹))))))))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (E : ℝ), (((((E ∈ (Set.univ : Set ℝ)) ∧ (E > 0)) ∧ (0 < |((x - 1))|)) ∧ (|((x - 1))| < (1 /. E))) → ((1 /. (|((1 - x))| ^ (2 : ℕ))) > E))))))
  (h4 : (forall (E : ℝ), (((E ∈ (Set.univ : Set ℝ)) ∧ (E > 0)) → (exists (v_uCE_uB4 : ℝ), ((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ ((v_uCE_uB4 > 0) → (v_uCE_uB4 = (min (1 : ℝ) (1 /. E)))))))))
  : (forall (E : ℝ), (((E ∈ (Set.univ : Set ℝ)) ∧ (E > 0)) → (exists (v_uCE_uB4 : ℝ), ((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ ((v_uCE_uB4 = (min (1 : ℝ) (1 /. E))) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < |((x - 1))|)) ∧ (|((x - 1))| < v_uCE_uB4)) → ((1 /. (|((1 - x))| ^ (2 : ℕ))) > E)))))))) := by
  sorry

theorem proof_gap_exercise_402_5
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (E : ℝ), (((((E ∈ (Set.univ : Set ℝ)) ∧ (E > 0)) ∧ (0 < |((x - 1))|)) ∧ (|((x - 1))| < (1 /. (Real.rpow E (((2 : ℝ))⁻¹))))) → ((1 /. (|((1 - x))| ^ (2 : ℕ))) > E))))))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (E : ℝ), (((((E ∈ (Set.univ : Set ℝ)) ∧ (E > 0)) ∧ (0 < |((x - 1))|)) ∧ (|((x - 1))| < (1 /. E))) → ((0 < |((x - 1))|) ∧ (|((x - 1))| < (1 /. (Real.rpow E (((2 : ℝ))⁻¹))))))))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (E : ℝ), (((((E ∈ (Set.univ : Set ℝ)) ∧ (E > 0)) ∧ (0 < |((x - 1))|)) ∧ (|((x - 1))| < (1 /. E))) → ((1 /. (|((1 - x))| ^ (2 : ℕ))) > E))))))
  (h4 : (forall (E : ℝ), (((E ∈ (Set.univ : Set ℝ)) ∧ (E > 0)) → (exists (v_uCE_uB4 : ℝ), ((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ ((v_uCE_uB4 > 0) → (v_uCE_uB4 = (min (1 : ℝ) (1 /. E)))))))))
  (h5 : (forall (E : ℝ), (((E ∈ (Set.univ : Set ℝ)) ∧ (E > 0)) → (exists (v_uCE_uB4 : ℝ), ((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ ((v_uCE_uB4 = (min (1 : ℝ) (1 /. E))) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < |((x - 1))|)) ∧ (|((x - 1))| < v_uCE_uB4)) → ((1 /. (|((1 - x))| ^ (2 : ℕ))) > E)))))))))
  : (forall (E : ℝ), (((E ∈ (Set.univ : Set ℝ)) ∧ (E > 0)) → (exists (v_uCE_uB4 : ℝ), ((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ ((v_uCE_uB4 = (min (1 : ℝ) (1 /. E))) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < |((x - 1))|)) ∧ (|((x - 1))| < v_uCE_uB4)) → (|((1 /. ((1 - x) ^ (2 : ℕ))))| > E)))))))) := by
  sorry

theorem proof_gap_exercise_402_6
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (E : ℝ), (((((E ∈ (Set.univ : Set ℝ)) ∧ (E > 0)) ∧ (0 < |((x - 1))|)) ∧ (|((x - 1))| < (1 /. (Real.rpow E (((2 : ℝ))⁻¹))))) → ((1 /. (|((1 - x))| ^ (2 : ℕ))) > E))))))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (E : ℝ), (((((E ∈ (Set.univ : Set ℝ)) ∧ (E > 0)) ∧ (0 < |((x - 1))|)) ∧ (|((x - 1))| < (1 /. (Real.rpow E (((2 : ℝ))⁻¹))))) → ((0 < |((x - 1))|) ∧ (|((x - 1))| < (1 /. (Real.rpow E (((2 : ℝ))⁻¹))))))))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (E : ℝ), (((((E ∈ (Set.univ : Set ℝ)) ∧ (E > 0)) ∧ (0 < |((x - 1))|)) ∧ (|((x - 1))| < (1 /. (Real.rpow E (((2 : ℝ))⁻¹))))) → ((1 /. (|((1 - x))| ^ (2 : ℕ))) > E))))))
  (h4 : (forall (E : ℝ), (((E ∈ (Set.univ : Set ℝ)) ∧ (E > 0)) → (exists (v_uCE_uB4 : ℝ), ((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ ((v_uCE_uB4 > 0) → (v_uCE_uB4 = (min (1 : ℝ) (1 /. (Real.rpow E (((2 : ℝ))⁻¹)))))))))))
  (h5 : (forall (E : ℝ), (((E ∈ (Set.univ : Set ℝ)) ∧ (E > 0)) → (exists (v_uCE_uB4 : ℝ), ((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ ((v_uCE_uB4 = (min (1 : ℝ) (1 /. (Real.rpow E (((2 : ℝ))⁻¹))))) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < |((x - 1))|)) ∧ (|((x - 1))| < v_uCE_uB4)) → ((1 /. (|((1 - x))| ^ (2 : ℕ))) > E)))))))))
  (h6 : (forall (E : ℝ), (((E ∈ (Set.univ : Set ℝ)) ∧ (E > 0)) → (exists (v_uCE_uB4 : ℝ), ((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ ((v_uCE_uB4 = (min (1 : ℝ) (1 /. (Real.rpow E (((2 : ℝ))⁻¹))))) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < |((x - 1))|)) ∧ (|((x - 1))| < v_uCE_uB4)) → (|((1 /. ((1 - x) ^ (2 : ℕ))))| > E)))))))))
  : Tendsto (fun x : ℝ => ((1 /. ((1 - x) ^ (2 : ℕ))) : EReal)) (𝓝[≠] 1) (𝓝 ⊤) := by
  sorry

theorem proof_gap_exercise_402_7
  (h1 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (E : ℝ), (((((E ∈ (Set.univ : Set ℝ)) ∧ (E > 0)) ∧ (0 < |((x - 1))|)) ∧ (|((x - 1))| < (1 /. (Real.rpow E (((2 : ℝ))⁻¹))))) → ((1 /. (|((1 - x))| ^ (2 : ℕ))) > E))))))
  (h2 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (E : ℝ), (((((E ∈ (Set.univ : Set ℝ)) ∧ (E > 0)) ∧ (0 < |((x - 1))|)) ∧ (|((x - 1))| < (1 /. E))) → ((0 < |((x - 1))|) ∧ (|((x - 1))| < (1 /. (Real.rpow E (((2 : ℝ))⁻¹))))))))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (E : ℝ), (((((E ∈ (Set.univ : Set ℝ)) ∧ (E > 0)) ∧ (0 < |((x - 1))|)) ∧ (|((x - 1))| < (1 /. E))) → ((1 /. (|((1 - x))| ^ (2 : ℕ))) > E))))))
  (h4 : (forall (E : ℝ), (((E ∈ (Set.univ : Set ℝ)) ∧ (E > 0)) → (exists (v_uCE_uB4 : ℝ), ((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ ((v_uCE_uB4 > 0) → (v_uCE_uB4 = (min (1 : ℝ) (1 /. E)))))))))
  (h5 : (forall (E : ℝ), (((E ∈ (Set.univ : Set ℝ)) ∧ (E > 0)) → (exists (v_uCE_uB4 : ℝ), ((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ ((v_uCE_uB4 = (min (1 : ℝ) (1 /. E))) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < |((x - 1))|)) ∧ (|((x - 1))| < v_uCE_uB4)) → ((1 /. (|((1 - x))| ^ (2 : ℕ))) > E)))))))))
  (h6 : (forall (E : ℝ), (((E ∈ (Set.univ : Set ℝ)) ∧ (E > 0)) → (exists (v_uCE_uB4 : ℝ), ((v_uCE_uB4 ∈ (Set.univ : Set ℝ)) ∧ ((v_uCE_uB4 = (min (1 : ℝ) (1 /. E))) → (forall (x : ℝ), ((((x ∈ (Set.univ : Set ℝ)) ∧ (0 < |((x - 1))|)) ∧ (|((x - 1))| < v_uCE_uB4)) → (|((1 /. ((1 - x) ^ (2 : ℕ))))| > E)))))))))
  (h7 : Tendsto (fun x : ℝ => ((1 /. ((1 - x) ^ (2 : ℕ))) : EReal)) (𝓝[≠] 1) (𝓝 ⊤))
  : Tendsto (fun x : ℝ => ((1 /. ((1 - x) ^ (2 : ℕ))) : EReal)) (𝓝[≠] 1) (𝓝 ⊤) := by
  sorry
