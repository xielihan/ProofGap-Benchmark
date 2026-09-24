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

-- exercise: exercise_3211

theorem proof_gap_exercise_3211_1
  (f : (ℝ × ℝ -> ℝ))
  (x : ℝ)
  (b : ℝ)
  (h1 : D ⊆ ((Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ)))
  (h2 : x ∈ (Set.univ : Set ℝ))
  (h3 : b ∈ (Set.univ : Set ℝ))
  (h4 : (x, b) ∈ D)
  (h5 : (exists (L : ℝ), ((L ∈ (Set.univ : Set ℝ)) ∧ ((iteratedDeriv 1 (fun t_1 => f (t_1, b)) x) = L))))
  (h6 : v_uCF_u86 = (fun (t : ℝ) => (f (t, b))))
  : (v_uCF_u86 x) = (f (x, b)) := by
  sorry

theorem proof_gap_exercise_3211_2
  (f : (ℝ × ℝ -> ℝ))
  (x : ℝ)
  (b : ℝ)
  (h1 : D ⊆ ((Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ)))
  (h2 : x ∈ (Set.univ : Set ℝ))
  (h3 : b ∈ (Set.univ : Set ℝ))
  (h4 : (x, b) ∈ D)
  (h5 : (exists (L : ℝ), ((L ∈ (Set.univ : Set ℝ)) ∧ ((iteratedDeriv 1 (fun t_1 => f (t_1, b)) x) = L))))
  (h6 : v_uCF_u86 = (fun (t : ℝ) => (f (t, b))))
  (h7 : (v_uCF_u86 x) = (f (x, b)))
  : (forall (v_uCE_u94_x : ℝ), ((((v_uCE_u94_x ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_u94_x ≠ 0)) ∧ (Tendsto (fun v_uCE_u94_x_1 : ℝ => v_uCE_u94_x_1) (𝓝[≠] 0) (𝓝 0))) → (((x + v_uCE_u94_x), b) ∈ D))) := by
  sorry

theorem proof_gap_exercise_3211_3
  (f : (ℝ × ℝ -> ℝ))
  (x : ℝ)
  (b : ℝ)
  (h1 : D ⊆ ((Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ)))
  (h2 : x ∈ (Set.univ : Set ℝ))
  (h3 : b ∈ (Set.univ : Set ℝ))
  (h4 : (x, b) ∈ D)
  (h5 : (exists (L : ℝ), ((L ∈ (Set.univ : Set ℝ)) ∧ ((iteratedDeriv 1 (fun t_1 => f (t_1, b)) x) = L))))
  (h6 : v_uCF_u86 = (fun (t : ℝ) => (f (t, b))))
  (h7 : (v_uCF_u86 x) = (f (x, b)))
  (h8 : (forall (v_uCE_u94_x : ℝ), ((((v_uCE_u94_x ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_u94_x ≠ 0)) ∧ (Tendsto (fun v_uCE_u94_x_1 : ℝ => v_uCE_u94_x_1) (𝓝[≠] 0) (𝓝 0))) → (((x + v_uCE_u94_x), b) ∈ D))))
  : (iteratedDeriv 1 (fun t_1 => (f (t_1, b))) x) = (iteratedDeriv 1 (fun t_1 => v_uCF_u86 t_1) x) := by
  sorry

theorem proof_gap_exercise_3211_4
  (f : (ℝ × ℝ -> ℝ))
  (x : ℝ)
  (b : ℝ)
  (h1 : D ⊆ ((Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ)))
  (h2 : x ∈ (Set.univ : Set ℝ))
  (h3 : b ∈ (Set.univ : Set ℝ))
  (h4 : (x, b) ∈ D)
  (h5 : (exists (L : ℝ), ((L ∈ (Set.univ : Set ℝ)) ∧ ((iteratedDeriv 1 (fun t_1 => f (t_1, b)) x) = L))))
  (h6 : v_uCF_u86 = (fun (t : ℝ) => (f (t, b))))
  (h7 : (v_uCF_u86 x) = (f (x, b)))
  (h8 : (forall (v_uCE_u94_x : ℝ), ((((v_uCE_u94_x ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_u94_x ≠ 0)) ∧ (Tendsto (fun v_uCE_u94_x_1 : ℝ => v_uCE_u94_x_1) (𝓝[≠] 0) (𝓝 0))) → (((x + v_uCE_u94_x), b) ∈ D))))
  (h9 : (iteratedDeriv 1 (fun t_1 => (f (t_1, b))) x) = (iteratedDeriv 1 (fun t_1 => v_uCF_u86 t_1) x))
  : Tendsto (fun v_uCE_u94_x : ℝ => (((v_uCF_u86 (x + v_uCE_u94_x)) - (v_uCF_u86 x)) /. v_uCE_u94_x)) (𝓝[≠] 0) (𝓝 (iteratedDeriv 1 (fun t_1 => v_uCF_u86 t_1) x)) := by
  sorry

theorem proof_gap_exercise_3211_5
  (f : (ℝ × ℝ -> ℝ))
  (x : ℝ)
  (b : ℝ)
  (h1 : D ⊆ ((Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ)))
  (h2 : x ∈ (Set.univ : Set ℝ))
  (h3 : b ∈ (Set.univ : Set ℝ))
  (h4 : (x, b) ∈ D)
  (h5 : (exists (L : ℝ), ((L ∈ (Set.univ : Set ℝ)) ∧ ((iteratedDeriv 1 (fun t_1 => f (t_1, b)) x) = L))))
  (h6 : v_uCF_u86 = (fun (t : ℝ) => (f (t, b))))
  (h7 : (v_uCF_u86 x) = (f (x, b)))
  (h8 : (forall (v_uCE_u94_x : ℝ), ((((v_uCE_u94_x ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_u94_x ≠ 0)) ∧ (Tendsto (fun v_uCE_u94_x_1 : ℝ => v_uCE_u94_x_1) (𝓝[≠] 0) (𝓝 0))) → (((x + v_uCE_u94_x), b) ∈ D))))
  (h9 : (iteratedDeriv 1 (fun t_1 => (f (t_1, b))) x) = (iteratedDeriv 1 (fun t_1 => v_uCF_u86 t_1) x))
  (h10 : Tendsto (fun v_uCE_u94_x : ℝ => (((v_uCF_u86 (x + v_uCE_u94_x)) - (v_uCF_u86 x)) /. v_uCE_u94_x)) (𝓝[≠] 0) (𝓝 (iteratedDeriv 1 (fun t_1 => v_uCF_u86 t_1) x)))
  : (∃ L_1 : ℝ, Tendsto (fun v_uCE_u94_x : ℝ => (((f ((x + v_uCE_u94_x), b)) - (f (x, b))) /. v_uCE_u94_x)) (𝓝[≠] 0) (𝓝 L_1) ∧ (Tendsto (fun v_uCE_u94_x : ℝ => (((v_uCF_u86 (x + v_uCE_u94_x)) - (v_uCF_u86 x)) /. v_uCE_u94_x)) (𝓝[≠] 0) (𝓝 ((𝓝[≠] 0).limUnder (fun v_uCE_u94_x : ℝ => (((f ((x + v_uCE_u94_x), b)) - (f (x, b))) /. v_uCE_u94_x)))))) := by
  sorry

theorem proof_gap_exercise_3211_6
  (f : (ℝ × ℝ -> ℝ))
  (x : ℝ)
  (b : ℝ)
  (h1 : D ⊆ ((Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ)))
  (h2 : x ∈ (Set.univ : Set ℝ))
  (h3 : b ∈ (Set.univ : Set ℝ))
  (h4 : (x, b) ∈ D)
  (h5 : (exists (L : ℝ), ((L ∈ (Set.univ : Set ℝ)) ∧ ((iteratedDeriv 1 (fun t_1 => f (t_1, b)) x) = L))))
  (h6 : v_uCF_u86 = (fun (t : ℝ) => (f (t, b))))
  (h7 : (v_uCF_u86 x) = (f (x, b)))
  (h8 : (forall (v_uCE_u94_x : ℝ), ((((v_uCE_u94_x ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_u94_x ≠ 0)) ∧ (Tendsto (fun v_uCE_u94_x_1 : ℝ => v_uCE_u94_x_1) (𝓝[≠] 0) (𝓝 0))) → (((x + v_uCE_u94_x), b) ∈ D))))
  (h9 : (iteratedDeriv 1 (fun t_1 => (f (t_1, b))) x) = (iteratedDeriv 1 (fun t_1 => v_uCF_u86 t_1) x))
  (h10 : Tendsto (fun v_uCE_u94_x : ℝ => (((v_uCF_u86 (x + v_uCE_u94_x)) - (v_uCF_u86 x)) /. v_uCE_u94_x)) (𝓝[≠] 0) (𝓝 (iteratedDeriv 1 (fun t_1 => v_uCF_u86 t_1) x)))
  (h11 : Tendsto (fun v_uCE_u94_x : ℝ => (((v_uCF_u86 (x + v_uCE_u94_x)) - (v_uCF_u86 x)) /. v_uCE_u94_x)) (𝓝[≠] 0) (𝓝 ((𝓝[≠] 0).limUnder (fun v_uCE_u94_x : ℝ => (((f ((x + v_uCE_u94_x), b)) - (f (x, b))) /. v_uCE_u94_x)))))
  (h12 : ∃ L_1 : ℝ, Tendsto (fun v_uCE_u94_x : ℝ => (((f ((x + v_uCE_u94_x), b)) - (f (x, b))) /. v_uCE_u94_x)) (𝓝[≠] 0) (𝓝 L_1))
  : Tendsto (fun v_uCE_u94_x : ℝ => (((f ((x + v_uCE_u94_x), b)) - (f (x, b))) /. v_uCE_u94_x)) (𝓝[≠] 0) (𝓝 (iteratedDeriv 1 (fun t_1 => f (t_1, b)) x)) := by
  sorry

theorem proof_gap_exercise_3211_7
  (f : (ℝ × ℝ -> ℝ))
  (x : ℝ)
  (b : ℝ)
  (h1 : D ⊆ ((Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ)))
  (h2 : x ∈ (Set.univ : Set ℝ))
  (h3 : b ∈ (Set.univ : Set ℝ))
  (h4 : (x, b) ∈ D)
  (h5 : (exists (L : ℝ), ((L ∈ (Set.univ : Set ℝ)) ∧ ((iteratedDeriv 1 (fun t_1 => f (t_1, b)) x) = L))))
  (h6 : v_uCF_u86 = (fun (t : ℝ) => (f (t, b))))
  (h7 : (v_uCF_u86 x) = (f (x, b)))
  (h8 : (forall (v_uCE_u94_x : ℝ), ((((v_uCE_u94_x ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_u94_x ≠ 0)) ∧ (Tendsto (fun v_uCE_u94_x_1 : ℝ => v_uCE_u94_x_1) (𝓝[≠] 0) (𝓝 0))) → (((x + v_uCE_u94_x), b) ∈ D))))
  (h9 : (iteratedDeriv 1 (fun t_1 => (f (t_1, b))) x) = (iteratedDeriv 1 (fun t_1 => v_uCF_u86 t_1) x))
  (h10 : Tendsto (fun v_uCE_u94_x : ℝ => (((v_uCF_u86 (x + v_uCE_u94_x)) - (v_uCF_u86 x)) /. v_uCE_u94_x)) (𝓝[≠] 0) (𝓝 (iteratedDeriv 1 (fun t_1 => v_uCF_u86 t_1) x)))
  (h11 : Tendsto (fun v_uCE_u94_x : ℝ => (((v_uCF_u86 (x + v_uCE_u94_x)) - (v_uCF_u86 x)) /. v_uCE_u94_x)) (𝓝[≠] 0) (𝓝 ((𝓝[≠] 0).limUnder (fun v_uCE_u94_x : ℝ => (((f ((x + v_uCE_u94_x), b)) - (f (x, b))) /. v_uCE_u94_x)))))
  (h12 : Tendsto (fun v_uCE_u94_x : ℝ => (((f ((x + v_uCE_u94_x), b)) - (f (x, b))) /. v_uCE_u94_x)) (𝓝[≠] 0) (𝓝 (iteratedDeriv 1 (fun t_1 => f (t_1, b)) x)))
  (h13 : ∃ L_1 : ℝ, Tendsto (fun v_uCE_u94_x : ℝ => (((f ((x + v_uCE_u94_x), b)) - (f (x, b))) /. v_uCE_u94_x)) (𝓝[≠] 0) (𝓝 L_1))
  : (iteratedDeriv 1 (fun t_1 => f (t_1, b)) x) = (iteratedDeriv 1 (fun t_1 => (f (t_1, b))) x) := by
  sorry

theorem proof_gap_exercise_3211_8
  (f : (ℝ × ℝ -> ℝ))
  (x : ℝ)
  (b : ℝ)
  (h1 : D ⊆ ((Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ)))
  (h2 : x ∈ (Set.univ : Set ℝ))
  (h3 : b ∈ (Set.univ : Set ℝ))
  (h4 : (x, b) ∈ D)
  (h5 : (exists (L : ℝ), ((L ∈ (Set.univ : Set ℝ)) ∧ ((iteratedDeriv 1 (fun t_1 => f (t_1, b)) x) = L))))
  (h6 : v_uCF_u86 = (fun (t : ℝ) => (f (t, b))))
  (h7 : (v_uCF_u86 x) = (f (x, b)))
  (h8 : (forall (v_uCE_u94_x : ℝ), ((((v_uCE_u94_x ∈ (Set.univ : Set ℝ)) ∧ (v_uCE_u94_x ≠ 0)) ∧ (Tendsto (fun v_uCE_u94_x_1 : ℝ => v_uCE_u94_x_1) (𝓝[≠] 0) (𝓝 0))) → (((x + v_uCE_u94_x), b) ∈ D))))
  (h9 : (iteratedDeriv 1 (fun t_1 => (f (t_1, b))) x) = (iteratedDeriv 1 (fun t_1 => v_uCF_u86 t_1) x))
  (h10 : Tendsto (fun v_uCE_u94_x : ℝ => (((v_uCF_u86 (x + v_uCE_u94_x)) - (v_uCF_u86 x)) /. v_uCE_u94_x)) (𝓝[≠] 0) (𝓝 (iteratedDeriv 1 (fun t_1 => v_uCF_u86 t_1) x)))
  (h11 : Tendsto (fun v_uCE_u94_x : ℝ => (((v_uCF_u86 (x + v_uCE_u94_x)) - (v_uCF_u86 x)) /. v_uCE_u94_x)) (𝓝[≠] 0) (𝓝 ((𝓝[≠] 0).limUnder (fun v_uCE_u94_x : ℝ => (((f ((x + v_uCE_u94_x), b)) - (f (x, b))) /. v_uCE_u94_x)))))
  (h12 : Tendsto (fun v_uCE_u94_x : ℝ => (((f ((x + v_uCE_u94_x), b)) - (f (x, b))) /. v_uCE_u94_x)) (𝓝[≠] 0) (𝓝 (iteratedDeriv 1 (fun t_1 => f (t_1, b)) x)))
  (h13 : (iteratedDeriv 1 (fun t_1 => f (t_1, b)) x) = (iteratedDeriv 1 (fun t_1 => (f (t_1, b))) x))
  (h14 : ∃ L_1 : ℝ, Tendsto (fun v_uCE_u94_x : ℝ => (((f ((x + v_uCE_u94_x), b)) - (f (x, b))) /. v_uCE_u94_x)) (𝓝[≠] 0) (𝓝 L_1))
  : (iteratedDeriv 1 (fun t_1 => f (t_1, b)) x) = (iteratedDeriv 1 (fun t_1 => (f (t_1, b))) x) := by
  sorry
