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

-- exercise: exercise_2416

theorem proof_gap_exercise_2416_1
  (x : (ℝ -> ℝ))
  (y : (ℝ -> ℝ))
  (FunDeri_x_1_1 : (ℝ -> ℝ))
  (FunDeri_y_1_1 : (ℝ -> ℝ))
  (a : ℝ)
  (S : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : S ∈ (Set.univ : Set ℝ))
  (h3 : (forall (t : ℝ), ((((t ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ t)) ∧ (t ≤ (2 * Real.pi))) → ((x t) = (a * ((2 * (Real.cos t)) - (Real.cos (2 * t))))))))
  (h4 : (forall (t : ℝ), ((((t ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ t)) ∧ (t ≤ (2 * Real.pi))) → ((y t) = (a * ((2 * (Real.sin t)) - (Real.sin (2 * t))))))))
  (h5 : True)
  : (forall (t : ℝ), ((((t ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ t)) ∧ (t ≤ (2 * Real.pi))) → ((iteratedDeriv 1 (fun t_1 => x t_1) t) = (a * (((-(2 : ℝ)) * (Real.sin t)) + (2 * (Real.sin (2 * t)))))))) := by
  sorry

theorem proof_gap_exercise_2416_2
  (x : (ℝ -> ℝ))
  (y : (ℝ -> ℝ))
  (FunDeri_x_1_1 : (ℝ -> ℝ))
  (FunDeri_y_1_1 : (ℝ -> ℝ))
  (a : ℝ)
  (S : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : S ∈ (Set.univ : Set ℝ))
  (h3 : (forall (t : ℝ), ((((t ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ t)) ∧ (t ≤ (2 * Real.pi))) → ((x t) = (a * ((2 * (Real.cos t)) - (Real.cos (2 * t))))))))
  (h4 : (forall (t : ℝ), ((((t ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ t)) ∧ (t ≤ (2 * Real.pi))) → ((y t) = (a * ((2 * (Real.sin t)) - (Real.sin (2 * t))))))))
  (h5 : (forall (t : ℝ), ((((t ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ t)) ∧ (t ≤ (2 * Real.pi))) → ((iteratedDeriv 1 (fun t_1 => x t_1) t) = (a * (((-(2 : ℝ)) * (Real.sin t)) + (2 * (Real.sin (2 * t)))))))))
  (h6 : True)
  : (forall (t : ℝ), ((((t ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ t)) ∧ (t ≤ (2 * Real.pi))) → ((iteratedDeriv 1 (fun t_1 => y t_1) t) = (a * ((2 * (Real.cos t)) - (2 * (Real.cos (2 * t)))))))) := by
  sorry

theorem proof_gap_exercise_2416_3
  (x : (ℝ -> ℝ))
  (y : (ℝ -> ℝ))
  (a : ℝ)
  (S : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : S ∈ (Set.univ : Set ℝ))
  (h3 : (forall (t : ℝ), ((((t ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ t)) ∧ (t ≤ (2 * Real.pi))) → ((x t) = (a * ((2 * (Real.cos t)) - (Real.cos (2 * t))))))))
  (h4 : (forall (t : ℝ), ((((t ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ t)) ∧ (t ≤ (2 * Real.pi))) → ((y t) = (a * ((2 * (Real.sin t)) - (Real.sin (2 * t))))))))
  (h5 : (forall (t : ℝ), ((((t ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ t)) ∧ (t ≤ (2 * Real.pi))) → ((iteratedDeriv 1 (fun t_1 => x t_1) t) = (a * (((-(2 : ℝ)) * (Real.sin t)) + (2 * (Real.sin (2 * t)))))))))
  (h6 : (forall (t : ℝ), ((((t ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ t)) ∧ (t ≤ (2 * Real.pi))) → ((iteratedDeriv 1 (fun t_1 => y t_1) t) = (a * ((2 * (Real.cos t)) - (2 * (Real.cos (2 * t)))))))))
  : S = ((1 /. 2) * (∫ t in (0 : ℝ)..(2 * Real.pi), ((((x t) * (iteratedDeriv 1 (fun t_1 => y t_1) t)) - ((y t) * (iteratedDeriv 1 (fun t_1 => x t_1) t))) * (1 : ℝ)))) := by
  sorry

theorem proof_gap_exercise_2416_4
  (x : (ℝ -> ℝ))
  (y : (ℝ -> ℝ))
  (a : ℝ)
  (S : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : S ∈ (Set.univ : Set ℝ))
  (h3 : (forall (t : ℝ), ((((t ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ t)) ∧ (t ≤ (2 * Real.pi))) → ((x t) = (a * ((2 * (Real.cos t)) - (Real.cos (2 * t))))))))
  (h4 : (forall (t : ℝ), ((((t ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ t)) ∧ (t ≤ (2 * Real.pi))) → ((y t) = (a * ((2 * (Real.sin t)) - (Real.sin (2 * t))))))))
  (h5 : (forall (t : ℝ), ((((t ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ t)) ∧ (t ≤ (2 * Real.pi))) → ((iteratedDeriv 1 (fun t_1 => x t_1) t) = (a * (((-(2 : ℝ)) * (Real.sin t)) + (2 * (Real.sin (2 * t)))))))))
  (h6 : (forall (t : ℝ), ((((t ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ t)) ∧ (t ≤ (2 * Real.pi))) → ((iteratedDeriv 1 (fun t_1 => y t_1) t) = (a * ((2 * (Real.cos t)) - (2 * (Real.cos (2 * t)))))))))
  (h7 : S = ((1 /. 2) * (∫ t in (0 : ℝ)..(2 * Real.pi), ((((x t) * (iteratedDeriv 1 (fun t_1 => y t_1) t)) - ((y t) * (iteratedDeriv 1 (fun t_1 => x t_1) t))) * (1 : ℝ)))))
  : S = ((1 /. 2) * (∫ t in (0 : ℝ)..(2 * Real.pi), (((((a * (((2 : ℝ) * (Real.cos t)) - (Real.cos (2 * t)))) * a) * (((2 : ℝ) * (Real.cos t)) - ((2 : ℝ) * (Real.cos (2 * t))))) - (((a * (((2 : ℝ) * (Real.sin t)) - (Real.sin (2 * t)))) * a) * (((-(2 : ℝ)) * (Real.sin t)) + ((2 : ℝ) * (Real.sin (2 * t)))))) * (1 : ℝ)))) := by
  sorry

theorem proof_gap_exercise_2416_5
  (x : (ℝ -> ℝ))
  (y : (ℝ -> ℝ))
  (a : ℝ)
  (S : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : S ∈ (Set.univ : Set ℝ))
  (h3 : (forall (t : ℝ), ((((t ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ t)) ∧ (t ≤ (2 * Real.pi))) → ((x t) = (a * ((2 * (Real.cos t)) - (Real.cos (2 * t))))))))
  (h4 : (forall (t : ℝ), ((((t ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ t)) ∧ (t ≤ (2 * Real.pi))) → ((y t) = (a * ((2 * (Real.sin t)) - (Real.sin (2 * t))))))))
  (h5 : (forall (t : ℝ), ((((t ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ t)) ∧ (t ≤ (2 * Real.pi))) → ((iteratedDeriv 1 (fun t_1 => x t_1) t) = (a * (((-(2 : ℝ)) * (Real.sin t)) + (2 * (Real.sin (2 * t)))))))))
  (h6 : (forall (t : ℝ), ((((t ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ t)) ∧ (t ≤ (2 * Real.pi))) → ((iteratedDeriv 1 (fun t_1 => y t_1) t) = (a * ((2 * (Real.cos t)) - (2 * (Real.cos (2 * t)))))))))
  (h7 : S = ((1 /. 2) * (∫ t in (0 : ℝ)..(2 * Real.pi), ((((x t) * (iteratedDeriv 1 (fun t_1 => y t_1) t)) - ((y t) * (iteratedDeriv 1 (fun t_1 => x t_1) t))) * (1 : ℝ)))))
  (h8 : S = ((1 /. 2) * (∫ t in (0 : ℝ)..(2 * Real.pi), (((((a * (((2 : ℝ) * (Real.cos t)) - (Real.cos (2 * t)))) * a) * (((2 : ℝ) * (Real.cos t)) - ((2 : ℝ) * (Real.cos (2 * t))))) - (((a * (((2 : ℝ) * (Real.sin t)) - (Real.sin (2 * t)))) * a) * (((-(2 : ℝ)) * (Real.sin t)) + ((2 : ℝ) * (Real.sin (2 * t)))))) * (1 : ℝ)))))
  : S = ((3 * (a ^ (2 : ℕ))) * (∫ t in (0 : ℝ)..(2 * Real.pi), ((((1 : ℝ) - ((Real.cos t) * (Real.cos (2 * t)))) - ((Real.sin t) * (Real.sin (2 * t)))) * (1 : ℝ)))) := by
  sorry

theorem proof_gap_exercise_2416_6
  (x : (ℝ -> ℝ))
  (y : (ℝ -> ℝ))
  (a : ℝ)
  (S : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : S ∈ (Set.univ : Set ℝ))
  (h3 : (forall (t : ℝ), ((((t ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ t)) ∧ (t ≤ (2 * Real.pi))) → ((x t) = (a * ((2 * (Real.cos t)) - (Real.cos (2 * t))))))))
  (h4 : (forall (t : ℝ), ((((t ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ t)) ∧ (t ≤ (2 * Real.pi))) → ((y t) = (a * ((2 * (Real.sin t)) - (Real.sin (2 * t))))))))
  (h5 : (forall (t : ℝ), ((((t ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ t)) ∧ (t ≤ (2 * Real.pi))) → ((iteratedDeriv 1 (fun t_1 => x t_1) t) = (a * (((-(2 : ℝ)) * (Real.sin t)) + (2 * (Real.sin (2 * t)))))))))
  (h6 : (forall (t : ℝ), ((((t ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ t)) ∧ (t ≤ (2 * Real.pi))) → ((iteratedDeriv 1 (fun t_1 => y t_1) t) = (a * ((2 * (Real.cos t)) - (2 * (Real.cos (2 * t)))))))))
  (h7 : S = ((1 /. 2) * (∫ t in (0 : ℝ)..(2 * Real.pi), ((((x t) * (iteratedDeriv 1 (fun t_1 => y t_1) t)) - ((y t) * (iteratedDeriv 1 (fun t_1 => x t_1) t))) * (1 : ℝ)))))
  (h8 : S = ((1 /. 2) * (∫ t in (0 : ℝ)..(2 * Real.pi), (((((a * (((2 : ℝ) * (Real.cos t)) - (Real.cos (2 * t)))) * a) * (((2 : ℝ) * (Real.cos t)) - ((2 : ℝ) * (Real.cos (2 * t))))) - (((a * (((2 : ℝ) * (Real.sin t)) - (Real.sin (2 * t)))) * a) * (((-(2 : ℝ)) * (Real.sin t)) + ((2 : ℝ) * (Real.sin (2 * t)))))) * (1 : ℝ)))))
  (h9 : S = ((3 * (a ^ (2 : ℕ))) * (∫ t in (0 : ℝ)..(2 * Real.pi), ((((1 : ℝ) - ((Real.cos t) * (Real.cos (2 * t)))) - ((Real.sin t) * (Real.sin (2 * t)))) * (1 : ℝ)))))
  : S = ((3 * (a ^ (2 : ℕ))) * (∫ t in (0 : ℝ)..(2 * Real.pi), (((1 : ℝ) - (Real.cos t)) * (1 : ℝ)))) := by
  sorry

theorem proof_gap_exercise_2416_7
  (x : (ℝ -> ℝ))
  (y : (ℝ -> ℝ))
  (a : ℝ)
  (S : ℝ)
  (h1 : (a ∈ (Set.univ : Set ℝ)) ∧ (a > 0))
  (h2 : S ∈ (Set.univ : Set ℝ))
  (h3 : (forall (t : ℝ), ((((t ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ t)) ∧ (t ≤ (2 * Real.pi))) → ((x t) = (a * ((2 * (Real.cos t)) - (Real.cos (2 * t))))))))
  (h4 : (forall (t : ℝ), ((((t ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ t)) ∧ (t ≤ (2 * Real.pi))) → ((y t) = (a * ((2 * (Real.sin t)) - (Real.sin (2 * t))))))))
  (h5 : (forall (t : ℝ), ((((t ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ t)) ∧ (t ≤ (2 * Real.pi))) → ((iteratedDeriv 1 (fun t_1 => x t_1) t) = (a * (((-(2 : ℝ)) * (Real.sin t)) + (2 * (Real.sin (2 * t)))))))))
  (h6 : (forall (t : ℝ), ((((t ∈ (Set.univ : Set ℝ)) ∧ (0 ≤ t)) ∧ (t ≤ (2 * Real.pi))) → ((iteratedDeriv 1 (fun t_1 => y t_1) t) = (a * ((2 * (Real.cos t)) - (2 * (Real.cos (2 * t)))))))))
  (h7 : S = ((1 /. 2) * (∫ t in (0 : ℝ)..(2 * Real.pi), ((((x t) * (iteratedDeriv 1 (fun t_1 => y t_1) t)) - ((y t) * (iteratedDeriv 1 (fun t_1 => x t_1) t))) * (1 : ℝ)))))
  (h8 : S = ((1 /. 2) * (∫ t in (0 : ℝ)..(2 * Real.pi), (((((a * (((2 : ℝ) * (Real.cos t)) - (Real.cos (2 * t)))) * a) * (((2 : ℝ) * (Real.cos t)) - ((2 : ℝ) * (Real.cos (2 * t))))) - (((a * (((2 : ℝ) * (Real.sin t)) - (Real.sin (2 * t)))) * a) * (((-(2 : ℝ)) * (Real.sin t)) + ((2 : ℝ) * (Real.sin (2 * t)))))) * (1 : ℝ)))))
  (h9 : S = ((3 * (a ^ (2 : ℕ))) * (∫ t in (0 : ℝ)..(2 * Real.pi), ((((1 : ℝ) - ((Real.cos t) * (Real.cos (2 * t)))) - ((Real.sin t) * (Real.sin (2 * t)))) * (1 : ℝ)))))
  (h10 : S = ((3 * (a ^ (2 : ℕ))) * (∫ t in (0 : ℝ)..(2 * Real.pi), (((1 : ℝ) - (Real.cos t)) * (1 : ℝ)))))
  : S = ((6 * Real.pi) * (a ^ (2 : ℕ))) := by
  sorry
