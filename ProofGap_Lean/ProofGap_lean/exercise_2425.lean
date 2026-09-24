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

-- exercise: exercise_2425

theorem proof_gap_exercise_2425_1
  (r : (ℝ -> ℝ))
  (v_uCF_u86 : (ℝ -> ℝ))
  (a : ℝ)
  (S : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : S ∈ (Set.univ : Set ℝ))
  (h3 : a > 0)
  (h4 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ≥ 0)) → (((r t) = (((2 * a) * t) /. (1 + (t ^ (2 : ℕ))))) ∧ ((v_uCF_u86 t) = ((Real.pi * t) /. (1 + t)))))))
  : S = ((1 /. 2) * (∫ t in Set.Ioi (0 : ℝ), (((r t) ^ (2 : ℕ)) * (deriv (fun (t : ℝ) => (v_uCF_u86 t)) t)))) := by
  sorry

theorem proof_gap_exercise_2425_2
  (r : (ℝ -> ℝ))
  (v_uCF_u86 : (ℝ -> ℝ))
  (a : ℝ)
  (S : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : S ∈ (Set.univ : Set ℝ))
  (h3 : a > 0)
  (h4 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ≥ 0)) → (((r t) = (((2 * a) * t) /. (1 + (t ^ (2 : ℕ))))) ∧ ((v_uCF_u86 t) = ((Real.pi * t) /. (1 + t)))))))
  (h5 : S = ((1 /. 2) * (∫ t in Set.Ioi (0 : ℝ), (((r t) ^ (2 : ℕ)) * (deriv (fun (t : ℝ) => (v_uCF_u86 t)) t)))))
  (h6 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ≥ 0)) → ((iteratedDeriv 1 (fun t_1 => v_uCF_u86 t_1) t) = (Real.pi /. ((1 + t) ^ (2 : ℕ)))))))
  : S = (((2 * Real.pi) * (a ^ (2 : ℕ))) * (∫ t in Set.Ioi (0 : ℝ), (((t ^ (2 : ℕ)) /. (((1 : ℝ) + (t ^ (2 : ℕ))) * ((1 + t) ^ (2 : ℕ)))) * (1 : ℝ)))) := by
  sorry

theorem proof_gap_exercise_2425_3
  (r : (ℝ -> ℝ))
  (v_uCF_u86 : (ℝ -> ℝ))
  (a : ℝ)
  (S : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : S ∈ (Set.univ : Set ℝ))
  (h3 : a > 0)
  (h4 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ≥ 0)) → (((r t) = (((2 * a) * t) /. (1 + (t ^ (2 : ℕ))))) ∧ ((v_uCF_u86 t) = ((Real.pi * t) /. (1 + t)))))))
  (h5 : S = ((1 /. 2) * (∫ t in Set.Ioi (0 : ℝ), (((r t) ^ (2 : ℕ)) * (deriv (fun (t : ℝ) => (v_uCF_u86 t)) t)))))
  (h6 : S = (((2 * Real.pi) * (a ^ (2 : ℕ))) * (∫ t in Set.Ioi (0 : ℝ), (((t ^ (2 : ℕ)) /. (((1 + (t ^ (2 : ℕ))) ^ (2 : ℕ)) * ((1 + t) ^ (2 : ℕ)))) * (1 : ℝ)))))
  : (∃ L : ℝ, Tendsto (fun b : ℝ => (((∫ t in (0 : ℝ)..b, (((1 : ℝ) /. ((4 : ℝ) * ((1 + t) ^ (2 : ℕ)))) * (1 : ℝ))) - ((1 /. 4) * (∫ t in (0 : ℝ)..b, (((1 : ℝ) /. ((1 : ℝ) + (t ^ (2 : ℕ)))) * (1 : ℝ))))) + ((1 /. 2) * (∫ t in (0 : ℝ)..b, ((t /. ((1 + (t ^ (2 : ℕ))) ^ (2 : ℕ))) * (1 : ℝ)))))) atTop (𝓝 L) ∧ (S = (((2 * Real.pi) * (a ^ (2 : ℕ))) * atTop.limUnder (fun b : ℝ => (((∫ t in (0 : ℝ)..b, (((1 : ℝ) /. ((4 : ℝ) * ((1 + t) ^ (2 : ℕ)))) * (1 : ℝ))) - ((1 /. 4) * (∫ t in (0 : ℝ)..b, (((1 : ℝ) /. ((1 : ℝ) + (t ^ (2 : ℕ)))) * (1 : ℝ))))) + ((1 /. 2) * (∫ t in (0 : ℝ)..b, ((t /. ((1 + (t ^ (2 : ℕ))) ^ (2 : ℕ))) * (1 : ℝ))))))))) := by
  sorry

theorem proof_gap_exercise_2425_4
  (r : (ℝ -> ℝ))
  (v_uCF_u86 : (ℝ -> ℝ))
  (a : ℝ)
  (S : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : S ∈ (Set.univ : Set ℝ))
  (h3 : a > 0)
  (h4 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ≥ 0)) → (((r t) = (((2 * a) * t) /. (1 + (t ^ (2 : ℕ))))) ∧ ((v_uCF_u86 t) = ((Real.pi * t) /. (1 + t)))))))
  (h5 : S = ((1 /. 2) * (∫ t in Set.Ioi (0 : ℝ), (((r t) ^ (2 : ℕ)) * (deriv (fun (t : ℝ) => (v_uCF_u86 t)) t)))))
  (h6 : S = (((2 * Real.pi) * (a ^ (2 : ℕ))) * (∫ t in Set.Ioi (0 : ℝ), (((t ^ (2 : ℕ)) /. (((1 + (t ^ (2 : ℕ))) ^ (2 : ℕ)) * ((1 + t) ^ (2 : ℕ)))) * (1 : ℝ)))))
  (h7 : S = (((2 * Real.pi) * (a ^ (2 : ℕ))) * atTop.limUnder (fun b : ℝ => (((∫ t in (0 : ℝ)..b, (((1 : ℝ) /. ((4 : ℝ) * ((1 + t) ^ (2 : ℕ)))) * (1 : ℝ))) - ((1 /. 4) * (∫ t in (0 : ℝ)..b, (((1 : ℝ) /. ((1 : ℝ) + (t ^ (2 : ℕ)))) * (1 : ℝ))))) + ((1 /. 2) * (∫ t in (0 : ℝ)..b, ((t /. ((1 + (t ^ (2 : ℕ))) ^ (2 : ℕ))) * (1 : ℝ))))))))
  (h8 : ∃ L : ℝ, Tendsto (fun b : ℝ => (((∫ t in (0 : ℝ)..b, (((1 : ℝ) /. ((4 : ℝ) * ((1 + t) ^ (2 : ℕ)))) * (1 : ℝ))) - ((1 /. 4) * (∫ t in (0 : ℝ)..b, (((1 : ℝ) /. ((1 : ℝ) + (t ^ (2 : ℕ)))) * (1 : ℝ))))) + ((1 /. 2) * (∫ t in (0 : ℝ)..b, ((t /. ((1 + (t ^ (2 : ℕ))) ^ (2 : ℕ))) * (1 : ℝ)))))) atTop (𝓝 L))
  : (∃ L : ℝ, Tendsto (fun b : ℝ => ((((-(1 /. (4 * (1 + b)))) - ((1 /. 4) * (Real.arctan b))) - ((1 /. 4) * (1 /. (1 + (b ^ (2 : ℕ)))))) - (((-(1 /. (4 * (1 + 0)))) - ((1 /. 4) * (Real.arctan (0 : ℝ)))) - ((1 /. 4) * (1 /. (1 + ((0 : ℕ) ^ (2 : ℕ)))))))) atTop (𝓝 L) ∧ (S = (((2 * Real.pi) * (a ^ (2 : ℕ))) * atTop.limUnder (fun b : ℝ => ((((-(1 /. (4 * (1 + b)))) - ((1 /. 4) * (Real.arctan b))) - ((1 /. 4) * (1 /. (1 + (b ^ (2 : ℕ)))))) - (((-(1 /. (4 * (1 + 0)))) - ((1 /. 4) * (Real.arctan (0 : ℝ)))) - ((1 /. 4) * (1 /. (1 + ((0 : ℕ) ^ (2 : ℕ))))))))))) := by
  sorry

theorem proof_gap_exercise_2425_5
  (r : (ℝ -> ℝ))
  (v_uCF_u86 : (ℝ -> ℝ))
  (a : ℝ)
  (S : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : S ∈ (Set.univ : Set ℝ))
  (h3 : a > 0)
  (h4 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ (t ≥ 0)) → (((r t) = (((2 * a) * t) /. (1 + (t ^ (2 : ℕ))))) ∧ ((v_uCF_u86 t) = ((Real.pi * t) /. (1 + t)))))))
  (h5 : S = ((1 /. 2) * (∫ t in Set.Ioi (0 : ℝ), (((r t) ^ (2 : ℕ)) * (deriv (fun (t : ℝ) => (v_uCF_u86 t)) t)))))
  (h6 : S = (((2 * Real.pi) * (a ^ (2 : ℕ))) * (∫ t in Set.Ioi (0 : ℝ), (((t ^ (2 : ℕ)) /. (((1 : ℝ) + (t ^ (2 : ℕ))) * ((1 + t) ^ (2 : ℕ)))) * (1 : ℝ)))))
  (h7 : S = (((2 * Real.pi) * (a ^ (2 : ℕ))) * atTop.limUnder (fun b : ℝ => (((∫ t in (0 : ℝ)..b, (((1 : ℝ) /. ((4 : ℝ) * ((1 + t) ^ (2 : ℕ)))) * (1 : ℝ))) - ((1 /. 4) * (∫ t in (0 : ℝ)..b, (((1 : ℝ) /. ((1 : ℝ) + (t ^ (2 : ℕ)))) * (1 : ℝ))))) + ((1 /. 2) * (∫ t in (0 : ℝ)..b, ((t /. ((1 + (t ^ (2 : ℕ))) ^ (2 : ℕ))) * (1 : ℝ))))))))
  (h8 : S = (((2 * Real.pi) * (a ^ (2 : ℕ))) * atTop.limUnder (fun b : ℝ => ((((-(1 /. (4 * (1 + b)))) - ((1 /. 4) * (Real.arctan b))) - ((1 /. 4) * (1 /. (1 + (b ^ (2 : ℕ)))))) - (((-(1 /. (4 * (1 + 0)))) - ((1 /. 4) * (Real.arctan (0 : ℝ)))) - ((1 /. 4) * (1 /. (1 + ((0 : ℕ) ^ (2 : ℕ))))))))))
  (h9 : ∃ L : ℝ, Tendsto (fun b : ℝ => (((∫ t in (0 : ℝ)..b, (((1 : ℝ) /. ((4 : ℝ) * ((1 + t) ^ (2 : ℕ)))) * (1 : ℝ))) - ((1 /. 4) * (∫ t in (0 : ℝ)..b, (((1 : ℝ) /. ((1 : ℝ) + (t ^ (2 : ℕ)))) * (1 : ℝ))))) + ((1 /. 2) * (∫ t in (0 : ℝ)..b, ((t /. ((1 + (t ^ (2 : ℕ))) ^ (2 : ℕ))) * (1 : ℝ)))))) atTop (𝓝 L))
  (h10 : ∃ L : ℝ, Tendsto (fun b : ℝ => ((((-(1 /. (4 * (1 + b)))) - ((1 /. 4) * (Real.arctan b))) - ((1 /. 4) * (1 /. (1 + (b ^ (2 : ℕ)))))) - (((-(1 /. (4 * (1 + 0)))) - ((1 /. 4) * (Real.arctan (0 : ℝ)))) - ((1 /. 4) * (1 /. (1 + ((0 : ℕ) ^ (2 : ℕ)))))))) atTop (𝓝 L))
  : S = ((Real.pi * (a ^ (2 : ℕ))) * (1 - (Real.pi /. 4))) := by
  sorry
