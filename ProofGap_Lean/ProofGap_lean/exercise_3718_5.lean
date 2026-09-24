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

-- exercise: exercise_3718_5

theorem proof_gap_exercise_3718_5_1
  (F : (ℝ -> ℝ))
  (h1 : (forall (v_uCE_uB1 : ℝ), ((v_uCE_uB1 ∈ (Set.univ : Set ℝ)) → ((F v_uCE_uB1) = (∫ x in (0 : ℝ)..(v_uCE_uB1 ^ (2 : ℕ)), ((∫ y in (x - v_uCE_uB1)..(x + v_uCE_uB1), ((Real.sin (((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) - (v_uCE_uB1 ^ (2 : ℕ)))) * (1 : ℝ))) * (1 : ℝ)))))))
  (h2 : Continuous (fun (p : ℝ × (ℝ × ℝ)) => (Real.sin (((p.1 ^ (2 : ℕ)) + (p.2.1 ^ (2 : ℕ))) - (p.2.2 ^ (2 : ℕ))))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), ((y ∈ (Set.univ : Set ℝ)) → (Differentiable ℝ (fun (v_uCE_uB1 : ℝ) => (Real.sin (((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) - (v_uCE_uB1 ^ (2 : ℕ)))))))))))
  : (forall (v_uCE_uB1 : ℝ), ((v_uCE_uB1 ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F t) v_uCE_uB1) = (((2 * v_uCE_uB1) * (∫ y in ((v_uCE_uB1 ^ (2 : ℕ)) - v_uCE_uB1)..((v_uCE_uB1 ^ (2 : ℕ)) + v_uCE_uB1), ((Real.sin (((v_uCE_uB1 ^ (4 : ℕ)) + (y ^ (2 : ℕ))) - (v_uCE_uB1 ^ (2 : ℕ)))) * (1 : ℝ)))) + (∫ x in (0 : ℝ)..(v_uCE_uB1 ^ (2 : ℕ)), ((iteratedDeriv 1 (fun t => (∫ y in (x - t)..(x + t), ((Real.sin (((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) - (t ^ (2 : ℕ)))) * (1 : ℝ)))) v_uCE_uB1) * (1 : ℝ))))))) := by
  sorry

theorem proof_gap_exercise_3718_5_2
  (F : (ℝ -> ℝ))
  (h1 : (forall (v_uCE_uB1 : ℝ), ((v_uCE_uB1 ∈ (Set.univ : Set ℝ)) → ((F v_uCE_uB1) = (∫ x in (0 : ℝ)..(v_uCE_uB1 ^ (2 : ℕ)), ((∫ y in (x - v_uCE_uB1)..(x + v_uCE_uB1), ((Real.sin (((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) - (v_uCE_uB1 ^ (2 : ℕ)))) * (1 : ℝ))) * (1 : ℝ)))))))
  (h2 : Continuous (fun (p : ℝ × (ℝ × ℝ)) => (Real.sin (((p.1 ^ (2 : ℕ)) + (p.2.1 ^ (2 : ℕ))) - (p.2.2 ^ (2 : ℕ))))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), ((y ∈ (Set.univ : Set ℝ)) → (Differentiable ℝ (fun (v_uCE_uB1 : ℝ) => (Real.sin (((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) - (v_uCE_uB1 ^ (2 : ℕ)))))))))))
  (h4 : (forall (v_uCE_uB1 : ℝ), ((v_uCE_uB1 ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F t) v_uCE_uB1) = (((2 * v_uCE_uB1) * (∫ y in ((v_uCE_uB1 ^ (2 : ℕ)) - v_uCE_uB1)..((v_uCE_uB1 ^ (2 : ℕ)) + v_uCE_uB1), ((Real.sin (((v_uCE_uB1 ^ (4 : ℕ)) + (y ^ (2 : ℕ))) - (v_uCE_uB1 ^ (2 : ℕ)))) * (1 : ℝ)))) + (∫ x in (0 : ℝ)..(v_uCE_uB1 ^ (2 : ℕ)), ((iteratedDeriv 1 (fun t => (∫ y in (x - t)..(x + t), ((Real.sin (((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) - (t ^ (2 : ℕ)))) * (1 : ℝ)))) v_uCE_uB1) * (1 : ℝ))))))))
  : (forall (v_uCE_uB1 : ℝ), ((v_uCE_uB1 ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F t) v_uCE_uB1) = (((2 * v_uCE_uB1) * (∫ y in ((v_uCE_uB1 ^ (2 : ℕ)) - v_uCE_uB1)..((v_uCE_uB1 ^ (2 : ℕ)) + v_uCE_uB1), ((Real.sin (((v_uCE_uB1 ^ (4 : ℕ)) + (y ^ (2 : ℕ))) - (v_uCE_uB1 ^ (2 : ℕ)))) * (1 : ℝ)))) + (∫ x in (0 : ℝ)..(v_uCE_uB1 ^ (2 : ℕ)), ((((Real.sin (((x ^ (2 : ℕ)) + ((x + v_uCE_uB1) ^ (2 : ℕ))) - (v_uCE_uB1 ^ (2 : ℕ)))) + (Real.sin (((x ^ (2 : ℕ)) + ((x - v_uCE_uB1) ^ (2 : ℕ))) - (v_uCE_uB1 ^ (2 : ℕ))))) + (∫ y in (x - v_uCE_uB1)..(x + v_uCE_uB1), ((((-(2 : ℝ)) * v_uCE_uB1) * (Real.cos (((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) - (v_uCE_uB1 ^ (2 : ℕ))))) * (1 : ℝ)))) * (1 : ℝ))))))) := by
  sorry

theorem proof_gap_exercise_3718_5_3
  (F : (ℝ -> ℝ))
  (h1 : (forall (v_uCE_uB1 : ℝ), ((v_uCE_uB1 ∈ (Set.univ : Set ℝ)) → ((F v_uCE_uB1) = (∫ x in (0 : ℝ)..(v_uCE_uB1 ^ (2 : ℕ)), ((∫ y in (x - v_uCE_uB1)..(x + v_uCE_uB1), ((Real.sin (((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) - (v_uCE_uB1 ^ (2 : ℕ)))) * (1 : ℝ))) * (1 : ℝ)))))))
  (h2 : Continuous (fun (p : ℝ × (ℝ × ℝ)) => (Real.sin (((p.1 ^ (2 : ℕ)) + (p.2.1 ^ (2 : ℕ))) - (p.2.2 ^ (2 : ℕ))))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), ((y ∈ (Set.univ : Set ℝ)) → (Differentiable ℝ (fun (v_uCE_uB1 : ℝ) => (Real.sin (((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) - (v_uCE_uB1 ^ (2 : ℕ)))))))))))
  (h4 : (forall (v_uCE_uB1 : ℝ), ((v_uCE_uB1 ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F t) v_uCE_uB1) = (((2 * v_uCE_uB1) * (∫ y in ((v_uCE_uB1 ^ (2 : ℕ)) - v_uCE_uB1)..((v_uCE_uB1 ^ (2 : ℕ)) + v_uCE_uB1), ((Real.sin (((v_uCE_uB1 ^ (4 : ℕ)) + (y ^ (2 : ℕ))) - (v_uCE_uB1 ^ (2 : ℕ)))) * (1 : ℝ)))) + (∫ x in (0 : ℝ)..(v_uCE_uB1 ^ (2 : ℕ)), ((iteratedDeriv 1 (fun t => (∫ y in (x - t)..(x + t), ((Real.sin (((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) - (t ^ (2 : ℕ)))) * (1 : ℝ)))) v_uCE_uB1) * (1 : ℝ))))))))
  (h5 : (forall (v_uCE_uB1 : ℝ), ((v_uCE_uB1 ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F t) v_uCE_uB1) = (((2 * v_uCE_uB1) * (∫ y in ((v_uCE_uB1 ^ (2 : ℕ)) - v_uCE_uB1)..((v_uCE_uB1 ^ (2 : ℕ)) + v_uCE_uB1), ((Real.sin (((v_uCE_uB1 ^ (4 : ℕ)) + (y ^ (2 : ℕ))) - (v_uCE_uB1 ^ (2 : ℕ)))) * (1 : ℝ)))) + (∫ x in (0 : ℝ)..(v_uCE_uB1 ^ (2 : ℕ)), ((((Real.sin (((x ^ (2 : ℕ)) + ((x + v_uCE_uB1) ^ (2 : ℕ))) - (v_uCE_uB1 ^ (2 : ℕ)))) + (Real.sin (((x ^ (2 : ℕ)) + ((x - v_uCE_uB1) ^ (2 : ℕ))) - (v_uCE_uB1 ^ (2 : ℕ))))) + (∫ y in (x - v_uCE_uB1)..(x + v_uCE_uB1), ((((-(2 : ℝ)) * v_uCE_uB1) * (Real.cos (((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) - (v_uCE_uB1 ^ (2 : ℕ))))) * (1 : ℝ)))) * (1 : ℝ))))))))
  : (forall (v_uCE_uB1 : ℝ), ((v_uCE_uB1 ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F t) v_uCE_uB1) = (((2 * v_uCE_uB1) * (∫ y in ((v_uCE_uB1 ^ (2 : ℕ)) - v_uCE_uB1)..((v_uCE_uB1 ^ (2 : ℕ)) + v_uCE_uB1), ((Real.sin (((v_uCE_uB1 ^ (4 : ℕ)) + (y ^ (2 : ℕ))) - (v_uCE_uB1 ^ (2 : ℕ)))) * (1 : ℝ)))) + (∫ x in (0 : ℝ)..(v_uCE_uB1 ^ (2 : ℕ)), ((((Real.sin ((2 * (x ^ (2 : ℕ))) + ((2 * v_uCE_uB1) * x))) + (Real.sin ((2 * (x ^ (2 : ℕ))) - ((2 * v_uCE_uB1) * x)))) + (∫ y in (x - v_uCE_uB1)..(x + v_uCE_uB1), ((((-(2 : ℝ)) * v_uCE_uB1) * (Real.cos (((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) - (v_uCE_uB1 ^ (2 : ℕ))))) * (1 : ℝ)))) * (1 : ℝ))))))) := by
  sorry

theorem proof_gap_exercise_3718_5_4
  (F : (ℝ -> ℝ))
  (h1 : (forall (v_uCE_uB1 : ℝ), ((v_uCE_uB1 ∈ (Set.univ : Set ℝ)) → ((F v_uCE_uB1) = (∫ x in (0 : ℝ)..(v_uCE_uB1 ^ (2 : ℕ)), ((∫ y in (x - v_uCE_uB1)..(x + v_uCE_uB1), ((Real.sin (((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) - (v_uCE_uB1 ^ (2 : ℕ)))) * (1 : ℝ))) * (1 : ℝ)))))))
  (h2 : Continuous (fun (p : ℝ × (ℝ × ℝ)) => (Real.sin (((p.1 ^ (2 : ℕ)) + (p.2.1 ^ (2 : ℕ))) - (p.2.2 ^ (2 : ℕ))))))
  (h3 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → (forall (y : ℝ), ((y ∈ (Set.univ : Set ℝ)) → (Differentiable ℝ (fun (v_uCE_uB1 : ℝ) => (Real.sin (((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) - (v_uCE_uB1 ^ (2 : ℕ)))))))))))
  (h4 : (forall (v_uCE_uB1 : ℝ), ((v_uCE_uB1 ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F t) v_uCE_uB1) = (((2 * v_uCE_uB1) * (∫ y in ((v_uCE_uB1 ^ (2 : ℕ)) - v_uCE_uB1)..((v_uCE_uB1 ^ (2 : ℕ)) + v_uCE_uB1), ((Real.sin (((v_uCE_uB1 ^ (4 : ℕ)) + (y ^ (2 : ℕ))) - (v_uCE_uB1 ^ (2 : ℕ)))) * (1 : ℝ)))) + (∫ x in (0 : ℝ)..(v_uCE_uB1 ^ (2 : ℕ)), ((iteratedDeriv 1 (fun t => (∫ y in (x - t)..(x + t), ((Real.sin (((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) - (t ^ (2 : ℕ)))) * (1 : ℝ)))) v_uCE_uB1) * (1 : ℝ))))))))
  (h5 : (forall (v_uCE_uB1 : ℝ), ((v_uCE_uB1 ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F t) v_uCE_uB1) = (((2 * v_uCE_uB1) * (∫ y in ((v_uCE_uB1 ^ (2 : ℕ)) - v_uCE_uB1)..((v_uCE_uB1 ^ (2 : ℕ)) + v_uCE_uB1), ((Real.sin (((v_uCE_uB1 ^ (4 : ℕ)) + (y ^ (2 : ℕ))) - (v_uCE_uB1 ^ (2 : ℕ)))) * (1 : ℝ)))) + (∫ x in (0 : ℝ)..(v_uCE_uB1 ^ (2 : ℕ)), ((((Real.sin (((x ^ (2 : ℕ)) + ((x + v_uCE_uB1) ^ (2 : ℕ))) - (v_uCE_uB1 ^ (2 : ℕ)))) + (Real.sin (((x ^ (2 : ℕ)) + ((x - v_uCE_uB1) ^ (2 : ℕ))) - (v_uCE_uB1 ^ (2 : ℕ))))) + (∫ y in (x - v_uCE_uB1)..(x + v_uCE_uB1), ((((-(2 : ℝ)) * v_uCE_uB1) * (Real.cos (((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) - (v_uCE_uB1 ^ (2 : ℕ))))) * (1 : ℝ)))) * (1 : ℝ))))))))
  (h6 : (forall (v_uCE_uB1 : ℝ), ((v_uCE_uB1 ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F t) v_uCE_uB1) = (((2 * v_uCE_uB1) * (∫ y in ((v_uCE_uB1 ^ (2 : ℕ)) - v_uCE_uB1)..((v_uCE_uB1 ^ (2 : ℕ)) + v_uCE_uB1), ((Real.sin (((v_uCE_uB1 ^ (4 : ℕ)) + (y ^ (2 : ℕ))) - (v_uCE_uB1 ^ (2 : ℕ)))) * (1 : ℝ)))) + (∫ x in (0 : ℝ)..(v_uCE_uB1 ^ (2 : ℕ)), ((((Real.sin ((2 * (x ^ (2 : ℕ))) + ((2 * v_uCE_uB1) * x))) + (Real.sin ((2 * (x ^ (2 : ℕ))) - ((2 * v_uCE_uB1) * x)))) + (∫ y in (x - v_uCE_uB1)..(x + v_uCE_uB1), ((((-(2 : ℝ)) * v_uCE_uB1) * (Real.cos (((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) - (v_uCE_uB1 ^ (2 : ℕ))))) * (1 : ℝ)))) * (1 : ℝ))))))))
  : (forall (v_uCE_uB1 : ℝ), ((v_uCE_uB1 ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t => F t) v_uCE_uB1) = ((((2 * v_uCE_uB1) * (∫ y in ((v_uCE_uB1 ^ (2 : ℕ)) - v_uCE_uB1)..((v_uCE_uB1 ^ (2 : ℕ)) + v_uCE_uB1), ((Real.sin (((v_uCE_uB1 ^ (4 : ℕ)) + (y ^ (2 : ℕ))) - (v_uCE_uB1 ^ (2 : ℕ)))) * (1 : ℝ)))) + (2 * (∫ x in (0 : ℝ)..(v_uCE_uB1 ^ (2 : ℕ)), (((Real.sin (2 * (x ^ (2 : ℕ)))) * (Real.cos ((2 * v_uCE_uB1) * x))) * (1 : ℝ))))) - ((2 * v_uCE_uB1) * (∫ x in (0 : ℝ)..(v_uCE_uB1 ^ (2 : ℕ)), ((∫ y in (x - v_uCE_uB1)..(x + v_uCE_uB1), ((Real.cos (((x ^ (2 : ℕ)) + (y ^ (2 : ℕ))) - (v_uCE_uB1 ^ (2 : ℕ)))) * (1 : ℝ))) * (1 : ℝ)))))))) := by
  sorry
